type walk = Persistent | Fresh | Triangle of { x : int; y : int }

type mode = Enumerate | Random of walk
type term_kind = Well_typed | Ill_typed

type bounds = {
    max_unique_vars : int option;
    max_depth       : int option;
    max_size        : int option;
}

let no_bounds = { max_unique_vars = None; max_depth = None; max_size = None }

let default_walk_size_cap = 64

let size_cap_of bounds =
    match bounds.max_size with
    | Some m -> m
    | None ->
        if bounds.max_unique_vars <> None || bounds.max_depth <> None
        then default_walk_size_cap
        else max_int

let random_size_cap bounds =
    match bounds.max_size with
    | Some m -> m
    | None -> default_walk_size_cap

type scheduler_config =
| CfgRoundRobin
| CfgEpoch of { stall_limit : int }
| CfgAdaptive of { alpha : float; epsilon : float }

type opts = {
    mode      : mode;
    term_kind : term_kind;
    strategy  : Enumerators.strategy;
    scheduler : scheduler_config;
    max_inst  : int;
    bounds    : bounds;
    fuel      : int option;
    stop_prob : float option;
    inverse_weight : bool;
    spine_mode     : bool;
    warmup_steps   : int;
}

let default_opts = {
    mode = Enumerate;
    term_kind = Well_typed;
    strategy = Enumerators.Shell;
    scheduler = CfgRoundRobin;
    max_inst = 1;
    bounds = no_bounds;
    fuel = None;
    stop_prob = None;
    inverse_weight = false;
    spine_mode = false;
    warmup_steps = 0;
}

let default_random_budget = 20_000

module Metrics = struct
    type t = {
        rule_counts : (string * int) list;
        conc_hist   : (int * int) list;
    }
    let empty = { rule_counts = []; conc_hist = [] }
    let incr key delta lst =
        let rec go = function
            | [] -> [(key, delta)]
            | (k, v) :: rest when k = key -> (k, v + delta) :: rest
            | kv :: rest -> kv :: go rest
        in go lst
    let add_rule m name k =
        if k <= 0 then m else { m with rule_counts = incr name k m.rule_counts }
    let add_conc m distinct = { m with conc_hist = incr distinct 1 m.conc_hist }
end

module Make (L : Language.LANGUAGE) = struct

    module PrototermSet = Set.Make(struct
        type t = L.prototerm_key
        let compare = L.compare_prototerm_key
    end)
    module FactSet = Set.Make(struct
        type t = L.fact_key
        let compare = L.compare_fact_key
    end)

    let materialize_rules config =
        let arr = Array.of_list (L.rules config) in
        let inputs = Array.map (fun (_, input_sorts, _, _, _) ->
            Array.of_list input_sorts) arr in
        (arr, inputs)

    let output_sort_indices = Array.of_list L.output_sorts
    let output_sort_set =
        let s = Array.make L.sort_count false in
        List.iter (fun i -> s.(i) <- true) L.output_sorts;
        s

    let concretize_for_mode ~search_budget config term_kind ~index s =
        match term_kind with
        | Well_typed -> L.concretize ~search_budget config s
        | Ill_typed ->
            let per_family =
                List.map (fun t ->
                    let variants = Helper.rotate_list index (List.of_seq (t config s)) in
                    Helper.interleave
                        (List.map (L.concretize ~search_budget config) variants))
                    L.techniques in
            Helper.interleave (Helper.rotate_list index per_family)

    let rotating_concretize ~search_budget config term_kind =
        let next_index = ref 0 in
        fun s ->
            let i = !next_index in
            incr next_index;
            concretize_for_mode ~search_budget config term_kind ~index:i s

    let fact_within_bounds bounds f =
        (match bounds.max_unique_vars with Some m -> L.fact_unique_vars f <= m | None -> true)
        && (match bounds.max_depth with Some m -> L.fact_depth f <= m | None -> true)
        && (match bounds.max_size with Some m -> L.fact_nodes f <= m | None -> true)

    type pool = { prototerms : L.prototerm array; n : int }

    type schedule_step =
    | Seed
    | Compose of int
    | Instantiate

    type epoch_phase =
    | EpochSeed
    | EpochCompose of int
    | EpochInstantiate

    type scheduler =
    | RoundRobin of { steps : schedule_step array }
    | Epoch of { phase : epoch_phase; stall : int; stall_limit : int; budget : int }
    | Adaptive of { rates : float array; alpha : float; epsilon : float }

    type state = {
        pools : pool array;
        seen_prototerms : PrototermSet.t;
        seen_facts : FactSet.t;
        seed_state : L.seed_state;
        next_seed : L.seed_state -> (L.prototerm * L.seed_state) option;
        rules_arr : L.prototerm Language.rule array;
        rule_inputs : int array array;
        cursors : Enumerators.t array;
        inst_cursors : int array;
        inst_round_robin : int;
        inst_ii : int;
        inst_distinct : int;
        inst_cache : L.fact Seq.t option;
        concretize : int -> L.prototerm -> L.fact Seq.t;
        metrics : Metrics.t;
        bounds : bounds;
        size_cap : int;
        max_inst_per_sketch : int;
        scheduler : scheduler;
        turn : int;
        fuel : int;
    }

    let default_schedule n_rules =
        Array.of_list
            (List.init 2 (fun _ -> Seed)
             @ List.init n_rules (fun i -> Compose i))

    let make_scheduler n_rules = function
        | CfgRoundRobin -> RoundRobin { steps = default_schedule n_rules }
        | CfgEpoch { stall_limit } ->
            Epoch { phase = EpochSeed; stall = 0; stall_limit; budget = stall_limit }
        | CfgAdaptive { alpha; epsilon } ->
            let n_phases = 1 + n_rules + 1 in
            Adaptive { rates = Array.make n_phases 0.5; alpha; epsilon }

    let initial_state ?(max_inst_per_sketch=1) ?(fuel=50000)
            ?(scheduler=CfgRoundRobin) ?(bounds=no_bounds)
            ~config ~search_budget ~term_kind strategy =
        let (rules_arr, rule_inputs) = materialize_rules config in
        let cursors = Array.map (fun input_sorts ->
            Enumerators.create strategy (Array.length input_sorts)) rule_inputs in
        let empty_pool = { prototerms = [||]; n = 0 } in
        { pools = Array.make L.sort_count empty_pool;
          seen_prototerms = PrototermSet.empty;
          seen_facts = FactSet.empty;
          seed_state = L.initial_seeds;
          next_seed = L.next_seed config;
          rules_arr;
          rule_inputs;
          cursors;
          inst_cursors = Array.make (Array.length output_sort_indices) 0;
          inst_round_robin = 0;
          inst_ii = 0;
          inst_distinct = 0;
          inst_cache = None;
          concretize = (fun index s ->
              concretize_for_mode ~search_budget config term_kind ~index s);
          metrics = Metrics.empty;
          bounds;
          size_cap = size_cap_of bounds;
          max_inst_per_sketch;
          scheduler = make_scheduler (Array.length rules_arr) scheduler;
          turn = 0; fuel }

    let pool_add pool prototerm =
        let prototerms = if pool.n >= Array.length pool.prototerms then
            let new_size = max 256 (2 * max 1 (Array.length pool.prototerms)) in
            let new_arr = Array.make new_size prototerm in
            Array.blit pool.prototerms 0 new_arr 0 pool.n;
            new_arr
        else pool.prototerms in
        prototerms.(pool.n) <- prototerm;
        { prototerms; n = pool.n + 1 }

    let add_to_pool state prototerm =
        if L.prototerm_min_size prototerm > state.size_cap then (state, false)
        else
        let key = L.prototerm_key prototerm in
        if PrototermSet.mem key state.seen_prototerms then (state, false)
        else
            let si = L.prototerm_sort prototerm in
            let new_pool = pool_add state.pools.(si) prototerm in
            let new_pools = Array.copy state.pools in
            new_pools.(si) <- new_pool;
            ({ state with
               pools = new_pools;
               seen_prototerms = PrototermSet.add key state.seen_prototerms }, true)

    let add_all_to_pool_count ?(limit=max_int) state prototerms =
        let rec go st k seq =
            if k >= limit then (st, k)
            else match seq () with
            | Seq.Nil -> (st, k)
            | Seq.Cons (s, rest) ->
                let (st', added) = add_to_pool st s in
                go st' (if added then k + 1 else k) rest in
        go state 0 prototerms

    let step_seed state =
        match state.next_seed state.seed_state with
        | None -> state
        | Some (prototerm, seed_state') ->
            fst @@ add_to_pool { state with seed_state = seed_state' } prototerm

    let update_cursor cursors ci cursor' =
        let c = Array.copy cursors in
        c.(ci) <- cursor'; c

    let step_compose state ci =
        let input_sorts = state.rule_inputs.(ci) in
        let arity = Array.length input_sorts in
        if arity = 0 then state
        else
            let dim_sizes = Array.map (fun si -> state.pools.(si).n) input_sorts in
            if Array.exists (fun s -> s = 0) dim_sizes then state
            else
                let cursor = state.cursors.(ci) in
                let (result, cursor') = Enumerators.multi_step dim_sizes cursor in
                let state' = { state with cursors = update_cursor state.cursors ci cursor' } in
                match result with
                | None -> state'
                | Some indices ->
                    let (name, _, _, suitable, expand) = state.rules_arr.(ci) in
                    let inputs = List.mapi (fun dim idx ->
                        let si = input_sorts.(dim) in
                        state'.pools.(si).prototerms.(idx)) indices in
                    if not (suitable inputs) then state'
                    else
                        let (state'', added) = add_all_to_pool_count state' (expand inputs) in
                        { state'' with
                          metrics = Metrics.add_rule state''.metrics name added }

    let advance_inst state osi si =
        let nc = Array.copy state.inst_cursors in
        nc.(osi) <- si + 1;
        { state with
          inst_cursors = nc;
          inst_round_robin = state.inst_round_robin + 1;
          inst_ii = 0; inst_distinct = 0; inst_cache = None;
          metrics = Metrics.add_conc state.metrics state.inst_distinct }

    let step_inst state =
        let n_output = Array.length output_sort_indices in
        if n_output = 0 then (state, None)
        else
            let osi = state.inst_round_robin mod n_output in
            let pool_idx = output_sort_indices.(osi) in
            let pool = state.pools.(pool_idx) in
            let si = state.inst_cursors.(osi) in
            if si >= pool.n then
                ({ state with
                   inst_round_robin = state.inst_round_robin + 1;
                   inst_ii = 0; inst_distinct = 0; inst_cache = None }, None)
            else
                let s = pool.prototerms.(si) in
                let facts_seq = match state.inst_cache with
                    | Some seq -> seq
                    | None -> state.concretize (si + osi) s in
                if state.inst_ii >= state.max_inst_per_sketch then
                    (advance_inst state osi si, None)
                else
                    match facts_seq () with
                    | Seq.Nil -> (advance_inst state osi si, None)
                    | Seq.Cons (fact, rest) ->
                        let key = L.fact_key fact in
                        let state' = { state with
                            inst_ii = state.inst_ii + 1;
                            inst_cache = Some rest;
                            inst_round_robin = state.inst_round_robin + 1 } in
                        if FactSet.mem key state'.seen_facts
                           || not (fact_within_bounds state'.bounds fact)
                        then (state', None)
                        else ({ state' with
                                inst_distinct = state.inst_distinct + 1;
                                seen_facts = FactSet.add key state'.seen_facts }, Some fact)

    let total_pool_size state =
        Array.fold_left (fun acc p -> acc + p.n) 0 state.pools

    let all_inst_caught_up state =
        let n_output = Array.length output_sort_indices in
        if n_output = 0 then true
        else
            let rec check osi =
                if osi >= n_output then true
                else
                    let pool_idx = output_sort_indices.(osi) in
                    state.inst_cursors.(osi) >= state.pools.(pool_idx).n
                    && check (osi + 1) in
            check 0

    let enumeration_exhausted state =
        state.next_seed state.seed_state = None
        && all_inst_caught_up state
        && (let n = Array.length state.rules_arr in
            let rec all_done ci =
                if ci >= n then true
                else
                    let input_sorts = state.rule_inputs.(ci) in
                    let dim_sizes =
                        Array.map (fun si -> state.pools.(si).n) input_sorts in
                    let exhausted_ci =
                        Array.length input_sorts = 0
                        || Array.exists (fun s -> s = 0) dim_sizes
                        || (match Enumerators.multi_step dim_sizes state.cursors.(ci) with
                            | (None, _) -> true | _ -> false) in
                    exhausted_ci && all_done (ci + 1) in
            all_done 0)

    let step_round_robin state steps =
        let idx = (state.turn - 1) mod Array.length steps in
        match steps.(idx) with
        | Seed -> (step_seed state, None)
        | Compose ci -> (step_compose state ci, None)
        | Instantiate -> step_inst state

    let step_epoch state phase stall stall_limit budget =
        let goto state' ?(stall = 0) phase budget out =
            ({ state' with scheduler =
                Epoch { phase; stall; stall_limit; budget } }, out) in
        match phase with
        | EpochSeed ->
            let pool_before = total_pool_size state in
            let state' = step_seed state in
            if total_pool_size state' > pool_before
            then goto state' EpochSeed budget None
            else goto state' (EpochCompose 0) stall_limit None
        | EpochCompose ci ->
            let n_rules = Array.length state.rules_arr in
            let pool_before = total_pool_size state in
            let state' = step_compose state (ci mod n_rules) in
            let next_ci = (ci + 1) mod n_rules in
            let new_budget = budget - 1 in
            let grew = total_pool_size state' > pool_before in
            let new_stall = if grew then 0 else stall + 1 in
            if new_budget <= 0 || new_stall >= stall_limit
            then goto state' EpochInstantiate 0 None
            else goto state' (EpochCompose next_ci) ~stall:new_stall new_budget None
        | EpochInstantiate ->
            let (state', fact_opt) = step_inst state in
            if all_inst_caught_up state'
            then goto state' (EpochCompose 0) stall_limit fact_opt
            else (state', fact_opt)

    let step_adaptive state rates alpha epsilon =
        let n_phases = Array.length rates in
        let n_rules = Array.length state.rules_arr in
        let choice =
            if Random.float 1.0 < epsilon then Random.int n_phases
            else begin
                let best = ref 0 in
                for i = 1 to n_phases - 1 do
                    if rates.(i) > rates.(!best) then best := i
                done;
                !best
            end in
        let pool_before = total_pool_size state in
        let (state', fact_opt) =
            if choice = 0 then (step_seed state, None)
            else if choice <= n_rules then (step_compose state (choice - 1), None)
            else step_inst state in
        let success =
            if choice > n_rules then (match fact_opt with Some _ -> true | None -> false)
            else total_pool_size state' > pool_before in
        let new_rates = Array.copy rates in
        new_rates.(choice) <- alpha *. (if success then 1.0 else 0.0)
                              +. (1.0 -. alpha) *. rates.(choice);
        ({ state' with scheduler =
            Adaptive { rates = new_rates; alpha; epsilon } }, fact_opt)

    let step state =
        let state' = { state with turn = state.turn + 1 } in
        match state'.scheduler with
        | RoundRobin { steps } -> step_round_robin state' steps
        | Epoch { phase; stall; stall_limit; budget } ->
            step_epoch state' phase stall stall_limit budget
        | Adaptive { rates; alpha; epsilon } -> step_adaptive state' rates alpha epsilon

    let rec next_fact state fuel =
        if fuel <= 0 then (state, None)
        else if not (all_inst_caught_up state) then
            match step_inst state with
            | (state', (Some _ as f)) -> (state', f)
            | (state', None) -> next_fact state' (fuel - 1)
        else
            match step state with
            | (state', (Some _ as f)) -> (state', f)
            | (state', None) -> next_fact state' (fuel - 1)

    type stream = {
        next      : unit -> L.fact option;
        metrics   : unit -> Metrics.t;
        exhausted : unit -> bool;
    }
end
