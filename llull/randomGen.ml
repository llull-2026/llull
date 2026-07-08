module Make (L : Language.LANGUAGE) = struct

    module G = Generator.Make (L)

    type rpool = { mutable arr : L.prototerm array; mutable len : int }

    let new_rpool () = { arr = [||]; len = 0 }

    let rpool_add pool prototerm =
        if pool.len >= Array.length pool.arr then begin
            let new_size = max 64 (2 * max 1 (Array.length pool.arr)) in
            let new_arr = Array.make new_size prototerm in
            Array.blit pool.arr 0 new_arr 0 pool.len;
            pool.arr <- new_arr
        end;
        pool.arr.(pool.len) <- prototerm;
        pool.len <- pool.len + 1

    let drain_seeds ~next_seed ?(extra=[]) () =
        let pools = Array.init L.sort_count (fun _ -> new_rpool ()) in
        let rec loop st =
            match next_seed st with
            | None -> ()
            | Some (s, st') -> rpool_add pools.(L.prototerm_sort s) s; loop st' in
        loop L.initial_seeds;
        List.iter (fun s -> rpool_add pools.(L.prototerm_sort s) s) extra;
        pools

    let gather_inputs pools input_sorts =
        let arity = Array.length input_sorts in
        let rec loop d acc =
            if d < 0 then Some acc
            else
                let p = pools.(input_sorts.(d)) in
                if p.len = 0 then None
                else loop (d - 1) (p.arr.(Random.int p.len) :: acc) in
        loop (arity - 1) []

    let pick_one xs =
        let rec nth k = function
            | [] -> assert false
            | x :: _ when k = 0 -> x
            | _ :: rest -> nth (k - 1) rest in
        nth (Random.int (List.length xs)) xs

    type rstate = {
        rpools : rpool array;
        rules_arr : L.prototerm Language.rule array;
        rule_inputs : int array array;
        mutable metrics : Generator.Metrics.t;
        mutable spine : L.prototerm option;
        sel_counts : int array;
    }

    let init_rstate ?(extra_seeds=[]) ?sel_counts ~config () =
        let (rules_arr, rule_inputs) = G.materialize_rules config in
        { rpools = drain_seeds ~next_seed:(L.next_seed config) ~extra:extra_seeds ();
          rules_arr;
          rule_inputs;
          metrics = Generator.Metrics.empty;
          spine = None;
          sel_counts = (match sel_counts with
              | Some a -> a
              | None -> Array.make (Array.length rules_arr) 0) }

    let pick_rule ~inverse_weight st n_rule =
        let ci =
            if not inverse_weight then Random.int n_rule
            else begin
                let weights = Array.init n_rule (fun i ->
                    1.0 /. (1.0 +. float_of_int st.sel_counts.(i))) in
                let total = Array.fold_left (+.) 0.0 weights in
                let r = ref (Random.float total) in
                let chosen = ref (n_rule - 1) in
                (try
                    for i = 0 to n_rule - 1 do
                        r := !r -. weights.(i);
                        if !r < 0.0 then (chosen := i; raise Exit)
                    done
                with Exit -> ());
                !chosen
            end in
        st.sel_counts.(ci) <- st.sel_counts.(ci) + 1;
        ci

    let gather_inputs_spine pools input_sorts spine =
        let arity = Array.length input_sorts in
        let spine_sort = L.prototerm_sort spine in
        let matching = ref [] in
        for d = 0 to arity - 1 do
            if input_sorts.(d) = spine_sort then matching := d :: !matching
        done;
        match !matching with
        | [] -> None
        | matches ->
            let slot = pick_one matches in
            let rec loop d acc =
                if d < 0 then Some acc
                else if d = slot then loop (d - 1) (spine :: acc)
                else
                    let p = pools.(input_sorts.(d)) in
                    if p.len = 0 then None
                    else loop (d - 1) (p.arr.(Random.int p.len) :: acc) in
            loop (arity - 1) []

    let gather_inputs_maybe_spine ~spine_mode st pools input_sorts =
        match (if spine_mode then st.spine else None) with
        | Some sp -> gather_inputs_spine pools input_sorts sp
        | None -> gather_inputs pools input_sorts

    let step_loop ?(time_ok = fun () -> true) ~stop_prob ~fuel ~max_inst ~bounds
            ~inverse_weight ~spine_mode ~concretize st =
        let pools = st.rpools in
        let size_cap = Generator.random_size_cap bounds in
        let n_rule = Array.length st.rules_arr in
        if n_rule = 0 then []
        else
            let rec loop fuel =
                if fuel <= 0 then []
                else if fuel land 255 = 0 && not (time_ok ()) then []
                else
                    let ci = pick_rule ~inverse_weight st n_rule in
                    let (name, _, _, suitable, expand) = st.rules_arr.(ci) in
                    let input_sorts = st.rule_inputs.(ci) in
                    match gather_inputs_maybe_spine ~spine_mode st pools input_sorts with
                    | None -> loop (fuel - 1)
                    | Some inputs ->
                        if not (suitable inputs) then loop (fuel - 1)
                        else
                            match List.of_seq (expand inputs) with
                            | [] -> loop (fuel - 1)
                            | outputs ->
                                let chosen = pick_one outputs in
                                if L.prototerm_min_size chosen > size_cap then loop (fuel - 1)
                                else begin
                                    let si = L.prototerm_sort chosen in
                                    rpool_add pools.(si) chosen;
                                    st.metrics <- Generator.Metrics.add_rule st.metrics name 1;
                                    st.spine <- Some chosen;
                                    if G.output_sort_set.(si) && Random.float 1.0 < stop_prob then
                                        match concretize chosen |> Seq.take max_inst |> List.of_seq
                                              |> List.filter (G.fact_within_bounds bounds) with
                                        | [] -> loop (fuel - 1)
                                        | facts ->
                                            st.metrics <- Generator.Metrics.add_conc st.metrics (List.length facts);
                                            facts
                                    else loop (fuel - 1)
                                end in
            loop fuel

    let next_buffered buffered refill =
        match !buffered with
        | f :: rest -> buffered := rest; Some f
        | [] ->
            match refill () with
            | [] -> None
            | f :: rest -> buffered := rest; Some f

    let rnext ?(time_ok = fun () -> true) ?(stop_prob=0.25) ?(fuel=200_000)
            ?(max_inst=1) ~bounds ~inverse_weight ~spine_mode ~concretize ~buffered st =
        next_buffered buffered (fun () ->
            step_loop ~time_ok ~stop_prob ~fuel ~max_inst ~bounds
                ~inverse_weight ~spine_mode ~concretize st)

    let step_triangle ?(time_ok = fun () -> true) ~x ~y ~fuel ~bounds
            ~inverse_weight ~spine_mode ~concretize st =
        if y <= x then None
        else
        let pools = st.rpools in
        let size_counts = Hashtbl.create 64 in
        let bump_count sz =
            let curr = try Hashtbl.find size_counts sz with Not_found -> 0 in
            Hashtbl.replace size_counts sz (curr + 1) in
        let count_at sz = try Hashtbl.find size_counts sz with Not_found -> 0 in
        Array.iter (fun p ->
            for i = 0 to p.len - 1 do bump_count (L.prototerm_min_size p.arr.(i)) done
        ) pools;
        let n_rule = Array.length st.rules_arr in
        if n_rule = 0 then None
        else
            let cap_at s =
                if s <= x then max_int
                else if s > y then 0
                else
                    let cx = count_at x in
                    let dx = float_of_int (s - x) in
                    let dy = float_of_int (y - x) in
                    let raw = float_of_int cx +. (1.0 -. float_of_int cx) *. dx /. dy in
                    max 1 (int_of_float (raw +. 0.5)) in
            let rec loop fuel =
                if fuel <= 0 then begin
                    Printf.eprintf
                        "[random-triangle] FUEL EXHAUSTED: never produced a size-%d prototerm (count(x=%d)=%d). Try smaller --triangle-y, smaller --triangle-x, or larger --fuel.\n%!"
                        y x (count_at x);
                    None
                end
                else if fuel land 255 = 0 && not (time_ok ()) then None
                else
                    let ci = pick_rule ~inverse_weight st n_rule in
                    let (name, _, _, suitable, expand) = st.rules_arr.(ci) in
                    let input_sorts = st.rule_inputs.(ci) in
                    match gather_inputs_maybe_spine ~spine_mode st pools input_sorts with
                    | None -> loop (fuel - 1)
                    | Some inputs ->
                        if not (suitable inputs) then loop (fuel - 1)
                        else
                            match List.of_seq (expand inputs) with
                            | [] -> loop (fuel - 1)
                            | outputs ->
                                let chosen = pick_one outputs in
                                let sz = L.prototerm_min_size chosen in
                                if count_at sz >= cap_at sz then loop (fuel - 1)
                                else if sz = y then begin
                                    st.spine <- Some chosen;
                                    let si = L.prototerm_sort chosen in
                                    if G.output_sort_set.(si) then
                                        match concretize chosen |> Seq.take 1 |> List.of_seq
                                              |> List.filter (G.fact_within_bounds bounds) with
                                        | f :: _ ->
                                            st.metrics <- Generator.Metrics.add_conc st.metrics 1;
                                            Some f
                                        | [] -> loop (fuel - 1)
                                    else loop (fuel - 1)
                                end else begin
                                    let si = L.prototerm_sort chosen in
                                    rpool_add pools.(si) chosen;
                                    st.metrics <- Generator.Metrics.add_rule st.metrics name 1;
                                    bump_count sz;
                                    st.spine <- Some chosen;
                                    loop (fuel - 1)
                                end in
            loop fuel
end
