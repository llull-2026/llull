module type S = sig
    type t
    val create : int -> t
    val multi_step : int array -> t -> int list option * t
    val step : int -> t -> int list option * t
end

module Naive = struct
    type t = { arity : int; pos : int array }

    let create arity =
        if arity < 1 then invalid_arg "Naive.create: arity must be >= 1";
        { arity; pos = Array.make arity 0 }

    let multi_step pool_sizes s =
        if s.pos.(0) >= pool_sizes.(0) then (None, s)
        else
        let tuple = Array.copy s.pos in
        let new_pos = Array.copy s.pos in
        let rec inc i =
            if i < 0 then new_pos.(0) <- pool_sizes.(0)
            else if new_pos.(i) + 1 < pool_sizes.(i) then
                (new_pos.(i) <- new_pos.(i) + 1;
                 for r = i + 1 to s.arity - 1 do new_pos.(r) <- 0 done)
            else (new_pos.(i) <- 0; inc (i - 1)) in
        inc (s.arity - 1);
        (Some (Array.to_list tuple), { s with pos = new_pos })

    let step pool_size s = multi_step (Array.make s.arity pool_size) s
end

module Cantor = struct
    type t = { arity : int; diagonal : int; comp : int array }

    let create arity =
        if arity < 1 then invalid_arg "Cantor.create: arity must be >= 1";
        { arity; diagonal = 0; comp = Array.make arity 0 }

    let next_composition comp arity =
        let c = Array.copy comp in
        let right_sum = ref c.(arity - 1) in
        let found = ref false in
        let j = ref (arity - 2) in
        while !j >= 0 && not !found do
            if !right_sum > 0 then
                (c.(!j) <- c.(!j) + 1;
                 right_sum := !right_sum - 1;
                 for k = !j + 1 to arity - 2 do c.(k) <- 0 done;
                 c.(arity - 1) <- !right_sum;
                 found := true)
            else
                (right_sum := !right_sum + c.(!j);
                 c.(!j) <- 0;
                 decr j)
        done;
        if !found then Some c else None

    let advance arity diagonal comp =
        match next_composition comp arity with
        | Some new_comp -> (diagonal, new_comp)
        | None ->
            let d = diagonal + 1 in
            let c = Array.make arity 0 in
            c.(arity - 1) <- d;
            (d, c)

    let multi_step pool_sizes s =
        let max_diag = Array.fold_left (fun acc sz -> acc + sz - 1) 0 pool_sizes in
        let valid c =
            let ok = ref true in
            for i = 0 to s.arity - 1 do
                if c.(i) >= pool_sizes.(i) then ok := false
            done;
            !ok in
        let rec find d c fuel =
            if d > max_diag || fuel <= 0 then (None, { s with diagonal = d; comp = c })
            else if valid c then
                let tuple = Array.to_list c in
                let (nd, nc) = advance s.arity d c in
                (Some tuple, { s with diagonal = nd; comp = nc })
            else
                let (nd, nc) = advance s.arity d c in
                find nd nc (fuel - 1) in
        let fuel = max 1000 (max_diag * s.arity) in
        find s.diagonal s.comp fuel

    let step pool_size s = multi_step (Array.make s.arity pool_size) s
end

module Shell = struct
    type t = { arity : int; shell : int; slab : int; slab_pos : int array }

    let create arity =
        if arity < 1 then invalid_arg "Shell.create: arity must be >= 1";
        { arity; shell = 0; slab = 0; slab_pos = Array.make (arity - 1) 0 }

    let to_tuple s =
        let tuple = Array.make s.arity 0 in
        tuple.(s.slab) <- s.shell;
        for p = 0 to s.arity - 2 do
            let c = if p < s.slab then p else p + 1 in
            tuple.(c) <- s.slab_pos.(p)
        done;
        tuple

    let slab_limit pool_sizes shell slab_pos_idx slab =
        let actual_dim = if slab_pos_idx < slab then slab_pos_idx else slab_pos_idx + 1 in
        let slab_lim = if slab_pos_idx < slab then shell - 1 else shell in
        min slab_lim (pool_sizes.(actual_dim) - 1)

    let try_increment_slab pool_sizes s =
        if s.arity <= 1 then None
        else
        let n = s.arity - 1 in
        let new_pos = Array.copy s.slab_pos in
        let rec inc i =
            if i < 0 then None
            else
                let limit = slab_limit pool_sizes s.shell i s.slab in
                if new_pos.(i) < limit then
                    (new_pos.(i) <- new_pos.(i) + 1;
                     for r = i + 1 to n - 1 do new_pos.(r) <- 0 done;
                     Some new_pos)
                else inc (i - 1) in
        inc (n - 1)

    let next_slab_start pool_sizes arity shell slab =
        let max_pool = Array.fold_left max 0 pool_sizes in
        let rec find s sl =
            if s >= max_pool then (s, sl)
            else if sl >= arity then find (s + 1) 0
            else if s = 0 && sl > 0 then find 1 0
            else if s >= pool_sizes.(sl) then find s (sl + 1)
            else
                let valid = ref true in
                for p = 0 to arity - 2 do
                    let d = if p < sl then p else p + 1 in
                    if pool_sizes.(d) = 0 then valid := false
                done;
                if !valid then (s, sl) else find s (sl + 1) in
        find shell (slab + 1)

    let rec multi_step pool_sizes s =
        let max_pool = Array.fold_left max 0 pool_sizes in
        if s.shell >= max_pool then (None, s)
        else if s.shell >= pool_sizes.(s.slab) then
            let (ns, nsl) = next_slab_start pool_sizes s.arity s.shell s.slab in
            if ns >= max_pool then (None, { s with shell = ns; slab = nsl })
            else
                let s' = { s with shell = ns; slab = nsl; slab_pos = Array.make (s.arity - 1) 0 } in
                multi_step pool_sizes s'
        else
            let tuple = to_tuple s in
            let next = match try_increment_slab pool_sizes s with
                | Some new_pos -> { s with slab_pos = new_pos }
                | None ->
                    let (ns, nsl) = next_slab_start pool_sizes s.arity s.shell s.slab in
                    { s with shell = ns; slab = nsl; slab_pos = Array.make (s.arity - 1) 0 } in
            (Some (Array.to_list tuple), next)

    let step pool_size s = multi_step (Array.make s.arity pool_size) s
end

type strategy = Naive | Cantor | Shell

type t = {
    arity : int;
    multi_step_fn : int array -> int list option * t;
}

let rec wrap arity multi_step_impl cursor = {
    arity;
    multi_step_fn = (fun pool_sizes ->
        let (result, cursor') = multi_step_impl pool_sizes cursor in
        (result, wrap arity multi_step_impl cursor'));
}

let create strategy arity =
    match strategy with
    | Shell -> wrap arity Shell.multi_step (Shell.create arity)
    | Naive -> wrap arity Naive.multi_step (Naive.create arity)
    | Cantor -> wrap arity Cantor.multi_step (Cantor.create arity)

let multi_step pool_sizes t = t.multi_step_fn pool_sizes

let step pool_size t = t.multi_step_fn (Array.make t.arity pool_size)

let string_of_strategy = function
    | Shell -> "shell"
    | Naive -> "naive"
    | Cantor -> "cantor"

let strategy_of_string s =
    match String.lowercase_ascii s with
    | "shell" -> Shell
    | "naive" -> Naive
    | "cantor" -> Cantor
    | _ -> invalid_arg ("Unknown enumeration strategy: " ^ s)
