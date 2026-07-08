module Make (L : Language.LANGUAGE) = struct

    module G = Generator.Make (L)

    type pool = { mutable arr : L.prototerm array; mutable n : int; mutable old : int }

    let new_pool () = { arr = [||]; n = 0; old = 0 }

    let push pool p =
        if pool.n >= Array.length pool.arr then begin
            let cap = max 256 (2 * max 1 (Array.length pool.arr)) in
            let a = Array.make cap p in
            Array.blit pool.arr 0 a 0 pool.n;
            pool.arr <- a
        end;
        pool.arr.(pool.n) <- p;
        pool.n <- pool.n + 1

    exception Reached

    let run ~interleaved ~waves ~target ~timeout ~sample ~config ~term_kind ~max_inst ~csv =
        let waves = match timeout with Some _ -> max_int | None -> waves in
        let oc = open_out csv in
        output_string oc "time,count\n";
        let (rules_arr, rule_inputs) = G.materialize_rules config in
        let pools = Array.init L.sort_count (fun _ -> new_pool ()) in
        let seen_proto = ref G.PrototermSet.empty in
        let seen_fact = ref G.FactSet.empty in
        let conc_index = ref 0 in
        let count = ref 0 in
        let start = Unix.gettimeofday () in
        let next_mark = ref 0.0 in
        let deadline = match timeout with None -> infinity | Some s -> s in
        let check_deadline () =
            if Unix.gettimeofday () -. start >= deadline then raise Reached in

        let emit () =
            let t = Unix.gettimeofday () -. start in
            if t >= !next_mark then begin
                Printf.fprintf oc "%.4f,%d\n" t !count; flush oc;
                next_mark := t +. sample
            end;
            if t >= deadline || !count >= target then raise Reached in

        let register p =
            let key = L.prototerm_key p in
            if G.PrototermSet.mem key !seen_proto then false
            else (seen_proto := G.PrototermSet.add key !seen_proto; true) in

        let is_output p = G.output_sort_set.(L.prototerm_sort p) in

        let concretize p =
            check_deadline ();
            let index = !conc_index in
            incr conc_index;
            let seq = G.concretize_for_mode ~search_budget:None config term_kind ~index p in
            let rec go seq pulls =
                if pulls >= max_inst then ()
                else match seq () with
                | Seq.Nil -> ()
                | Seq.Cons (f, rest) ->
                    let key = L.fact_key f in
                    if G.FactSet.mem key !seen_fact then go rest (pulls + 1)
                    else (seen_fact := G.FactSet.add key !seen_fact;
                          incr count; emit (); go rest (pulls + 1)) in
            go seq 0 in

        let build_wave ~store =
            let fresh = ref [] in
            let handle p =
                check_deadline ();
                if register p then begin
                    if interleaved && is_output p then concretize p;
                    if store then fresh := p :: !fresh
                end in
            Array.iteri (fun ci (_, _, _, suitable, expand) ->
                let is = rule_inputs.(ci) in
                let m = Array.length is in
                if m > 0 then
                    for d = 0 to m - 1 do
                        let rec go i acc =
                            if i = m then begin
                                check_deadline ();
                                let inputs = List.rev acc in
                                if suitable inputs then Seq.iter handle (expand inputs)
                            end else
                                let pool = pools.(is.(i)) in
                                let lo = if i = d then pool.old else 0 in
                                let hi = if i < d then pool.old else pool.n in
                                for j = lo to hi - 1 do go (i + 1) (pool.arr.(j) :: acc) done in
                        go 0 []
                    done) rules_arr;
            let added = List.rev !fresh in
            Array.iter (fun pool -> pool.old <- pool.n) pools;
            if store then List.iter (fun p -> push pools.(L.prototerm_sort p) p) added;
            if not interleaved then
                List.iter (fun p -> if is_output p then concretize p) added;
            List.length added in

        (try
            let seeds = ref [] in
            let rec drain st =
                match L.next_seed config st with
                | None -> ()
                | Some (p, st') ->
                    if register p then begin
                        push pools.(L.prototerm_sort p) p;
                        seeds := p :: !seeds;
                        if interleaved && is_output p then concretize p
                    end;
                    drain st' in
            drain L.initial_seeds;
            if not interleaved then
                List.iter (fun p -> if is_output p then concretize p) (List.rev !seeds);
            Printf.eprintf "wave 0: %d prototerms, %d concrete\n%!"
                (List.length !seeds) !count;
            let w = ref 0 in
            let continue = ref true in
            while !continue do
                incr w;
                let store = not (interleaved && !w >= waves) in
                let facts_before = !count in
                let added = build_wave ~store in
                Printf.eprintf "wave %d: %d prototerms, %d concrete\n%!"
                    !w added (!count - facts_before);
                if added = 0 || !w >= waves then continue := false
            done
        with Reached -> ());
        let total = Unix.gettimeofday () -. start in
        close_out oc;
        Printf.printf "%s: %d concrete terms in %.2fs -> %s\n%!"
            (if interleaved then "lazy" else "eager") !count total csv
end

let () =
    let lang = ref "comb" in
    let term_kind = ref Generator.Ill_typed in
    let max_inst = ref 1 in
    let interleaved = ref true in
    let waves = ref 3 in
    let target = ref max_int in
    let timeout = ref None in
    let sample = ref 0.25 in
    let csv = ref "out.csv" in
    let settings = ref [] in
    let rec parse = function
        | [] -> ()
        | "--lazy" :: r -> interleaved := true; parse r
        | "--eager" :: r -> interleaved := false; parse r
        | "--well-typed" :: r -> term_kind := Generator.Well_typed; parse r
        | "--ill-typed" :: r -> term_kind := Generator.Ill_typed; parse r
        | "--max-inst" :: v :: r -> max_inst := int_of_string v; parse r
        | "--waves" :: v :: r -> waves := int_of_string v; parse r
        | "--target" :: v :: r -> target := int_of_string v; parse r
        | "--timeout" :: v :: r -> timeout := Some (float_of_string v); parse r
        | "--sample" :: v :: r -> sample := float_of_string v; parse r
        | "--csv" :: v :: r -> csv := v; parse r
        | "--set" :: v :: r ->
            (match String.index_opt v '=' with
             | Some i -> settings := (String.sub v 0 i,
                 String.sub v (i + 1) (String.length v - i - 1)) :: !settings
             | None -> ());
            parse r
        | a :: r -> lang := a; parse r in
    parse (List.tl (Array.to_list Sys.argv));
    let term_kind = !term_kind and max_inst = !max_inst in
    let interleaved = !interleaved and waves = !waves and target = !target in
    let timeout = !timeout in
    let sample = !sample and csv = !csv in
    let settings = List.rev !settings in
    match !lang with
    | "comb" ->
        let module E = Make (CombGenerator) in
        E.run ~interleaved ~waves ~target ~timeout ~sample
            ~config:(CombGenerator.parse_config settings) ~term_kind ~max_inst ~csv
    | s -> prerr_endline ("unknown language: " ^ s); exit 1
