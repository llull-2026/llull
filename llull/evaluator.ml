let string_of_term_kind = function
    | Generator.Well_typed -> "well-typed"
    | Generator.Ill_typed -> "ill-typed"

type severity = [ `Shallow | `Medium | `Deep | `Unnatural ]
type polarity = [ `Accept | `Reject ]

type 'fact bug =
    string * string * int * severity * string * polarity * ('fact -> bool)

let string_of_severity = function
    | `Shallow -> "S" | `Medium -> "M" | `Deep -> "D" | `Unnatural -> "U"

type config = {
    num_terms        : int;
    time_limit       : float;
    variants         : bool;
    output_csv       : string option;
    show_progress    : bool;
    progress_by_time : bool;
    print_terms      : bool;
    checkin_secs     : float;
    stall_secs       : float;
    time_offset      : float;
    max_rss_kb       : int;
    catch_log        : string option;
    trace_file       : string option;
    trace_every      : int;
    stop_when_all    : bool;
}

let default_config = {
    num_terms = 100_000;
    time_limit = 60.0;
    variants = false;
    output_csv = None;
    show_progress = true;
    progress_by_time = false;
    print_terms = false;
    checkin_secs = 300.0;
    stall_secs = 0.0;
    time_offset = 0.0;
    max_rss_kb = 0;
    catch_log = None;
    trace_file = None;
    trace_every = 10_000;
    stop_when_all = false;
}

type bug_catch = {
    catch_name : string;
    catch_model : string;
    catch_bug_id : int;
    catch_severity : severity;
    iteration : int;
    time : float;
    cpu_time : float;
    counterexample : string;
}

type uncaught = {
    u_name : string;
    u_model : string;
    u_bug_id : int;
    u_severity : severity;
    u_description : string;
}

type result = {
    language : string;
    term_kind : Generator.term_kind;
    total_bugs : int;
    total_iterations : int;
    total_time : float;
    cpu_time : float;
    gen_time : float;
    check_time : float;
    peak_rss_kb : int;
    stop_reason : string;
    caught : bug_catch list;
    uncaught : uncaught list;
}

let difficulty_tag = function `Easy -> "E" | `Medium -> "M" | `Hard -> "H"

let string_of_difficulty = function `Easy -> "easy" | `Medium -> "medium" | `Hard -> "hard"

let difficulty_of_name name =
    match String.index_opt name '+' with
    | None -> `Easy
    | Some i ->
        if i + 2 < String.length name && name.[i+2] = ':' then
            match name.[i+1] with 'M' -> `Medium | 'H' -> `Hard | _ -> `Easy
        else `Easy

let term_atom_holds ~parent_child ~grandparent_grandchild ~ancestor_descendant ~tag_eq atom fact =
    match atom with
    | `Parent (x, y) ->
        List.exists (fun (p, c) -> tag_eq p y && tag_eq c x) (parent_child fact)
    | `Child (x, y) ->
        List.exists (fun (p, c) -> tag_eq p x && tag_eq c y) (parent_child fact)
    | `Grandparent (x, y) ->
        List.exists (fun (g, c) -> tag_eq g y && tag_eq c x) (grandparent_grandchild fact)
    | `Grandchild (x, y) ->
        List.exists (fun (g, c) -> tag_eq g x && tag_eq c y) (grandparent_grandchild fact)
    | `Ancestor (x, y) ->
        List.exists (fun (a, d) -> tag_eq a y && tag_eq d x) (ancestor_descendant fact)
    | `Descendant (x, y) ->
        List.exists (fun (a, d) -> tag_eq a x && tag_eq d y) (ancestor_descendant fact)

let class_atom_holds ~class_ancestors ~cid_eq atom fact =
    let pairs = class_ancestors fact in
    match atom with
    | `ClassAncestor (descendant, ancestor) ->
        List.exists (fun (d, a) -> cid_eq d descendant && cid_eq a ancestor) pairs
    | `ClassDepthAtLeast n ->
        let counts = Hashtbl.create 16 in
        List.iter (fun (d, _) ->
            let prev = try Hashtbl.find counts d with Not_found -> 0 in
            Hashtbl.replace counts d (prev + 1)) pairs;
        Hashtbl.fold (fun _ c acc -> acc || c >= n) counts false

let expand ~catalog ~optout ~adapter base =
    let (parent_child, grandparent_grandchild, ancestor_descendant,
         class_ancestors, tag_eq, cid_eq) = adapter in
    let matches (_, _, term_atom, class_atom) fact =
        let term_ok = match term_atom with
            | None -> true
            | Some atom -> term_atom_holds ~parent_child ~grandparent_grandchild
                               ~ancestor_descendant ~tag_eq atom fact in
        let class_ok = match class_atom with
            | None -> true
            | Some atom -> class_atom_holds ~class_ancestors ~cid_eq atom fact in
        term_ok && class_ok in
    let variant (name, model, bug_id, sev, desc, pol, check) ((id, diff, _, _) as pat) =
        let check' fact =
            if matches pat fact then check fact
            else (match pol with `Accept -> true | `Reject -> false) in
        (name ^ "+" ^ difficulty_tag diff ^ ":" ^ id, model, bug_id, sev, desc, pol, check') in
    List.concat_map (fun ((name, _, _, _, _, _, _) as bug) ->
        List.filter_map (fun ((id, _, _, _) as pat) ->
            if optout name id then None else Some (variant bug pat)) catalog) base

let progress_bar_width = 40

let bar_of_fraction pct =
    let pct = if pct < 0.0 then 0.0 else if pct > 1.0 then 1.0 else pct in
    let filled = int_of_float (pct *. float_of_int progress_bar_width) in
    let empty = progress_bar_width - filled in
    Printf.sprintf "[%s%s]" (String.make filled '#') (String.make empty '-')

let show_progress ~by_time ~generated ~num_terms ~elapsed ~time_limit
        ~bugs_caught ~total_bugs =
    let line =
        if by_time then
            let pct = if time_limit > 0.0 then elapsed /. time_limit else 0.0 in
            Printf.sprintf "\r%s %.1fs/%.0fs | %d terms | %d/%d bugs   "
                (bar_of_fraction pct) elapsed time_limit
                generated bugs_caught total_bugs
        else
            let pct =
                if num_terms > 0 then float_of_int generated /. float_of_int num_terms
                else 0.0 in
            Printf.sprintf "\r%s %d/%d terms | %.1fs | %d/%d bugs   "
                (bar_of_fraction pct) generated num_terms elapsed
                bugs_caught total_bugs in
    print_string line;
    flush stdout

let clear_progress () =
    Printf.printf "\r%s\r" (String.make 80 ' ');
    flush stdout

let proc_status_kb field =
    let n = String.length field in
    try
        let ic = open_in "/proc/self/status" in
        let rec find () =
            match input_line ic with
            | line when String.length line > n && String.sub line 0 n = field ->
                Scanf.sscanf (String.sub line n (String.length line - n)) " %d" (fun k -> k)
            | _ -> find () in
        let k = try find () with End_of_file -> 0 in
        close_in ic; k
    with Sys_error _ -> 0

let peak_rss_kb () = proc_status_kb "VmHWM:"
let heap_kb () = (Gc.quick_stat ()).Gc.heap_words * (Sys.word_size / 8) / 1024
let current_rss_kb () = proc_status_kb "VmRSS:"

let stop_requested = ref false

let csv_header =
    "bug,model,bug_id,severity,difficulty,caught,iteration,time,cpu_time,term_kind,counterexample\n"

let csv_catch_line term_kind (c : bug_catch) =
    let escaped =
        c.counterexample
        |> String.split_on_char '"'
        |> String.concat "\"\"" in
    Printf.sprintf "%s,%s,%d,%s,%s,true,%d,%.6f,%.6f,%s,\"%s\"\n"
        c.catch_name c.catch_model c.catch_bug_id
        (string_of_severity c.catch_severity)
        (string_of_difficulty (difficulty_of_name c.catch_name))
        c.iteration c.time c.cpu_time
        (string_of_term_kind term_kind)
        escaped

let run (config : config) (term_kind : Generator.term_kind) (opts : Generator.opts)
        ~name ~term_to_string ~(bugs : 'fact bug list) ~(gen : unit -> 'fact option)
        ?(exhausted = fun () -> false) ?(pool_size = fun () -> 0)
        ?(metrics = fun () -> Generator.Metrics.empty) () : result =
    let total_bugs = List.length bugs in

    let start_time = Unix.gettimeofday () -. config.time_offset in
    let start_cpu = Sys.time () in
    let gen_time = ref 0.0 and check_time = ref 0.0 in
    let caught = ref [] in
    let remaining = ref bugs in
    let generated = ref 0 in

    let time_active = config.time_limit > 0.0 in
    let time_ok () =
        not time_active
        || Unix.gettimeofday () -. start_time < config.time_limit in

    let last_term_time = ref start_time in
    let stalled = ref false in
    let stop_reason = ref "terms" in

    let out_of_memory = ref false in
    let memory_ok () =
        if config.max_rss_kb <= 0 || !out_of_memory then not !out_of_memory
        else begin
            let rss = current_rss_kb () in
            if rss > config.max_rss_kb then begin
                out_of_memory := true;
                Printf.eprintf "[memory] resident %d MB > limit %d MB -> stopping at %d terms\n%!"
                    (rss / 1024) (config.max_rss_kb / 1024) !generated
            end;
            not !out_of_memory
        end in

    let prototerm_counts () =
        List.fold_left (fun (i, p) (d, c) -> (i + c, if d > 0 then p + c else p))
            (0, 0) (metrics ()).Generator.Metrics.conc_hist in

    let catch_oc = Option.map (fun f ->
        let oc = open_out f in output_string oc csv_header; flush oc; oc) config.catch_log in
    let trace_oc = Option.map (fun f ->
        let oc = open_out f in
        output_string oc ("terms,time,cpu_time,gen_time,check_time,bugs,rss_kb,heap_kb,"
            ^ "pool_prototerms,prototerms_instantiated,productive_prototerms\n"); flush oc; oc)
        config.trace_file in
    let last_traced = ref (-1) in
    let last_trace_time = ref (Unix.gettimeofday ()) in
    let trace () = match trace_oc with
        | None -> ()
        | Some _ when !last_traced = !generated -> ()
        | Some oc ->
            last_traced := !generated;
            last_trace_time := Unix.gettimeofday ();
            let (inst, productive) = prototerm_counts () in
            Printf.fprintf oc "%d,%.3f,%.3f,%.3f,%.3f,%d,%d,%d,%d,%d,%d\n%!" !generated
                (Unix.gettimeofday () -. start_time) (Sys.time () -. start_cpu)
                !gen_time !check_time (total_bugs - List.length !remaining)
                (current_rss_kb ()) (heap_kb ()) (pool_size ()) inst productive in

    let rec gen_blocking () =
        if not (time_ok ()) then None
        else if !stop_requested || not (memory_ok ()) then None
        else if exhausted () then None
        else if config.stall_secs > 0.0
                && Unix.gettimeofday () -. !last_term_time > config.stall_secs
        then begin
            stalled := true;
            Printf.eprintf "[stall] no term for %.0fs -> stopping at %d terms\n%!"
                config.stall_secs !generated;
            None
        end
        else match gen () with
            | Some _ as t -> t
            | None -> gen_blocking () in

    let keep_going () =
        time_ok () && !generated < config.num_terms && not !stalled
        && not !stop_requested && not !out_of_memory
        && not (config.stop_when_all && !remaining = [])
        && (!generated land 255 <> 0 || memory_ok ())
        && not (exhausted ()) in

    let last_render = ref (-1.0) in
    let render () =
        if config.show_progress && not config.print_terms then begin
            let elapsed = Unix.gettimeofday () -. start_time in
            if elapsed -. !last_render >= 0.1 then begin
                last_render := elapsed;
                let bugs_caught = total_bugs - List.length !remaining in
                show_progress ~by_time:config.progress_by_time
                    ~generated:!generated ~num_terms:config.num_terms
                    ~elapsed ~time_limit:config.time_limit
                    ~bugs_caught ~total_bugs
            end
        end in

    let last_checkin = ref start_time in
    let checkin () =
        if config.checkin_secs > 0.0 then begin
            let now = Unix.gettimeofday () in
            if now -. !last_checkin >= config.checkin_secs then begin
                last_checkin := now;
                let elapsed = now -. start_time in
                let bugs_caught = total_bugs - List.length !remaining in
                let rate = if elapsed > 0.0
                    then float_of_int !generated /. elapsed else 0.0 in
                let (inst, _) = prototerm_counts () in
                Printf.eprintf
                    "[checkin] %s (%s)  %.0fs  terms=%d  bugs=%d/%d  %.1f t/s  rss=%dMB  heap=%dMB  pool=%d  proto=%d\n%!"
                    name (string_of_term_kind term_kind) elapsed
                    !generated bugs_caught total_bugs rate (current_rss_kb () / 1024)
                    (heap_kb () / 1024) (pool_size ()) inst
            end
        end in

    Printf.printf "\n";
    Printf.printf "================================================================================\n";
    Printf.printf "  Eval suite: %s (%s)\n" name (string_of_term_kind term_kind);
    Printf.printf "================================================================================\n";
    Printf.printf "\n";
    Printf.printf "Bugs to find: %d\n" total_bugs;
    Printf.printf "Stop after: %s    Time limit: %s\n"
        (Printf.sprintf "%d generated terms" config.num_terms)
        (if time_active then Printf.sprintf "%.0fs" config.time_limit else "none");
    Printf.printf "Mode: %s    Strategy: %s\n"
        (match opts.mode with
         | Generator.Enumerate -> "enumerate"
         | Generator.Random Generator.Persistent -> "random (persistent pool)"
         | Generator.Random Generator.Fresh -> "random (fresh pool per term)"
         | Generator.Random (Generator.Triangle { x; y }) ->
             Printf.sprintf "random (triangle x=%d y=%d)" x y)
        (Enumerators.string_of_strategy opts.strategy);
    Printf.printf "Variants: %s    Max inst/proto-term: %d\n"
        (if config.variants then "on" else "off")
        opts.max_inst;
    Printf.printf "\n";

    while keep_going () do
        let gen_start = Unix.gettimeofday () in
        let next = gen_blocking () in
        gen_time := !gen_time +. (Unix.gettimeofday () -. gen_start);
        match next with
        | None -> ()
        | Some term ->
            incr generated;
            last_term_time := Unix.gettimeofday ();
            let check_start = !last_term_time in
            if config.print_terms then print_endline (term_to_string term);

            let newly_caught = ref [] in
            remaining := List.filter (fun bug ->
                let (bname, bmodel, bid, bsev, _, pol, check) = bug in
                let exposed = match pol with
                    | `Accept -> not (check term)
                    | `Reject -> check term in
                if exposed then begin
                    let elapsed = Unix.gettimeofday () -. start_time in
                    let catch = {
                        catch_name = bname;
                        catch_model = bmodel;
                        catch_bug_id = bid;
                        catch_severity = bsev;
                        iteration = !generated;
                        time = elapsed;
                        cpu_time = Sys.time () -. start_cpu;
                        counterexample = term_to_string term;
                    } in
                    newly_caught := catch :: !newly_caught;
                    false
                end
                else true) !remaining;
            check_time := !check_time +. (Unix.gettimeofday () -. check_start);

            List.iter (fun (catch : bug_catch) ->
                caught := catch :: !caught;
                Option.iter (fun oc ->
                    output_string oc (csv_catch_line term_kind catch); flush oc) catch_oc)
                (List.rev !newly_caught);
            if !generated mod config.trace_every = 0
               || Unix.gettimeofday () -. !last_trace_time >= 60. then trace ();
            render ();
            checkin ()
    done;
    if config.show_progress && not config.print_terms then clear_progress ();
    if exhausted () then
        Printf.eprintf
            "[exhausted] generation space fully explored at %d terms -> stopping\n%!"
            !generated;
    stop_reason :=
        if config.stop_when_all && !remaining = [] then "all-caught"
        else if !out_of_memory then "memory"
        else if !stop_requested then "signal"
        else if !stalled then "stall"
        else if exhausted () then "exhausted"
        else if !generated >= config.num_terms then "terms"
        else "time";
    if !stop_requested then
        Printf.eprintf "[signal] stop requested -> stopping at %d terms\n%!" !generated;
    trace ();
    Option.iter close_out catch_oc;
    Option.iter close_out trace_oc;

    let end_time = Unix.gettimeofday () in
    let total_time = end_time -. start_time in
    let cpu_time = Sys.time () -. start_cpu in
    let caught_list = List.rev !caught in
    let uncaught_list = List.map (fun bug ->
        let (bname, bmodel, bid, bsev, bdesc, _, _) = bug in
        { u_name = bname; u_model = bmodel; u_bug_id = bid;
          u_severity = bsev; u_description = bdesc }) !remaining in

    Printf.printf "\n";
    Printf.printf "================================================================================\n";
    Printf.printf "  Results\n";
    Printf.printf "================================================================================\n";
    Printf.printf "\n";
    Printf.printf "Terms generated: %d\n" !generated;
    Printf.printf "Total time: %.2fs\n" total_time;
    if total_time > 0.0
    then Printf.printf "Rate: %.0f terms/sec\n"
            (float_of_int !generated /. total_time);
    Printf.printf "Bugs caught: %d / %d\n"
        (List.length caught_list) total_bugs;
    Printf.printf "\n";

    { language = name;
      term_kind;
      total_bugs;
      total_iterations = !generated;
      total_time;
      cpu_time;
      gen_time = !gen_time;
      check_time = !check_time;
      peak_rss_kb = peak_rss_kb ();
      stop_reason = !stop_reason;
      caught = caught_list;
      uncaught = uncaught_list }

let write_csv filename (r : result) =
    let oc = open_out filename in
    output_string oc csv_header;
    List.iter (fun c -> output_string oc (csv_catch_line r.term_kind c)) r.caught;
    List.iter (fun (u : uncaught) ->
        Printf.fprintf oc "%s,%s,%d,%s,%s,false,%d,%.6f,%.6f,%s,\"\"\n"
            u.u_name u.u_model u.u_bug_id
            (string_of_severity u.u_severity)
            (string_of_difficulty (difficulty_of_name u.u_name))
            r.total_iterations r.total_time r.cpu_time
            (string_of_term_kind r.term_kind)) r.uncaught;
    close_out oc;
    Printf.printf "Results written to %s\n" filename

let write_meta ?generator ?(real_world = false) ?seed filename ~(opts : Generator.opts) ~settings
        ~(metrics : Generator.Metrics.t) (r : result) =
    let rate =
        if r.total_time > 0.0
        then float_of_int r.total_iterations /. r.total_time else 0.0 in
    let total_conc =
        List.fold_left (fun a (d, c) -> a + d * c) 0 metrics.Generator.Metrics.conc_hist in
    let prototerms_inst =
        List.fold_left (fun a (_, c) -> a + c) 0 metrics.Generator.Metrics.conc_hist in
    let productive =
        List.fold_left (fun a (d, c) -> if d > 0 then a + c else a) 0
            metrics.Generator.Metrics.conc_hist in
    let bugs_found = List.length r.caught in
    let mode_str = match opts.mode with
        | Generator.Enumerate -> "enumerate"
        | Generator.Random Generator.Persistent -> "random-persistent"
        | Generator.Random Generator.Fresh -> "random-fresh"
        | Generator.Random (Generator.Triangle { x; y }) ->
            Printf.sprintf "random-triangle:x=%d:y=%d" x y in
    let mode_str = match generator with Some g -> g | None -> mode_str in
    let opt_int = function Some i -> string_of_int i | None -> "" in
    let oc = open_out filename in
    let p fmt = Printf.fprintf oc fmt in
    p "# Run-level eval metadata.\n";
    p "# Headline: %d/%d bugs found at %.1f terms/sec.\n" bugs_found r.total_bugs rate;
    p "[results]\n";
    p "language = %s\n" r.language;
    p "real_world = %b\n" real_world;
    p "seed = %s\n" (match seed with Some n -> string_of_int n | None -> "");
    p "term_kind = %s\n" (string_of_term_kind r.term_kind);
    p "generator = %s\n" mode_str;
    p "strategy = %s\n" (Enumerators.string_of_strategy opts.strategy);
    p "scheduler = %s\n"
        (match opts.scheduler with
         | Generator.CfgRoundRobin -> "round-robin"
         | Generator.CfgEpoch { stall_limit } -> Printf.sprintf "epoch:%d" stall_limit
         | Generator.CfgAdaptive { alpha; epsilon } ->
             Printf.sprintf "adaptive:%g:%g" alpha epsilon);
    p "max_inst = %d\n" opts.max_inst;
    p "dovetail = %b\n" opts.dovetail;
    p "max_size = %s\n" (opt_int opts.bounds.Generator.max_size);
    p "max_depth = %s\n" (opt_int opts.bounds.Generator.max_depth);
    p "max_unique_vars = %s\n" (opt_int opts.bounds.Generator.max_unique_vars);
    p "stop_prob = %s\n"
        (match opts.stop_prob with Some x -> Printf.sprintf "%g" x | None -> "");
    p "inverse_weight = %b\n" opts.inverse_weight;
    p "warmup_steps = %d\n" opts.warmup_steps;
    p "term_time = %s\n"
        (match opts.term_time with Some x -> Printf.sprintf "%g" x | None -> "");
    p "term_timeouts = %d\n" !Generator.term_timeouts;
    p "settings = %s\n"
        (String.concat ";" (List.map (fun (k, v) -> k ^ "=" ^ v) settings));
    p "bugs_found = %d\n" bugs_found;
    p "total_bugs = %d\n" r.total_bugs;
    p "total_terms = %d\n" r.total_iterations;
    p "total_time = %.4f\n" r.total_time;
    p "generation_rate = %.4f\n" rate;
    p "cpu_time = %.4f\n" r.cpu_time;
    p "gen_time = %.4f\n" r.gen_time;
    p "check_time = %.4f\n" r.check_time;
    p "peak_rss_kb = %d\n" r.peak_rss_kb;
    p "stop_reason = %s\n" r.stop_reason;
    p "actual_concretizations = %d\n" total_conc;
    p "prototerms_instantiated = %d\n" prototerms_inst;
    p "productive_prototerms = %d\n" productive;
    p "conc_hist = %s\n"
        (String.concat ";"
           (List.map (fun (d, c) -> Printf.sprintf "%d:%d" d c)
              (List.sort compare metrics.Generator.Metrics.conc_hist)));
    close_out oc;
    Printf.printf "Run metadata written to %s\n" filename

module Engine (L : Language.LANGUAGE) = struct

    module G = Generator.Make (L)
    module R = RandomGen.Make (L)

    let rpool_size (st : R.rstate) = Array.fold_left (fun a p -> a + p.R.len) 0 st.rpools

    let make_stream ?(extra_seeds=[]) ?deadline ?concretize_steps ~settings
            (opts : Generator.opts) : G.stream =
        let config = L.parse_config settings in
        let time_ok () = match deadline with
            | Some d -> Unix.gettimeofday () < d
            | None -> true in
        let search_budget = match opts.mode with
            | Generator.Enumerate -> None
            | Generator.Random _ -> Some Generator.default_random_budget in
        match opts.mode with
        | Generator.Enumerate ->
            let fuel = match opts.fuel with Some f -> f | None -> 50000 in
            let state = ref (G.initial_state
                ~max_inst_per_prototerm:opts.max_inst ~fuel
                ~dovetail:opts.dovetail ?concretize_steps ?term_time:opts.term_time
                ~scheduler:opts.scheduler ~bounds:opts.bounds ~config ~search_budget
                ~term_kind:opts.term_kind opts.strategy) in
            { next = (fun () ->
                let (state', fact_opt) = G.next_fact !state (!state).fuel in
                state := state';
                fact_opt);
              metrics = (fun () -> (!state).metrics);
              exhausted = (fun () -> G.enumeration_exhausted !state);
              pool_size = (fun () -> G.total_pool_size !state) }
        | Generator.Random Generator.Persistent ->
            let st = R.init_rstate ~extra_seeds ~config () in
            let concretize = G.rotating_concretize ~search_budget config opts.term_kind in
            let stop_prob = match opts.stop_prob with Some p -> p | None -> 0.25 in
            let fuel = match opts.fuel with Some f -> f | None -> 200_000 in
            let buffered = ref [] in
            { next = (fun () ->
                R.rnext ~time_ok ~stop_prob ~fuel ~max_inst:opts.max_inst ~bounds:opts.bounds
                    ~inverse_weight:opts.inverse_weight ~spine_mode:opts.spine_mode
                    ~concretize ~buffered st);
              metrics = (fun () -> st.metrics);
              exhausted = (fun () -> false);
              pool_size = (fun () -> rpool_size st) }
        | Generator.Random Generator.Fresh ->
            let concretize = G.rotating_concretize ~search_budget config opts.term_kind in
            let stop_prob = match opts.stop_prob with Some p -> p | None -> 0.1 in
            let fuel = match opts.fuel with Some f -> f | None -> 10_000_000 in
            let acc = ref Generator.Metrics.empty in
            let sel = Array.make (List.length (L.rules config)) 0 in
            let buffered = ref [] in
            let rec attempt () =
                let st = R.init_rstate ~extra_seeds ~sel_counts:sel ~config () in
                st.metrics <- !acc;
                Generator.term_deadline := (match opts.term_time with
                    | Some t -> Unix.gettimeofday () +. t | None -> infinity);
                let r = try Some (R.step_loop ~time_ok ~stop_prob ~fuel ~max_inst:opts.max_inst
                                ~bounds:opts.bounds ~inverse_weight:opts.inverse_weight
                                ~spine_mode:opts.spine_mode ~concretize st)
                        with Generator.Term_timeout -> None in
                Generator.term_deadline := infinity;
                acc := st.metrics;
                match r with
                | Some facts -> facts
                | None -> incr Generator.term_timeouts; if time_ok () then attempt () else [] in
            { next = (fun () -> R.next_buffered buffered attempt);
              metrics = (fun () -> !acc);
              exhausted = (fun () -> false);
              pool_size = (fun () -> 0) }
        | Generator.Random (Generator.Triangle { x; y }) ->
            let concretize = G.rotating_concretize ~search_budget config opts.term_kind in
            let fuel = match opts.fuel with Some f -> f | None -> 10_000_000 in
            let acc = ref Generator.Metrics.empty in
            let sel = Array.make (List.length (L.rules config)) 0 in
            { next = (fun () ->
                let st = R.init_rstate ~extra_seeds ~sel_counts:sel ~config () in
                st.metrics <- !acc;
                let r = R.step_triangle ~time_ok ~x ~y ~fuel ~bounds:opts.bounds
                            ~inverse_weight:opts.inverse_weight
                            ~spine_mode:opts.spine_mode ~concretize st in
                acc := st.metrics;
                r);
              metrics = (fun () -> !acc);
              exhausted = (fun () -> false);
              pool_size = (fun () -> 0) }

    let warmup ~settings ~steps (opts : Generator.opts) : L.prototerm list =
        if steps <= 0 then []
        else
            let config = L.parse_config settings in
            match opts.mode with
            | Generator.Enumerate ->
                let state0 = G.initial_state
                    ~max_inst_per_prototerm:opts.max_inst
                    ~scheduler:opts.scheduler ~bounds:opts.bounds
                    ~config ~search_budget:None
                    ~term_kind:opts.term_kind opts.strategy in
                let rec drive st k =
                    if k <= 0 then st
                    else let (st', _) = G.next_fact st st.fuel in drive st' (k - 1) in
                let final = drive state0 steps in
                Array.fold_left (fun acc p ->
                    let rec take i acc =
                        if i >= p.G.n then acc else take (i + 1) (p.G.prototerms.(i) :: acc) in
                    take 0 acc) [] final.pools
            | Generator.Random _ ->
                let st = R.init_rstate ~config () in
                let concretize =
                    G.rotating_concretize ~search_budget:(Some Generator.default_random_budget)
                        config opts.term_kind in
                let buffered = ref [] in
                let rec drive k =
                    if k <= 0 then ()
                    else begin
                        ignore (R.rnext ~bounds:opts.bounds
                            ~inverse_weight:opts.inverse_weight
                            ~spine_mode:opts.spine_mode ~concretize ~buffered st);
                        drive (k - 1)
                    end in
                drive steps;
                Array.fold_left (fun acc p ->
                    let rec take i acc =
                        if i >= p.R.len then acc else take (i + 1) (p.R.arr.(i) :: acc) in
                    take 0 acc) [] st.rpools

    let evaluate ?(extra_seeds=[]) ?concretize_steps ~settings ~config
            ~name ~term_to_string ~to_testable ~fp_bugs ~fn_bugs ~variant_expand
            (opts : Generator.opts) =
        let term_kind = opts.term_kind in
        let base = match term_kind with
            | Generator.Well_typed -> fp_bugs
            | Generator.Ill_typed -> fn_bugs in
        let bugs = if config.variants then base @ variant_expand base else base in
        let extra_seeds = warmup ~settings ~steps:opts.warmup_steps opts @ extra_seeds in
        let deadline =
            if config.time_limit > 0.0
            then Some (Unix.gettimeofday () +. config.time_limit)
            else None in
        let stream = make_stream ?deadline ?concretize_steps ~extra_seeds ~settings opts in
        let gen () =
            match stream.next () with
            | None -> None
            | Some raw -> to_testable term_kind raw in
        let r = run config term_kind opts ~name ~term_to_string ~bugs ~gen
                    ~exhausted:stream.exhausted ~pool_size:stream.pool_size
                    ~metrics:stream.metrics () in
        (match config.output_csv with Some f -> write_csv f r | None -> ());
        (r, stream.metrics ())
end

let fj_variants base =
    expand ~catalog:FjVariants.catalog ~optout:FjVariants.optout
        ~adapter:FjVariants.adapter base
let comb_variants base =
    expand ~catalog:CombVariants.catalog ~optout:CombVariants.optout
        ~adapter:CombVariants.adapter base
let heph_variants base =
    expand ~catalog:HephVariants.catalog ~optout:HephVariants.optout
        ~adapter:HephVariants.adapter base
let replay_breccia ~name ~term_to_string ~facts_of_output ~bugs ~settings ~config
        (opts : Generator.opts) =
    let setting k = match List.assoc_opt k settings with
        | Some v -> v
        | None -> failwith (name ^ " needs --set " ^ k ^ "=...") in
    if opts.term_kind <> Generator.Well_typed then
        failwith (name ^ " generates only well-typed programs");
    let t0 = Unix.gettimeofday () in
    let facts = ref (facts_of_output (BrecciaOutput.read_file (setting "breccia_output"))) in
    let load_secs = Unix.gettimeofday () -. t0 in
    let config = { config with
        time_offset = float_of_string (setting "breccia_secs") +. load_secs } in
    let gen () = match !facts with
        | [] -> None
        | f :: rest -> facts := rest; Some f in
    let r = run config opts.term_kind opts ~name ~term_to_string ~bugs ~gen
        ~exhausted:(fun () -> !facts = []) () in
    (match config.output_csv with Some f -> write_csv f r | None -> ());
    (r, Generator.Metrics.empty)

let with_variants config expand base = if config.variants then base @ expand base else base

let evaluate_language lang ~real_world ~settings ~config (opts : Generator.opts) =
    if real_world && lang <> "heph" then failwith "--real-world applies only to heph";
    match lang with
    | "fj" ->
        let module E = Engine (FjGenerator) in
        E.evaluate ~settings ~config ~name:"fj"
            ~term_to_string:FjPrograms.string_of_fact
            ~to_testable:FjTranslation.to_testable
            ~fp_bugs:FjBugs.bugs ~fn_bugs:FjBugsIll.bugs ~variant_expand:fj_variants opts
    | "fj-concrete" ->
        let module E = Engine (FjConcreteGenerator) in
        E.evaluate ~settings ~config ~name:"fj-concrete"
            ~term_to_string:FjPrograms.string_of_fact
            ~to_testable:FjTranslation.to_testable_oracle
            ~fp_bugs:FjBugs.bugs ~fn_bugs:FjBugsIll.bugs ~variant_expand:fj_variants opts
    | "comb" ->
        let module E = Engine (CombGenerator) in
        E.evaluate ~settings ~config ~name:"comb"
            ~term_to_string:CombPrograms.string_of_fact
            ~to_testable:CombTranslation.to_testable
            ~fp_bugs:CombBugs.bugs ~fn_bugs:CombBugsIll.bugs ~variant_expand:comb_variants opts
    | "comb-concrete" ->
        let module E = Engine (CombConcreteGenerator) in
        E.evaluate ~settings ~config ~name:"comb-concrete"
            ~term_to_string:CombPrograms.string_of_fact
            ~to_testable:CombTranslation.to_testable_oracle
            ~fp_bugs:CombBugs.bugs ~fn_bugs:CombBugsIll.bugs ~variant_expand:comb_variants opts
    | "heph" when real_world ->
        let module E = Engine (HephRwGenerator) in
        E.evaluate ~settings ~config:{ config with variants = false } ~name:"heph"
            ~concretize_steps:HephRwGenerator.concretize_steps
            ~term_to_string:HephRwPrograms.string_of_fact
            ~to_testable:HephRwTranslation.to_testable
            ~fp_bugs:HephRwBugs.bugs ~fn_bugs:HephRwBugsIll.bugs ~variant_expand:(fun _ -> []) opts
    | "heph" ->
        let module E = Engine (HephGenerator) in
        E.evaluate ~settings ~config ~name:"heph"
            ~term_to_string:HephPrograms.string_of_fact
            ~to_testable:HephTranslation.to_testable
            ~fp_bugs:HephBugs.bugs ~fn_bugs:HephBugsIll.bugs ~variant_expand:heph_variants opts
    | "heph-concrete" ->
        let module E = Engine (HephConcreteGenerator) in
        E.evaluate ~settings ~config ~name:"heph-concrete"
            ~term_to_string:HephPrograms.string_of_fact
            ~to_testable:HephTranslation.to_testable
            ~fp_bugs:HephBugs.bugs ~fn_bugs:HephBugsIll.bugs ~variant_expand:heph_variants opts
    | "comb-breccia" ->
        replay_breccia ~name:lang ~term_to_string:CombPrograms.string_of_fact
            ~facts_of_output:CombBreccia.facts_of_output
            ~bugs:(with_variants config comb_variants CombBugs.bugs) ~settings ~config opts
    | "fj-breccia" ->
        replay_breccia ~name:lang ~term_to_string:FjPrograms.string_of_fact
            ~facts_of_output:FjBreccia.facts_of_output
            ~bugs:(with_variants config fj_variants FjBugs.bugs) ~settings ~config opts
    | "heph-breccia" ->
        replay_breccia ~name:lang ~term_to_string:HephPrograms.string_of_fact
            ~facts_of_output:HephBreccia.facts_of_output
            ~bugs:(with_variants config heph_variants HephBugs.bugs) ~settings ~config opts
    | _ -> failwith ("unknown language: " ^ lang)

let usage () =
    prerr_endline "usage: llull_eval <language> [options]";
    prerr_endline "  languages: fj fj-concrete comb comb-concrete heph heph-concrete";
    prerr_endline "             comb-breccia fj-breccia heph-breccia";
    prerr_endline "  --real-world                       (heph: the real-world bug suite; ignores --variants)";
    prerr_endline "  *-breccia replay breccia's programs: --set breccia_output=FILE --set breccia_secs=S";
    prerr_endline "  --strategy shell|naive|triangle    (default shell)";
    prerr_endline "  --mode enumerate|random-persistent|random-fresh   (default enumerate)";
    prerr_endline "  --scheduler round-robin|epoch|adaptive            (default round-robin)";
    prerr_endline "  --stall-limit N | --alpha F | --epsilon F         (epoch/adaptive params)";
    prerr_endline "  --well-typed | --ill-typed         (default ill-typed)";
    prerr_endline "  --max-inst N                       (default 1)";
    prerr_endline "  --max-size N | --max-depth N | --max-unique-vars N";
    prerr_endline "  --n N                              (term limit)";
    prerr_endline "  --time SECS                        (time limit)";
    prerr_endline "  --csv FILE                         (write results csv + .meta)";
    prerr_endline "  --variants                         (expand structural variants)";
    prerr_endline "  --quiet                            (no live bar; periodic check-ins still print)";
    prerr_endline "  --print-terms                      (print each generated term to stdout)";
    prerr_endline "  --progress-secs N                  (stderr progress every N s, default 120)";
    prerr_endline "  --stall-secs N                     (stop+write partial if no term for N s; 0=off)";
    prerr_endline "  --stop-prob P                      (random-walk stop probability)";
    prerr_endline "  --inverse-weight                   (random walk: inverse-frequency rule weighting)";
    prerr_endline "  --term-time S                      (random-fresh: abandon a term after S seconds;
                                      enumerate: end a prototerm's groundings after a step over S seconds)";
    prerr_endline "  --dovetail                         (enumerate: interleave every prototerm's groundings; ignores --max-inst)";
    prerr_endline "  --max-rss-mb N                     (stop+write results once resident memory passes N MB)";
    prerr_endline "  --catch-log FILE                   (csv of catches, written as each bug is caught)";
    prerr_endline "  --trace FILE                       (csv of terms/time/bugs/memory every --trace-every terms)";
    prerr_endline "  --trace-every N                    (default 10000)";
    prerr_endline "  --stop-when-all                    (stop once every bug is caught)";
    prerr_endline "  (SIGTERM or SIGUSR1 stops the run and writes its results)";
    prerr_endline "  --warmup N                         (pre-roll N steps as extra seeds before the run)";
    prerr_endline "  --seed N                           (fixed RNG seed, reproducible)";
    prerr_endline "  --unseed                           (fresh time-based RNG seed)";
    prerr_endline "  --set key=value                    (language config, repeatable)";
    exit 1

let () =
    let lang = ref "" in
    let strategy = ref "shell" in
    let mode = ref "enumerate" in
    let term_kind = ref Generator.Ill_typed in
    let max_inst = ref 1 in
    let dovetail = ref false in
    let real_world = ref false in
    let max_rss_mb = ref 0 in
    let catch_log = ref None in
    let trace_file = ref None in
    let trace_every = ref 10_000 in
    let stop_when_all = ref false in
    let max_size = ref None in
    let max_depth = ref None in
    let max_unique_vars = ref None in
    let n = ref None in
    let time = ref None in
    let csv = ref None in
    let variants = ref false in
    let quiet = ref false in
    let print_terms = ref false in
    let stall_secs = ref 0.0 in
    let progress_secs = ref 120.0 in
    let stop_prob = ref None in
    let inverse_weight = ref false in
    let warmup = ref 0 in
    let term_time = ref None in
    let seed = ref None in
    let unseed = ref false in
    let scheduler = ref "round-robin" in
    let stall_limit = ref 50 in
    let alpha = ref 0.1 in
    let epsilon = ref 0.1 in
    let settings = ref [] in
    let rec parse = function
        | [] -> ()
        | "--strategy" :: v :: r -> strategy := v; parse r
        | "--mode" :: v :: r -> mode := v; parse r
        | "--well-typed" :: r -> term_kind := Generator.Well_typed; parse r
        | "--ill-typed" :: r -> term_kind := Generator.Ill_typed; parse r
        | "--max-inst" :: v :: r -> max_inst := int_of_string v; parse r
        | "--max-size" :: v :: r -> max_size := Some (int_of_string v); parse r
        | "--max-depth" :: v :: r -> max_depth := Some (int_of_string v); parse r
        | "--max-unique-vars" :: v :: r -> max_unique_vars := Some (int_of_string v); parse r
        | "--n" :: v :: r -> n := Some (int_of_string v); parse r
        | "--time" :: v :: r -> time := Some (float_of_string v); parse r
        | "--csv" :: v :: r -> csv := Some v; parse r
        | "--variants" :: r -> variants := true; parse r
        | "--quiet" :: r -> quiet := true; parse r
        | "--print-terms" :: r -> print_terms := true; parse r
        | "--stall-secs" :: v :: r -> stall_secs := float_of_string v; parse r
        | "--progress-secs" :: v :: r -> progress_secs := float_of_string v; parse r
        | "--stop-prob" :: v :: r -> stop_prob := Some (float_of_string v); parse r
        | "--inverse-weight" :: r -> inverse_weight := true; parse r
        | "--warmup" :: v :: r -> warmup := int_of_string v; parse r
        | "--term-time" :: v :: r -> term_time := Some (float_of_string v); parse r
        | "--dovetail" :: r -> dovetail := true; parse r
        | "--real-world" :: r -> real_world := true; parse r
        | "--max-rss-mb" :: v :: r -> max_rss_mb := int_of_string v; parse r
        | "--catch-log" :: v :: r -> catch_log := Some v; parse r
        | "--trace" :: v :: r -> trace_file := Some v; parse r
        | "--trace-every" :: v :: r -> trace_every := int_of_string v; parse r
        | "--stop-when-all" :: r -> stop_when_all := true; parse r
        | "--scheduler" :: v :: r -> scheduler := v; parse r
        | "--stall-limit" :: v :: r -> stall_limit := int_of_string v; parse r
        | "--alpha" :: v :: r -> alpha := float_of_string v; parse r
        | "--epsilon" :: v :: r -> epsilon := float_of_string v; parse r
        | "--seed" :: v :: r -> seed := Some (int_of_string v); parse r
        | "--unseed" :: r -> unseed := true; parse r
        | "--set" :: v :: r ->
            (match String.index_opt v '=' with
             | Some i -> settings := (String.sub v 0 i,
                 String.sub v (i + 1) (String.length v - i - 1)) :: !settings
             | None -> usage ());
            parse r
        | ("-h" | "--help") :: _ -> usage ()
        | a :: r -> lang := a; parse r in
    parse (List.tl (Array.to_list Sys.argv));
    if !lang = "" then usage ();
    (match !seed with Some n -> Random.init n | None -> if !unseed then Random.self_init ());
    let mode_v = match !mode with
        | "enumerate" -> Generator.Enumerate
        | "random-persistent" -> Generator.Random Generator.Persistent
        | "random-fresh" -> Generator.Random Generator.Fresh
        | s -> prerr_endline ("unknown mode: " ^ s); exit 1 in
    let scheduler_v = match !scheduler with
        | "round-robin" | "rr" -> Generator.CfgRoundRobin
        | "epoch" -> Generator.CfgEpoch { stall_limit = !stall_limit }
        | "adaptive" -> Generator.CfgAdaptive { alpha = !alpha; epsilon = !epsilon }
        | s -> prerr_endline ("unknown scheduler: " ^ s); exit 1 in
    let opts = { Generator.default_opts with
        mode = mode_v;
        term_kind = !term_kind;
        strategy = Enumerators.strategy_of_string !strategy;
        scheduler = scheduler_v;
        max_inst = !max_inst;
        bounds = { Generator.max_size = !max_size;
                   max_depth = !max_depth;
                   max_unique_vars = !max_unique_vars };
        stop_prob = !stop_prob;
        inverse_weight = !inverse_weight;
        warmup_steps = !warmup;
        term_time = !term_time;
        dovetail = !dovetail } in
    let (num_terms, time_limit) = match (!n, !time) with
        | (None, None) -> (100_000, 300.0)
        | (Some k, None) -> (k, 0.0)
        | (None, Some t) -> (max_int, t)
        | (Some k, Some t) -> (k, t) in
    let settings = List.rev !settings in
    let config = { default_config with
        num_terms; time_limit; variants = !variants;
        output_csv = !csv; show_progress = not !quiet;
        print_terms = !print_terms;
        checkin_secs = !progress_secs; stall_secs = !stall_secs;
        max_rss_kb = !max_rss_mb * 1024; catch_log = !catch_log;
        trace_file = !trace_file; trace_every = max 1 !trace_every;
        stop_when_all = !stop_when_all } in
    List.iter (fun s -> Sys.set_signal s (Sys.Signal_handle (fun _ -> stop_requested := true)))
        [Sys.sigterm; Sys.sigusr1];
    let (r, metrics) = evaluate_language !lang ~real_world:!real_world ~settings ~config opts in
    match !csv with
    | Some f ->
        let generator = match !lang with
            | "comb-breccia" | "fj-breccia" | "heph-breccia" -> Some "breccia"
            | _ -> None in
        write_meta ?generator ~real_world:!real_world ?seed:!seed
            (Filename.remove_extension f ^ ".meta") ~opts ~settings ~metrics r
    | None -> ()
