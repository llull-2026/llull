open HephRwPrograms
open HephRwPrototerms
open HephRwConcretization

let object_ty = TyClass (Prelude "Object", [])

let rerender_main (f : tagged_fact) =
    let r = f.tf_rendered in
    let len = String.length r in
    let needle = "main: " in
    let nlen = String.length needle in
    let rec rfind k =
        if k < 0 then 0
        else if k + nlen <= len && String.sub r k nlen = needle then k
        else rfind (k - 1)
    in
    let cut = rfind (len - nlen) in
    String.sub r 0 cut
    ^ "main: " ^ string_of_term f.tf_main_term
    ^ " : " ^ string_of_type f.tf_main_type

let mutate_unbound_var (f : tagged_fact) =
    let fresh = List.fold_left (fun a (s, _) -> max a s) (-1) f.tf_bindings + 1 in
    let f' = { f with tf_main_term = Var fresh; tf_main_type = object_ty } in
    { f' with tf_rendered = rerender_main f' }

let mutate_bvar_oob (f : tagged_fact) =
    let f' = { f with tf_main_term = BVar 0; tf_main_type = object_ty } in
    { f' with tf_rendered = rerender_main f' }

let mutate_bad_default (f : tagged_fact) =
    match f.tf_methods with
    | [] -> f
    | m :: rest ->
        let bad = Some (TyClass (Prelude "Boolean", []),
                        New (TyClass (Prelude "Integer", []), [])) in
        { f with tf_methods = { m with cm_default = bad } :: rest }

let replace_first ~sub ~by str =
    let n = String.length sub and len = String.length str in
    let rec find i =
        if i + n > len then None
        else if String.sub str i n = sub then Some i
        else find (i + 1) in
    match find 0 with
    | None -> str
    | Some i -> String.sub str 0 i ^ by ^ String.sub str (i + n) (len - i - n)

let mutate_return config p ml (f : tagged_fact) =
    match List.find_opt (fun (m : concrete_method) -> m.cm_label = ml) f.tf_methods with
    | None -> Seq.empty
    | Some m ->
        let mbounds = List.map (fun tp -> tp.tp_bound) m.cm_tparams in
        let bounds = match List.find_opt (fun c -> c.cc_label = m.cm_class) f.tf_classes with
            | Some c -> List.map (fun tp -> tp.tp_bound) c.cc_tparams | None -> [] in
        types_up_to p ~scope_tparams:0 config.max_type_depth
        |> List.filter (fun t ->
            (match t with TyClass _ -> true | _ -> false)
            && not (is_subtype ~bounds ~mbounds p m.cm_return t))
        |> List.to_seq
        |> Seq.map (fun r ->
            let m' = { m with cm_return = r } in
            { f with
              tf_methods = List.map (fun x -> if x == m then m' else x) f.tf_methods;
              tf_rendered = replace_first ~sub:(render_cmethod m)
                  ~by:(render_cmethod m') f.tf_rendered })

let break_recipes config p d =
    let scope0 = types_up_to p ~scope_tparams:0 config.max_type_depth in
    let class_types =
        List.filter (function TyClass _ -> true | _ -> false) scope0 in
    let object_type = TyClass (Prelude "Object", []) in
    match d with
    | Subtype (TVar a, TVar b) when a <> b ->
        List.map (fun ct -> [(a, object_type); (b, ct)]) class_types
        @ List.map (fun ct -> [(a, ct)]) class_types
    | Subtype (TVar a, TyClass _) ->
        [(a, object_type)] :: List.map (fun ct -> [(a, ct)]) class_types
    | FieldCount (TVar a, k) ->
        let recipes = ref [] in
        if k > 0 then recipes := [(a, TyBot)] :: [(a, object_type)] :: !recipes;
        List.iter (fun ct ->
            match ct with
            | TyClass (cr, args) ->
                if List.length (fields_of_class p cr args) <> k then
                    recipes := [(a, ct)] :: !recipes
            | _ -> ()
        ) class_types;
        !recipes
    | NeedField (TVar r, _, _) ->
        [[(r, object_type)]; [(r, TyBot)]]
        @ List.map (fun ct -> [(r, ct)]) class_types
    | NeedMethod (TVar r, _, _, _) ->
        [[(r, object_type)]; [(r, TyBot)]]
        @ List.map (fun ct -> [(r, ct)]) class_types
    | _ -> []

let illtyped_assignment_cap = 128

let ground_fault ~search_budget config p fault : tagged_fact Seq.t =
    match fault with
    | BreakDemand fixed ->
        (match p.main with
         | None -> Seq.empty
         | Some e ->
             candidate_groundings ~cap:illtyped_assignment_cap ~fixed
                 ~randomize:(config.randomize_breaks && search_budget <> None) config p
             |> budget_take search_budget
             |> Seq.filter (fun (assignment, fl_map, ml_map) ->
                 check_label_neqs fl_map ml_map p.all_label_neqs
                 && not (check_demands ~opts:(demand_opts_of config)
                           p assignment fl_map ml_map p.all_demands))
             |> Seq.map (fun (assignment, fl_map, ml_map) ->
                 build_tagged_fact_for ~generic:config.generic_methods
                     p e assignment fl_map ml_map))
    | MutateVar ->
        Seq.map mutate_unbound_var (instantiate_program ~search_budget config p)
    | MutateBVar ->
        Seq.map mutate_bvar_oob (instantiate_program ~search_budget config p)
    | AddBoundViolation ce ->
        instantiate_program ~search_budget config { p with classes = ce :: p.classes }
    | BadDefault ->
        Seq.map mutate_bad_default (instantiate_program ~search_budget config p)
    | MutateReturn ml ->
        Seq.concat_map (mutate_return config p ml) (instantiate_program ~search_budget config p)

let ground_fault_steps config p fault : tagged_fact option Seq.t =
    let lift f = Seq.map (Option.map f) in
    match fault with
    | BreakDemand fixed ->
        (match p.main with
         | None -> Seq.empty
         | Some e ->
             grounding_steps ~fixed config p
             |> Seq.map (function
               | None -> None
               | Some (assignment, fl_map, ml_map) ->
                 if check_label_neqs fl_map ml_map p.all_label_neqs
                    && not (check_demands ~opts:(demand_opts_of config)
                              p assignment fl_map ml_map p.all_demands)
                 then Some (build_tagged_fact_for ~generic:config.generic_methods
                                p e assignment fl_map ml_map)
                 else None))
    | MutateVar -> lift mutate_unbound_var (instantiate_steps config p)
    | MutateBVar -> lift mutate_bvar_oob (instantiate_steps config p)
    | AddBoundViolation ce ->
        instantiate_steps config { p with classes = ce :: p.classes }
    | BadDefault -> lift mutate_bad_default (instantiate_steps config p)
    | MutateReturn ml ->
        Seq.concat_map (function
            | None -> Seq.return None
            | Some f ->
                (match mutate_return config p ml f () with
                 | Seq.Nil -> Seq.return None
                 | Seq.Cons (x, rest) -> Seq.map Option.some (Seq.cons x rest)))
            (instantiate_steps config p)

let gate_hash p =
    Hashtbl.hash_param 4096 65536 (p.classes, p.methods, p.main, p.all_demands, p.all_label_neqs,
                  p.tvar_scope, p.next_class_label, p.next_tvar, p.next_fl, p.next_ml)

let mutator_gate = 16

let bound_violation_pool =
    List.map (fun n -> TyClass (Prelude n, []))
        ["Object"; "Number"; "Integer"; "String"; "Boolean"]

let bound_violating_classes p =
    List.concat_map (fun ce ->
        if ce.cl_tparams = [] then []
        else
            capped_tuples bound_violation_pool (List.length ce.cl_tparams)
            |> List.filter (fun args ->
                not (bound_satisfied p (Synth ce.cl_label) args))
            |> List.map (fun args ->
                { cl_label = p.next_class_label;
                  cl_tparams = [];
                  cl_parent = (Synth ce.cl_label, args);
                  cl_fields = [] })
    ) p.classes

let max_bound_violations = 4

let bound_gate = 8

let bound_violation_technique config s =
    match auto_close_if_needed config s with
    | ProgramProtoTerm p
      when IntSet.cardinal (tvars_in_program p) <= config.max_tvars
           && gate_hash p land (bound_gate - 1) = 0 ->
        bound_violating_classes p
        |> List.filteri (fun i _ -> i < max_bound_violations)
        |> List.map (fun ce -> FaultedProgram (p, AddBoundViolation ce))
        |> List.to_seq
    | _ -> Seq.empty

let techniques = [
    bound_violation_technique;
    (fun config s ->
        match auto_close_if_needed config s with
        | ProgramProtoTerm p
          when IntSet.cardinal (tvars_in_program p) <= config.max_tvars ->
            let breaks =
                if p.all_demands = [] then []
                else
                    let recipes =
                        List.concat_map (break_recipes config p) p.all_demands @ [[]] in
                    List.map (fun r -> FaultedProgram (p, BreakDemand r)) recipes
            in
            let mutators =
                if gate_hash p land (mutator_gate - 1) = 0
                then [FaultedProgram (p, MutateVar); FaultedProgram (p, MutateBVar)]
                     @ (if p.methods <> [] then [FaultedProgram (p, BadDefault)] else [])
                     @ (if config.mutate_return
                        then List.map (fun me -> FaultedProgram (p, MutateReturn me.mt_label))
                               p.methods
                        else [])
                else []
            in
            List.to_seq (breaks @ mutators)
        | _ -> Seq.empty);
]
