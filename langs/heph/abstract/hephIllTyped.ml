open HephPrograms
open HephPrototerms
open HephConcretization

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

let break_recipes config p d =
    let scope0 = types_up_to p ~scope_tparams:0 config.max_type_depth in
    let class_types =
        List.filter (function TyClass _ -> true | _ -> false) scope0 in
    let object_type = TyClass (Prelude "Object", []) in
    match d with
    | Subtype (TVar a, TVar b) when a <> b ->
        List.map (fun ct -> [(a, object_type); (b, ct)]) class_types
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
             candidate_groundings ~cap:illtyped_assignment_cap ~fixed config p
             |> budget_take search_budget
             |> Seq.filter (fun (assignment, fl_map, ml_map) ->
                 check_label_neqs fl_map ml_map p.all_label_neqs
                 && not (check_demands p assignment fl_map ml_map p.all_demands))
             |> Seq.map (fun (assignment, fl_map, ml_map) ->
                 build_tagged_fact_for p e assignment fl_map ml_map))
    | MutateVar ->
        Seq.map mutate_unbound_var (instantiate_program ~search_budget config p)
    | MutateBVar ->
        Seq.map mutate_bvar_oob (instantiate_program ~search_budget config p)
    | AddBoundViolation ce ->
        instantiate_program ~search_budget config { p with classes = ce :: p.classes }

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
           && Hashtbl.hash p land (bound_gate - 1) = 0 ->
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
                if Hashtbl.hash p land (mutator_gate - 1) = 0
                then [FaultedProgram (p, MutateVar); FaultedProgram (p, MutateBVar)]
                else []
            in
            List.to_seq (breaks @ mutators)
        | _ -> Seq.empty);
]
