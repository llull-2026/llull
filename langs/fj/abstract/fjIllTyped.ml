open FjPrograms
open FjPrototerms
open FjConcretization

let rec max_sym_in_term acc = function
    | Var id -> max acc id
    | New (_, args) -> List.fold_left max_sym_in_term acc args
    | FieldAccess (e, _) -> max_sym_in_term acc e
    | MethodInvoke (e, _, args) ->
        List.fold_left max_sym_in_term (max_sym_in_term acc e) args

let max_sym_in_fact (f : tagged_fact) =
    let m0 = List.fold_left (fun a (s, _) -> max a s) (-1) f.tf_bindings in
    let m1 = List.fold_left (fun a m ->
        let a = max a m.cm_this_sym in
        List.fold_left (fun a (s, _) -> max a s) a m.cm_params
    ) m0 f.tf_methods in
    let m2 = max_sym_in_term m1 f.tf_main_term in
    List.fold_left (fun a m -> max_sym_in_term a m.cm_body) m2 f.tf_methods

let max_class_in_fact (f : tagged_fact) =
    List.fold_left (fun a c -> max a c.cc_label) (-1) f.tf_classes

let rec rfind_sub r needle k =
    let len = String.length r in
    let nlen = String.length needle in
    if k < 0 then 0 else
    if k + nlen <= len && String.sub r k nlen = needle then k else
    rfind_sub r needle (k - 1)

let rerender_main (f : tagged_fact) =
    let r = f.tf_rendered in
    let needle = "main: " in
    let cut = rfind_sub r needle (String.length r - String.length needle) in
    String.sub r 0 cut
    ^ "main: " ^ string_of_term f.tf_main_term
    ^ " : " ^ string_of_concrete_type f.tf_main_type

let mutate_unbound_var (f : tagged_fact) =
    let fresh = max_sym_in_fact f + 1 in
    let f' = { f with
        tf_main_term = Var fresh;
        tf_main_type = ConcreteObject } in
    { f' with tf_rendered = rerender_main f' }

let mutate_unknown_new (f : tagged_fact) =
    let fresh = max_class_in_fact f + 1 in
    let f' = { f with
        tf_main_term = New (fresh, [New (-1, [])]);
        tf_main_type = ConcreteClass fresh } in
    { f' with tf_rendered = rerender_main f' }

let max_perturbations_per_prototerm = 256
let perturb_buckets = 8

let list_set xs i x' = List.mapi (fun j x -> if i = j then x' else x) xs

let list_drop_last = function
    | [] -> []
    | xs -> List.filteri (fun j _ -> j <> List.length xs - 1) xs

let obj = New (-1, [])

let perturb_here class_labels field_labels method_labels
        fresh_field fresh_method fresh_sym t =
    match t with
    | Var _ -> [Var fresh_sym]
    | New (c, args) ->
        List.filter_map (fun c' ->
            if c' = c then None else Some (New (c', args))) class_labels
        @ (if args = [] then [] else [New (c, list_drop_last args)])
        @ [New (c, args @ [obj])]
        @ List.mapi (fun i _ -> New (c, list_set args i obj)) args
    | FieldAccess (recv, fl) ->
        List.filter_map (fun fl' ->
            if fl' = fl then None else Some (FieldAccess (recv, fl')))
            (fresh_field :: field_labels)
        @ [FieldAccess (obj, fl)]
    | MethodInvoke (recv, ml, args) ->
        List.filter_map (fun ml' ->
            if ml' = ml then None else Some (MethodInvoke (recv, ml', args)))
            (fresh_method :: method_labels)
        @ [MethodInvoke (obj, ml, args)]
        @ (if args = [] then [] else [MethodInvoke (recv, ml, list_drop_last args)])
        @ [MethodInvoke (recv, ml, args @ [obj])]
        @ List.mapi (fun i _ -> MethodInvoke (recv, ml, list_set args i obj)) args

let rec perturbs_seq class_labels field_labels method_labels
        fresh_field fresh_method fresh_class fresh_sym t : term Seq.t =
    let recur = perturbs_seq class_labels field_labels method_labels
        fresh_field fresh_method fresh_class fresh_sym in
    let here = perturb_here class_labels field_labels method_labels
        fresh_field fresh_method fresh_sym t in
    let universal = [Var fresh_sym; New (fresh_class, [])] in
    let child_seqs = match t with
        | Var _ -> []
        | New (c, args) ->
            List.mapi (fun i arg ->
                Seq.map (fun a' -> New (c, list_set args i a')) (recur arg)) args
        | FieldAccess (recv, fl) ->
            [Seq.map (fun r' -> FieldAccess (r', fl)) (recur recv)]
        | MethodInvoke (recv, ml, args) ->
            Seq.map (fun r' -> MethodInvoke (r', ml, args)) (recur recv)
            :: List.mapi (fun i arg ->
                Seq.map (fun a' -> MethodInvoke (recv, ml, list_set args i a'))
                    (recur arg)) args
    in
    Helper.interleave (List.to_seq (here @ universal) :: child_seqs)

let refreshed_main_fact f mt' =
    let f' = { f with tf_main_term = mt' } in
    { f' with tf_rendered = rerender_main f' }

let perturb_main ~bucket (f : tagged_fact) : tagged_fact Seq.t =
    let class_labels = -1 :: List.map (fun c -> c.cc_label) f.tf_classes in
    let field_labels =
        List.sort_uniq compare
            (List.concat_map (fun c -> List.map fst c.cc_own_fields) f.tf_classes) in
    let method_labels =
        List.sort_uniq compare (List.map (fun m -> m.cm_label) f.tf_methods) in
    let fresh_field = List.fold_left max (-1) field_labels + 1 in
    let fresh_method = List.fold_left max (-1) method_labels + 1 in
    let fresh_class = max_class_in_fact f + 1 in
    let fresh_sym = max_sym_in_fact f + 1 in
    perturbs_seq class_labels field_labels method_labels
        fresh_field fresh_method fresh_class fresh_sym f.tf_main_term
    |> Seq.drop bucket
    |> Seq.take max_perturbations_per_prototerm
    |> Seq.map (refreshed_main_fact f)

let render_method_line (m : concrete_method_entry) =
    let params_s = String.concat ", " (List.map (fun (sid, pt) ->
        string_of_concrete_type pt ^ " x" ^ string_of_int sid) m.cm_params) in
    "  " ^ string_of_concrete_type m.cm_return ^ " " ^ ml_name m.cm_label
    ^ "(" ^ params_s ^ ") { return " ^ string_of_term m.cm_body ^ "; }\n"

let rec find_sub s old i =
    let slen = String.length s and olen = String.length old in
    if i + olen > slen then -1 else
    if String.sub s i olen = old then i else
    find_sub s old (i + 1)

let replace_first s old nw =
    let slen = String.length s and olen = String.length old in
    match find_sub s old 0 with
    | -1 -> s
    | i -> String.sub s 0 i ^ nw ^ String.sub s (i + olen) (slen - i - olen)

let break_method_at (f : tagged_fact) ((i, m) : int * concrete_method_entry) =
    let m' = { m with cm_body = obj } in
    let methods' = List.mapi (fun j mm -> if j = i then m' else mm) f.tf_methods in
    let rendered' =
        replace_first f.tf_rendered (render_method_line m) (render_method_line m') in
    { f with tf_methods = methods'; tf_rendered = rendered' }

let break_method_body (f : tagged_fact) : tagged_fact Seq.t =
    List.mapi (fun i m -> (i, m)) f.tf_methods
    |> List.filter (fun (_, m) ->
        match m.cm_return with ConcreteClass _ -> true | ConcreteObject -> false)
    |> List.to_seq
    |> Seq.map (break_method_at f)

let break_recipes p d =
    let class_ids = List.map (fun ce -> ce.cl_label) p.classes in
    match d with
    | Subtype (ObjectType, CVar b) ->
        List.map (fun cl -> [(b, ConcreteClass cl)]) class_ids
    | Subtype (CVar a, CVar b) when a <> b ->
        List.map (fun cl -> [(a, ConcreteObject); (b, ConcreteClass cl)]) class_ids
    | FieldCount (CVar a, k) ->
        let recipes = ref [] in
        if k > 0 then recipes := [(a, ConcreteObject)] :: !recipes;
        List.iter (fun ce ->
            if List.length ce.cl_fields <> k then
                recipes := [(a, ConcreteClass ce.cl_label)] :: !recipes
        ) p.classes;
        !recipes
    | NeedField (CVar r, _, _) ->
        [[(r, ConcreteObject)]]
        @ List.map (fun cl -> [(r, ConcreteClass cl)]) class_ids
    | NeedMethod (CVar r, _, _, _) ->
        [[(r, ConcreteObject)]]
        @ List.map (fun cl -> [(r, ConcreteClass cl)]) class_ids
    | _ -> []

let override_assignment fixed assignment =
    List.map (fun (i, t) ->
        match List.assoc_opt i fixed with
        | Some t' -> (i, t')
        | None -> (i, t)) assignment

let breaks_some_demand st assignment =
    check_label_neqs st.sfl st.sp.all_label_neqs
    && not (check_demands st.sp.classes st.sp.methods assignment
                st.sfl st.sml st.sp.all_demands)

let break_demand_facts config fixed e st =
    type_assignments config st
    |> Seq.map (override_assignment fixed)
    |> Seq.filter (breaks_some_demand st)
    |> Seq.map (fact_of_assignment e st)

let ground_fault config p fault : tagged_fact Seq.t =
    match fault with
    | BreakDemand fixed ->
        (match p.main with
         | None -> Seq.empty
         | Some e ->
             solve_program ~freeze_params:false p
             |> Seq.concat_map (break_demand_facts config fixed e))
    | MutateVar ->
        Seq.map mutate_unbound_var (instantiate_program_solved config p)
    | MutateNewClass ->
        Seq.map mutate_unknown_new (instantiate_program_solved config p)
    | MutatePerturb bucket ->
        Seq.concat_map (perturb_main ~bucket) (instantiate_program_solved config p)
    | MutateMethodBody ->
        Seq.concat_map break_method_body (instantiate_program_solved config p)

let concretize ~search_budget config = function
    | FaultedProgram (p, fault) -> ground_fault config p fault
    | s -> FjConcretization.concretize ~search_budget config s

let techniques = [
    (fun _config s ->
        match s with
        | ProgramPrototerm p ->
            let recipes =
                List.concat_map (break_recipes p) p.all_demands in
            List.to_seq (List.map (fun r -> FaultedProgram (p, BreakDemand r)) recipes)
        | _ -> Seq.empty);
    (fun _config s ->
        match s with
        | ProgramPrototerm p ->
            List.to_seq [FaultedProgram (p, MutateVar);
                         FaultedProgram (p, MutateNewClass);
                         FaultedProgram (p, MutateMethodBody)]
        | _ -> Seq.empty);
    (fun _config s ->
        match s with
        | ProgramPrototerm p ->
            List.to_seq
                (List.init perturb_buckets (fun k -> FaultedProgram (p, MutatePerturb k)))
        | _ -> Seq.empty);
]
