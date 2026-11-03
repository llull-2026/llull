open FjPrograms
open FjPrototerms
open FjConcretePrototerms
open FjConcreteConcretization

let list_set xs i x' =
    List.mapi (fun j x -> if i = j then x' else x) xs

let list_drop xs i =
    List.filteri (fun j _ -> j <> i) xs

let all_class_labels classes =
    -1 :: List.map (fun ce -> ce.cl_label) classes

let all_field_labels classes =
    List.sort_uniq compare
        (List.concat_map (fun ce -> List.map fst ce.cl_fields) classes)

let all_method_labels methods =
    List.sort_uniq compare (List.map (fun me -> me.me_label) methods)

let perturbations_here classes methods (t : term) : term list =
    match t with
    | Var _ ->
        [Var 0; Var 1]
    | New (c, args) ->
        let labels = all_class_labels classes in
        let class_swaps =
            List.filter_map (fun c' ->
                if c' = c then None else Some (New (c', args))
            ) labels
        in
        let drops =
            if args = [] then [] else
            [New (c, list_drop args (List.length args - 1))]
        in
        let adds = [New (c, args @ [New (-1, [])])] in
        class_swaps @ drops @ adds
    | FieldAccess (recv, fl) ->
        let fl_swaps =
            List.filter_map (fun fl' ->
                if fl' = fl then None else Some (FieldAccess (recv, fl'))
            ) (all_field_labels classes)
        in
        let recv_to_object = [FieldAccess (New (-1, []), fl)] in
        fl_swaps @ recv_to_object
    | MethodInvoke (recv, ml, args) ->
        let ml_swaps =
            List.filter_map (fun ml' ->
                if ml' = ml then None else Some (MethodInvoke (recv, ml', args))
            ) (all_method_labels methods)
        in
        ml_swaps
        @ [MethodInvoke (recv, ml + 1, args);
           MethodInvoke (New (-1, []), ml, args)]

let rec perturbations classes methods (t : term) : term list =
    let here = perturbations_here classes methods t in
    let from_children = match t with
        | Var _ -> []
        | New (c, args) ->
            List.concat (List.mapi (fun i arg ->
                List.map (fun arg' ->
                    New (c, list_set args i arg')
                ) (perturbations classes methods arg)
            ) args)
        | FieldAccess (recv, fl) ->
            List.map (fun recv' -> FieldAccess (recv', fl))
                (perturbations classes methods recv)
        | MethodInvoke (recv, ml, args) ->
            let from_recv =
                List.map (fun recv' -> MethodInvoke (recv', ml, args))
                    (perturbations classes methods recv)
            in
            let from_args =
                List.concat (List.mapi (fun i arg ->
                    List.map (fun arg' ->
                        MethodInvoke (recv, ml, list_set args i arg')
                    ) (perturbations classes methods arg)
                ) args)
            in
            from_recv @ from_args
    in
    here @ from_children

let max_perturbations_per_prototerm = 256

let with_method_body p k body' =
    Prog { p with cp_methods =
        List.mapi (fun j m ->
            if j = k then { m with me_body = body' } else m
        ) p.cp_methods }

let method_body_variants p ((k, me) : int * concrete_method) =
    List.to_seq (perturbations p.cp_classes p.cp_methods me.me_body)
    |> Seq.map (with_method_body p k)

let perturbed_programs p =
    match p.cp_main_opt with
    | None -> Seq.empty
    | Some (mt, mty) ->
        let main_variants =
            List.to_seq (perturbations p.cp_classes p.cp_methods mt)
            |> Seq.map (fun mt' -> Prog { p with cp_main_opt = Some (mt', mty) })
        in
        let body_variants =
            List.to_seq (List.mapi (fun k me -> (k, me)) p.cp_methods)
            |> Seq.concat_map (method_body_variants p)
        in
        Seq.append main_variants body_variants
        |> Seq.take max_perturbations_per_prototerm

let techniques = [
    (fun _config s ->
        match s with
        | Expr _ -> Seq.empty
        | Prog p -> perturbed_programs (close_program p));
]
