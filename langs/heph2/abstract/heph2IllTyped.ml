open HephPrograms
open Heph2Prototerms
open Heph2Concretization

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

let object_new = New (object_ty, [])

let rec map_first f t =
    match f t with
    | Some t' -> Some t'
    | None ->
        match t with
        | Var _ | BVar _ -> None
        | New (ty, args) ->
            Option.map (fun a -> New (ty, a)) (map_first_list f args)
        | FieldAccess (e, fl) ->
            Option.map (fun e' -> FieldAccess (e', fl)) (map_first f e)
        | MethodInvoke (e, ml, args) ->
            (match map_first f e with
             | Some e' -> Some (MethodInvoke (e', ml, args))
             | None -> Option.map (fun a -> MethodInvoke (e, ml, a)) (map_first_list f args))
        | Lambda (ty, b) -> Option.map (fun b' -> Lambda (ty, b')) (map_first f b)
        | If (ty, c, x, y) ->
            (match map_first f c with
             | Some c' -> Some (If (ty, c', x, y))
             | None -> match map_first f x with
                 | Some x' -> Some (If (ty, c, x', y))
                 | None -> Option.map (fun y' -> If (ty, c, x, y')) (map_first f y))
and map_first_list f = function
    | [] -> None
    | x :: xs ->
        (match map_first f x with
         | Some x' -> Some (x' :: xs)
         | None -> Option.map (fun xs' -> x :: xs') (map_first_list f xs))

let break_arity = function New (ty, a) -> Some (New (ty, a @ [object_new])) | _ -> None

let apply_mut mut (f : tagged_fact) =
    match map_first mut f.tf_main_term with
    | None -> None
    | Some t' ->
        let f' = { f with tf_main_term = t'; tf_main_type = object_ty } in
        Some { f' with tf_rendered = rerender_main f' }

let fresh_sym (f : tagged_fact) =
    List.fold_left (fun a (s, _) -> max a s) (-1) f.tf_bindings + 1

let mut_field recv = function FieldAccess (_, fl) -> Some (FieldAccess (recv, fl)) | _ -> None
let mut_invk recv = function MethodInvoke (_, ml, a) -> Some (MethodInvoke (recv, ml, a)) | _ -> None

let apply_recv_mut mk (f : tagged_fact) =
    let sym = fresh_sym f in
    match map_first (mk (Var sym)) f.tf_main_term with
    | None -> None
    | Some t' ->
        let f' = { f with tf_main_term = t'; tf_main_type = object_ty;
                          tf_bindings = (sym, TyBot) :: f.tf_bindings } in
        Some { f' with tf_rendered = rerender_main f' }

let is_object_ty = function TyClass (Prelude "Object", []) -> true | _ -> false

let fresh_fl (f : tagged_fact) =
    1 + List.fold_left (fun a ce ->
        List.fold_left (fun a (fl, _) -> max a fl) a ce.cc_fields) (-1) f.tf_classes

let fresh_ml (f : tagged_fact) =
    1 + List.fold_left (fun a m -> max a m.cm_label) (-1) f.tf_methods

let mutate_new_nonclass (f : tagged_fact) =
    match f.tf_main_term with
    | New (TyClass _, args) ->
        let f' = { f with tf_main_term = New (TyParam 0, args);
                          tf_main_type = TyParam 0 } in
        Some { f' with tf_rendered = rerender_main f' }
    | _ -> None

let mut_field_label fl = function
    | FieldAccess (e, _) -> Some (FieldAccess (e, fl)) | _ -> None
let mut_invk_label ml = function
    | MethodInvoke (e, _, a) -> Some (MethodInvoke (e, ml, a)) | _ -> None
let mut_invk_arity = function
    | MethodInvoke (e, ml, a) -> Some (MethodInvoke (e, ml, a @ [object_new])) | _ -> None
let mut_lambda_body sym = function
    | Lambda (ty, _) -> Some (Lambda (ty, Var sym)) | _ -> None

let rec replace_arg expected args sym =
    match expected, args with
    | ft :: es, a :: rest ->
        if not (is_object_ty ft) then Some (Var sym :: rest)
        else Option.map (fun r -> a :: r) (replace_arg es rest sym)
    | _ -> None

let rec recv_class_type (f : tagged_fact) = function
    | New (TyClass (cr, args), _) -> Some (cr, args)
    | Var id ->
        (match List.assoc_opt id f.tf_bindings with
         | Some (TyClass (cr, args)) -> Some (cr, args) | _ -> None)
    | FieldAccess (e, fl) ->
        (match recv_class_type f e with
         | Some (cr, args) ->
             (match List.assoc_opt fl (HephTypechecker.fields_of f.tf_classes cr args) with
              | Some (TyClass (cr', args')) -> Some (cr', args') | _ -> None)
         | None -> None)
    | MethodInvoke (e, ml, _) ->
        (match recv_class_type f e with
         | Some (cr, args) ->
             (match HephTypechecker.lookup_method f.tf_classes f.tf_methods cr args ml with
              | Some (_, TyClass (cr', args')) -> Some (cr', args') | _ -> None)
         | None -> None)
    | _ -> None

let new_argsub (f : tagged_fact) sym = function
    | New (TyClass (cr, cargs) as ty, args) ->
        let expected = List.map snd (HephTypechecker.fields_of f.tf_classes cr cargs) in
        Option.map (fun a' -> New (ty, a')) (replace_arg expected args sym)
    | _ -> None

let invk_argsub (f : tagged_fact) sym = function
    | MethodInvoke (recv, ml, args) ->
        (match recv_class_type f recv with
         | Some (cr, cargs) ->
             (match HephTypechecker.lookup_method f.tf_classes f.tf_methods cr cargs ml with
              | Some (param_tys, _) ->
                  Option.map (fun a' -> MethodInvoke (recv, ml, a'))
                      (replace_arg param_tys args sym)
              | None -> None)
         | None -> None)
    | _ -> None

let apply_argsub_mut mk (f : tagged_fact) =
    let sym = fresh_sym f in
    match map_first (mk f sym) f.tf_main_term with
    | None -> None
    | Some t' ->
        let f' = { f with tf_main_term = t'; tf_main_type = object_ty;
                          tf_bindings = (sym, object_ty) :: f.tf_bindings } in
        Some { f' with tf_rendered = rerender_main f' }

let structural_mutations (f : tagged_fact) : tagged_fact list =
    List.filter_map (fun m -> m f) [
        mutate_new_nonclass;
        apply_recv_mut mut_field;
        apply_recv_mut mut_invk;
        apply_mut break_arity;
        (fun f -> apply_mut (mut_field_label (fresh_fl f)) f);
        (fun f -> apply_mut (mut_invk_label (fresh_ml f)) f);
        apply_mut mut_invk_arity;
        (fun f -> apply_mut (mut_lambda_body (fresh_sym f)) f);
        apply_argsub_mut new_argsub;
        apply_argsub_mut invk_argsub;
    ]

let all_main_mutations (f : tagged_fact) : tagged_fact Seq.t =
    List.to_seq
        (mutate_unbound_var f :: mutate_bvar_oob f :: structural_mutations f)

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

let mutate_witnesses = 4

let ground_fault ~search_budget config p fault : tagged_fact Seq.t =
    match fault with
    | BreakDemand _ ->
        instantiate_program_violating config p
    | MutateMain ->
        Seq.concat_map all_main_mutations
            (Seq.take mutate_witnesses (instantiate_program ~search_budget config p))
    | AddBoundViolation ce ->
        instantiate_program ~search_budget config { p with classes = ce :: p.classes }

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

let bound_violation_technique (config : config) s =
    match s with
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
    (fun (config : config) s ->
        match s with
        | ProgramProtoTerm p
          when IntSet.cardinal (tvars_in_program p) <= config.max_tvars ->
            List.to_seq [FaultedProgram (p, BreakDemand []);
                         FaultedProgram (p, MutateMain)]
        | _ -> Seq.empty);
]
