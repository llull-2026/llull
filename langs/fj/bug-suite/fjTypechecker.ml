module L = FjPrograms
module IntMap = Map.Make(Int)

let class_of classes cl =
    List.find_opt (fun ce -> ce.L.cc_label = cl) classes

let rec all_fields_of classes cl =
    if cl = -1 then [] else
    match class_of classes cl with
    | None -> []
    | Some ce ->
        all_fields_of classes ce.L.cc_parent @ ce.L.cc_own_fields

let rec lookup_method methods classes c ml =
    if c = -1 then None else
    match List.find_opt (fun m ->
        m.L.cm_class = c && m.L.cm_label = ml) methods with
    | Some m -> Some (List.map snd m.L.cm_params, m.L.cm_return)
    | None ->
        match class_of classes c with
        | None -> None
        | Some ce -> lookup_method methods classes ce.L.cc_parent ml

let rec is_subtype classes sub sup =
    if sub = sup then true else
    match sub with
    | L.ConcreteObject -> false
    | L.ConcreteClass c ->
        (match class_of classes c with
         | None -> false
         | Some ce ->
             if ce.L.cc_parent = -1 then sup = L.ConcreteObject else
             is_subtype classes (L.ConcreteClass ce.L.cc_parent) sup)

type env = L.concrete_type IntMap.t

let rec synth_type env classes methods = function
    | L.Var id -> IntMap.find_opt id env
    | L.New (-1, []) -> Some L.ConcreteObject
    | L.New (-1, _) -> None
    | L.New (c, args) ->
        let expected = all_fields_of classes c in
        if List.length args <> List.length expected then None else
        let ok = List.for_all2 (fun (_, ft) arg ->
            match synth_type env classes methods arg with
            | Some at -> is_subtype classes at ft
            | None -> false
        ) expected args in
        if ok then Some (L.ConcreteClass c) else None
    | L.FieldAccess (e, fl) ->
        (match synth_type env classes methods e with
         | Some (L.ConcreteClass c) ->
             List.assoc_opt fl (all_fields_of classes c)
         | _ -> None)
    | L.MethodInvoke (e, ml, args) ->
        (match synth_type env classes methods e with
         | Some (L.ConcreteClass c) ->
             (match lookup_method methods classes c ml with
              | None -> None
              | Some (param_tys, ret) ->
                  if List.length args <> List.length param_tys then None else
                  let ok = List.for_all2 (fun pt arg ->
                      match synth_type env classes methods arg with
                      | Some at -> is_subtype classes at pt
                      | None -> false
                  ) param_tys args in
                  if ok then Some ret else None)
         | _ -> None)

let method_well_typed classes methods m =
    let this_type = L.ConcreteClass m.L.cm_class in
    let env0 = IntMap.singleton m.L.cm_this_sym this_type in
    let env = List.fold_left (fun e (sid, ty) ->
        IntMap.add sid ty e) env0 m.L.cm_params in
    match synth_type env classes methods m.L.cm_body with
    | None -> false
    | Some body_ty -> is_subtype classes body_ty m.L.cm_return

let check (fact : L.tagged_fact) : bool =
    let classes = fact.L.tf_classes in
    let methods = fact.L.tf_methods in
    let env = List.fold_left (fun m (sid, ty) ->
        IntMap.add sid ty m) IntMap.empty fact.L.tf_bindings in
    List.for_all (method_well_typed classes methods) methods
    && (match synth_type env classes methods fact.L.tf_main_term with
        | None -> false
        | Some ty -> is_subtype classes ty fact.L.tf_main_type)

let string_of_fact (f : L.tagged_fact) = f.L.tf_rendered
