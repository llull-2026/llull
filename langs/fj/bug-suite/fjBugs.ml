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

let rec is_subtype_bug1 classes sub sup =
    match sub with
    | L.ConcreteObject -> sup = L.ConcreteObject
    | L.ConcreteClass c ->
        (match class_of classes c with
         | None -> false
         | Some ce ->
             if ce.L.cc_parent = -1 then sup = L.ConcreteObject else
             is_subtype_bug1 classes (L.ConcreteClass ce.L.cc_parent) sup)

let rec is_subtype_bug2 classes sub sup =
    if sub = sup then true else
    match sub with
    | L.ConcreteObject -> false
    | L.ConcreteClass c ->
        (match class_of classes c with
         | None -> false
         | Some ce ->
             if ce.L.cc_parent = -1 then false else
             is_subtype_bug2 classes (L.ConcreteClass ce.L.cc_parent) sup)

let all_fields_bug3 classes cl =
    match class_of classes cl with
    | None -> []
    | Some ce -> ce.L.cc_own_fields

let lookup_method_bug4 methods _classes c ml =
    if c = -1 then None else
    match List.find_opt (fun m ->
        m.L.cm_class = c && m.L.cm_label = ml) methods with
    | Some m -> Some (List.map snd m.L.cm_params, m.L.cm_return)
    | None -> None

type helpers = {
    is_subtype : L.concrete_type -> L.concrete_type -> bool;
    all_fields : int -> (int * L.concrete_type) list;
    lookup_method : int -> int -> (L.concrete_type list * L.concrete_type) option;
    check_new_arg : L.concrete_type -> L.concrete_type -> bool;
    check_invk_arg : L.concrete_type -> L.concrete_type -> bool;
    pair_new : (int * L.concrete_type) list -> 'a list -> ((int * L.concrete_type) * 'a) list option;
} constraint 'a = L.term

let rec synth_type_with (h : helpers) env methods = function
    | L.Var id -> IntMap.find_opt id env
    | L.New (-1, []) -> Some L.ConcreteObject
    | L.New (-1, _) -> None
    | L.New (c, args) ->
        let expected = h.all_fields c in
        (match h.pair_new expected args with
         | None -> None
         | Some pairs ->
             let ok = List.for_all (fun ((_, ft), arg) ->
                 match synth_type_with h env methods arg with
                 | Some at -> h.check_new_arg at ft
                 | None -> false
             ) pairs in
             if ok then Some (L.ConcreteClass c) else None)
    | L.FieldAccess (e, fl) ->
        (match synth_type_with h env methods e with
         | Some (L.ConcreteClass c) -> List.assoc_opt fl (h.all_fields c)
         | _ -> None)
    | L.MethodInvoke (e, ml, args) ->
        (match synth_type_with h env methods e with
         | Some (L.ConcreteClass c) ->
             (match h.lookup_method c ml with
              | None -> None
              | Some (param_tys, ret) ->
                  if List.length args <> List.length param_tys then None else
                  let ok = List.for_all2 (fun pt arg ->
                      match synth_type_with h env methods arg with
                      | Some at -> h.check_invk_arg at pt
                      | None -> false
                  ) param_tys args in
                  if ok then Some ret else None)
         | _ -> None)

let pair_new_standard expected args =
    if List.length args <> List.length expected then None else
    Some (List.combine expected args)

let pair_new_reversed expected args =
    if List.length args <> List.length expected then None else
    Some (List.combine (List.rev expected) args)

let method_ok_with (h : helpers) classes methods m ~include_this ~contravariant_ret =
    let this_type = L.ConcreteClass m.L.cm_class in
    let env0 =
        if include_this then IntMap.singleton m.L.cm_this_sym this_type else
        IntMap.empty
    in
    let env = List.fold_left (fun e (sid, ty) ->
        IntMap.add sid ty e) env0 m.L.cm_params in
    let _ = classes in
    match synth_type_with h env methods m.L.cm_body with
    | None -> false
    | Some body_ty ->
        if contravariant_ret then h.is_subtype m.L.cm_return body_ty else
        h.is_subtype body_ty m.L.cm_return

let check_with (h : helpers) ~include_this ~contravariant_ret (fact : L.tagged_fact) =
    let classes = fact.L.tf_classes in
    let methods = fact.L.tf_methods in
    let env = List.fold_left (fun m (sid, ty) ->
        IntMap.add sid ty m) IntMap.empty fact.L.tf_bindings in
    List.for_all (method_ok_with h classes methods
                      ~include_this ~contravariant_ret) methods
    && (match synth_type_with h env methods fact.L.tf_main_term with
        | None -> false
        | Some ty -> h.is_subtype ty fact.L.tf_main_type)

let baseline_helpers classes methods = {
    is_subtype = is_subtype_bug1 classes;
    all_fields = all_fields_of classes;
    lookup_method = lookup_method methods classes;
    check_new_arg = (fun at ft -> at = ft);
    check_invk_arg = (fun at pt -> at = pt);
    pair_new = pair_new_standard;
}

let rec correct_subtype classes a b =
    if a = b then true else
    match a with
    | L.ConcreteObject -> false
    | L.ConcreteClass c -> (match class_of classes c with
        | None -> false | Some ce ->
            if ce.L.cc_parent = -1 then b = L.ConcreteObject else
            correct_subtype classes (L.ConcreteClass ce.L.cc_parent) b)

let check_bug1 fact =
    let classes = fact.L.tf_classes and methods = fact.L.tf_methods in
    let sub = is_subtype_bug1 classes in
    let h = { (baseline_helpers classes methods) with
        is_subtype = sub;
        check_new_arg = sub;
        check_invk_arg = sub; } in
    check_with h ~include_this:true ~contravariant_ret:false fact

let check_bug2 fact =
    let classes = fact.L.tf_classes and methods = fact.L.tf_methods in
    let sub = is_subtype_bug2 classes in
    let h = { (baseline_helpers classes methods) with
        is_subtype = sub;
        check_new_arg = sub;
        check_invk_arg = sub; } in
    check_with h ~include_this:true ~contravariant_ret:false fact

let check_bug3 fact =
    let classes = fact.L.tf_classes and methods = fact.L.tf_methods in
    let sub = correct_subtype classes in
    let h = { (baseline_helpers classes methods) with
        is_subtype = sub;
        all_fields = all_fields_bug3 classes;
        check_new_arg = sub;
        check_invk_arg = sub; } in
    check_with h ~include_this:true ~contravariant_ret:false fact

let check_bug4 fact =
    let classes = fact.L.tf_classes and methods = fact.L.tf_methods in
    let sub = correct_subtype classes in
    let h = { (baseline_helpers classes methods) with
        is_subtype = sub;
        lookup_method = lookup_method_bug4 methods classes;
        check_new_arg = sub;
        check_invk_arg = sub; } in
    check_with h ~include_this:true ~contravariant_ret:false fact

let check_bug5 fact =
    let classes = fact.L.tf_classes and methods = fact.L.tf_methods in
    let sub = correct_subtype classes in
    let h = { (baseline_helpers classes methods) with
        is_subtype = sub;
        check_new_arg = (fun a b -> a = b);
        check_invk_arg = sub; } in
    check_with h ~include_this:true ~contravariant_ret:false fact

let check_bug6 fact =
    let classes = fact.L.tf_classes and methods = fact.L.tf_methods in
    let sub = correct_subtype classes in
    let h = { (baseline_helpers classes methods) with
        is_subtype = sub;
        check_new_arg = sub;
        check_invk_arg = (fun a b -> a = b); } in
    check_with h ~include_this:true ~contravariant_ret:false fact

let check_bug7 fact =
    let classes = fact.L.tf_classes and methods = fact.L.tf_methods in
    let sub = correct_subtype classes in
    let h = { (baseline_helpers classes methods) with
        is_subtype = sub;
        check_new_arg = sub;
        check_invk_arg = sub;
        pair_new = pair_new_reversed; } in
    check_with h ~include_this:true ~contravariant_ret:false fact

let rec bug8_synth classes methods env = function
    | L.Var id -> IntMap.find_opt id env
    | L.New (-1, []) -> Some L.ConcreteObject
    | L.New (-1, _) -> None
    | L.New (c, args) ->
        let expected = all_fields_of classes c in
        if List.length args <> List.length expected then None else
        let ok = List.for_all2 (fun (_, ft) arg ->
            match bug8_synth classes methods env arg with
            | Some at -> correct_subtype classes at ft
            | None -> false
        ) expected args in
        if ok then Some (L.ConcreteClass c) else None
    | L.FieldAccess (e, fl) ->
        (match bug8_synth classes methods env e with
         | Some (L.ConcreteClass c) ->
             List.assoc_opt fl (all_fields_bug3 classes c)
         | _ -> None)
    | L.MethodInvoke (e, ml, args) ->
        (match bug8_synth classes methods env e with
         | Some (L.ConcreteClass c) ->
             (match lookup_method methods classes c ml with
              | None -> None
              | Some (param_tys, ret) ->
                  if List.length args <> List.length param_tys then None else
                  let ok = List.for_all2 (fun pt arg ->
                      match bug8_synth classes methods env arg with
                      | Some at -> correct_subtype classes at pt
                      | None -> false
                  ) param_tys args in
                  if ok then Some ret else None)
         | _ -> None)

let bug8_method_ok classes methods m =
    let this_type = L.ConcreteClass m.L.cm_class in
    let env0 = IntMap.singleton m.L.cm_this_sym this_type in
    let env = List.fold_left (fun e (sid, ty) ->
        IntMap.add sid ty e) env0 m.L.cm_params in
    match bug8_synth classes methods env m.L.cm_body with
    | None -> false
    | Some body_ty -> correct_subtype classes body_ty m.L.cm_return

let check_bug8 fact =
    let classes = fact.L.tf_classes and methods = fact.L.tf_methods in
    let env = List.fold_left (fun m (sid, ty) ->
        IntMap.add sid ty m) IntMap.empty fact.L.tf_bindings in
    List.for_all (bug8_method_ok classes methods) fact.L.tf_methods
    && (match bug8_synth classes methods env fact.L.tf_main_term with
        | None -> false
        | Some ty -> correct_subtype classes ty fact.L.tf_main_type)

let check_bug9 fact =
    let classes = fact.L.tf_classes and methods = fact.L.tf_methods in
    let sub = correct_subtype classes in
    let h = { (baseline_helpers classes methods) with
        is_subtype = sub;
        check_new_arg = sub;
        check_invk_arg = sub; } in
    check_with h ~include_this:false ~contravariant_ret:false fact

let check_bug10 fact =
    let classes = fact.L.tf_classes and methods = fact.L.tf_methods in
    let sub = correct_subtype classes in
    let h = { (baseline_helpers classes methods) with
        is_subtype = sub;
        check_new_arg = sub;
        check_invk_arg = sub; } in
    check_with h ~include_this:true ~contravariant_ret:true fact

let make name bug_id sev desc check =
    (name, "fj-program", bug_id, sev, desc, `Accept, check)

let bugs = [
    make "fjp-1" 1 `Shallow
        "is_subtype missing reflexivity shortcut" check_bug1;
    make "fjp-2" 2 `Shallow
        "is_subtype misses C <: Object (parent=-1 falls through)" check_bug2;
    make "fjp-3" 3 `Shallow
        "all_fields_of drops inherited fields" check_bug3;
    make "fjp-4" 4 `Shallow
        "lookup_method doesn't walk to parent" check_bug4;
    make "fjp-5" 5 `Medium
        "T-New requires arg type = field type (instead of <:)" check_bug5;
    make "fjp-6" 6 `Medium
        "T-Invk requires arg type = param type (instead of <:)" check_bug6;
    make "fjp-7" 7 `Shallow
        "T-New pairs args with fields in reverse" check_bug7;
    make "fjp-8" 8 `Shallow
        "T-Field bypasses inheritance chain" check_bug8;
    make "fjp-9" 9 `Medium
        "method body typing omits 'this' binding" check_bug9;
    make "fjp-10" 10 `Medium
        "method body return check is contravariant" check_bug10;
]
