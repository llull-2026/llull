open HephPrograms
module IntMap = Map.Make(Int)

let rec subst_typaram args = function
    | TyParam i ->
        (try List.nth args i
         with Failure _ | Invalid_argument _ -> TyParam i)
    | TyClass (cr, ts) -> TyClass (cr, List.map (subst_typaram args) ts)
    | TVar _ as t -> t
    | TyBot -> TyBot

let class_of classes cl = List.find_opt (fun ce -> ce.cc_label = cl) classes

let prelude_parent = function
    | "Object" -> None
    | "Number" -> Some (Prelude "Object")
    | "Integer" -> Some (Prelude "Number")
    | "String" -> Some (Prelude "Object")
    | "Boolean" -> Some (Prelude "Object")
    | "Function" -> Some (Prelude "Object")
    | _ -> None

let parent_of classes = function
    | Prelude n -> (match prelude_parent n with Some p -> Some (p, []) | None -> None)
    | Synth i ->
        (match class_of classes i with
         | Some ce -> Some ce.cc_parent
         | None -> None)

let tparam_variances_of classes = function
    | Prelude "Function" -> [Contravariant; Covariant]
    | Prelude _ -> []
    | Synth i ->
        (match class_of classes i with
         | Some ce -> List.map (fun tp -> tp.tp_variance) ce.cc_tparams
         | None -> [])

let rec type_equal a b =
    match a, b with
    | TyBot, TyBot -> true
    | TyClass (c1, a1), TyClass (c2, a2) ->
        c1 = c2 && List.length a1 = List.length a2 &&
        List.for_all2 type_equal a1 a2
    | TyParam i, TyParam j -> i = j
    | TVar i, TVar j -> i = j
    | _ -> false

let rec is_subtype_bug1 classes sub sup =
    if type_equal sub sup then true
    else match sub, sup with
    | TyBot, _ -> true
    | _, TyBot -> false
    | TyClass (c1, a1), TyClass (c2, a2) ->
        if c1 = c2 then args_contained_bug1 classes c1 a1 a2
        else
            (match parent_of classes c1 with
             | None -> false
             | Some (pcr, pargs) ->
                 let pargs' = List.map (subst_typaram a1) pargs in
                 is_subtype_bug1 classes (TyClass (pcr, pargs')) sup)
    | TyParam i, TyParam j -> i = j
    | _ -> false

and args_contained_bug1 classes cr a1 a2 =
    let vs = tparam_variances_of classes cr in
    List.length a1 = List.length a2 && List.length a1 = List.length vs &&
    List.for_all2 (fun (x, y) v ->
        match v with
        | Invariant -> type_equal x y
        | Covariant -> is_subtype_bug1 classes x y
        | Contravariant -> is_subtype_bug1 classes x y
    ) (List.combine a1 a2) vs

let rec fields_of_bug2 classes cr _args =
    match cr with
    | Prelude _ -> []
    | Synth i ->
        (match class_of classes i with
         | None -> []
         | Some ce ->
             let (par_cr, _par_args) = ce.cc_parent in
             let parent_fs = fields_of_bug2 classes par_cr [] in
             let own = ce.cc_fields in
             parent_fs @ own)

let rec is_subtype_normal classes sub sup =
    if type_equal sub sup then true
    else match sub, sup with
    | TyBot, _ -> true
    | _, TyBot -> false
    | TyClass (c1, a1), TyClass (c2, a2) ->
        if c1 = c2 then args_contained_normal classes c1 a1 a2
        else
            (match parent_of classes c1 with
             | None -> false
             | Some (pcr, pargs) ->
                 let pargs' = List.map (subst_typaram a1) pargs in
                 is_subtype_normal classes (TyClass (pcr, pargs')) sup)
    | TyParam i, TyParam j -> i = j
    | _ -> false

and args_contained_normal classes cr a1 a2 =
    let vs = tparam_variances_of classes cr in
    List.length a1 = List.length a2 && List.length a1 = List.length vs &&
    List.for_all2 (fun (x, y) v ->
        match v with
        | Invariant -> type_equal x y
        | Covariant -> is_subtype_normal classes x y
        | Contravariant -> is_subtype_normal classes y x
    ) (List.combine a1 a2) vs

let rec lookup_method_bug3 classes methods cr _args ml =
    match cr with
    | Prelude _ ->
        let _ = classes in
        let _ = methods in
        let _ = ml in
        None
    | Synth i ->
        (match List.find_opt (fun m ->
            m.cm_class = i && m.cm_label = ml) methods with
         | Some m ->
             Some (List.map (fun (_, pt) -> pt) m.cm_params, m.cm_return)
         | None ->
             match class_of classes i with
             | None -> None
             | Some ce ->
                 let (pcr, _) = ce.cc_parent in
                 lookup_method_bug3 classes methods pcr [] ml)

type env = {
    free_env : heph_type IntMap.t;
    bound_env : heph_type list;
}

let empty_env = { free_env = IntMap.empty; bound_env = [] }
let push_bound ty env = { env with bound_env = ty :: env.bound_env }

let rec lookup_method_normal classes methods cr args ml =
    match cr with
    | Prelude n ->
        (match n, ml with
         | "Function", -1 ->
             Some ([subst_typaram args (TyParam 0)],
                   subst_typaram args (TyParam 1))
         | _ ->
             match prelude_parent n with
             | None -> None
             | Some p -> lookup_method_normal classes methods p [] ml)
    | Synth i ->
        (match List.find_opt (fun m ->
            m.cm_class = i && m.cm_label = ml) methods with
         | Some m ->
             Some (List.map (fun (_, pt) -> subst_typaram args pt) m.cm_params,
                   subst_typaram args m.cm_return)
         | None ->
             match class_of classes i with
             | None -> None
             | Some ce ->
                 let (pcr, pa) = ce.cc_parent in
                 let pa' = List.map (subst_typaram args) pa in
                 lookup_method_normal classes methods pcr pa' ml)

let rec fields_of_normal classes cr args =
    match cr with
    | Prelude _ -> []
    | Synth i ->
        (match class_of classes i with
         | None -> []
         | Some ce ->
             let (par_cr, par_args) = ce.cc_parent in
             let par_args' = List.map (subst_typaram args) par_args in
             let parent_fs = fields_of_normal classes par_cr par_args' in
             let own = List.map (fun (fl, ft) ->
                 (fl, subst_typaram args ft)) ce.cc_fields in
             parent_fs @ own)

let default_lambda_result pty bt =
    TyClass (Prelude "Function", [pty; bt])

let default_invk_result _pts ret = ret

let default_classtable_ok _classes = true

let make_check ~is_subtype ~fields_of ~lookup_method
               ?(lambda_result = default_lambda_result)
               ?(invk_result = default_invk_result)
               ?(classtable_ok = default_classtable_ok) () =
    let rec synth_type env classes methods = function
        | Var id -> IntMap.find_opt id env.free_env
        | BVar i ->
            (try Some (List.nth env.bound_env i)
             with Failure _ | Invalid_argument _ -> None)
        | New (ty, args) ->
            (match ty with
             | TyClass (cr, class_args) ->
                 let fs = fields_of classes cr class_args in
                 if List.length args <> List.length fs then None
                 else
                     let oks = List.map2 (fun (_, ft) a ->
                         match synth_type env classes methods a with
                         | None -> false
                         | Some at -> is_subtype classes at ft
                     ) fs args in
                     if List.for_all (fun b -> b) oks then Some ty else None
             | _ -> None)
        | FieldAccess (e, fl) ->
            (match synth_type env classes methods e with
             | Some (TyClass (cr, args)) ->
                 List.assoc_opt fl (fields_of classes cr args)
             | _ -> None)
        | MethodInvoke (e, ml, args) ->
            (match synth_type env classes methods e with
             | Some (TyClass (cr, class_args)) ->
                 (match lookup_method classes methods cr class_args ml with
                  | None -> None
                  | Some (pts, ret) ->
                      if List.length args <> List.length pts then None
                      else
                          let oks = List.map2 (fun pt a ->
                              match synth_type env classes methods a with
                              | None -> false
                              | Some at -> is_subtype classes at pt
                          ) pts args in
                          if List.for_all (fun b -> b) oks
                          then Some (invk_result pts ret)
                          else None)
             | _ -> None)
        | Lambda (pty, body) ->
            let env' = push_bound pty env in
            (match synth_type env' classes methods body with
             | None -> None
             | Some bt -> Some (lambda_result pty bt))
        | If (result_ty, c, t, e) ->
            (match synth_type env classes methods c,
                   synth_type env classes methods t,
                   synth_type env classes methods e with
             | Some ct, Some tt, Some et ->
                 if is_subtype classes ct (TyClass (Prelude "Boolean", []))
                    && is_subtype classes tt result_ty
                    && is_subtype classes et result_ty
                 then Some result_ty else None
             | _ -> None)
    in
    fun (fact : tagged_fact) ->
        let classes = fact.tf_classes in
        let methods = fact.tf_methods in
        let env = { empty_env with
            free_env = List.fold_left (fun m (sid, ty) ->
                IntMap.add sid ty m) IntMap.empty fact.tf_bindings } in
        classtable_ok classes
        && (match synth_type env classes methods fact.tf_main_term with
            | None -> false
            | Some ty -> is_subtype classes ty fact.tf_main_type)

let check_bug1 = make_check
    ~is_subtype:is_subtype_bug1
    ~fields_of:fields_of_normal
    ~lookup_method:lookup_method_normal ()

let check_bug2 = make_check
    ~is_subtype:is_subtype_normal
    ~fields_of:fields_of_bug2
    ~lookup_method:lookup_method_normal ()

let check_bug3 = make_check
    ~is_subtype:is_subtype_normal
    ~fields_of:fields_of_normal
    ~lookup_method:lookup_method_bug3 ()

let fields_of_bug4 classes cr args =
    match cr with
    | Prelude _ -> []
    | Synth i ->
        (match class_of classes i with
         | None -> []
         | Some ce ->
             List.map (fun (fl, ft) ->
                 (fl, subst_typaram args ft)) ce.cc_fields)

let check_bug4 = make_check
    ~is_subtype:is_subtype_normal
    ~fields_of:fields_of_bug4
    ~lookup_method:lookup_method_normal ()

let rec lookup_method_bug5 classes methods cr args ml =
    match cr with
    | Prelude n ->
        (match n, ml with
         | "Function", -1 ->
             Some ([subst_typaram args (TyParam 0)],
                   subst_typaram args (TyParam 1))
         | _ ->
             match prelude_parent n with
             | None -> None
             | Some p -> lookup_method_bug5 classes methods p [] ml)
    | Synth i ->
        (match List.find_opt (fun m ->
            m.cm_class = i && m.cm_label = ml) methods with
         | Some m ->
             Some (List.map (fun (_, pt) -> subst_typaram args pt) m.cm_params,
                   subst_typaram args m.cm_return)
         | None -> None)

let check_bug5 = make_check
    ~is_subtype:is_subtype_normal
    ~fields_of:fields_of_normal
    ~lookup_method:lookup_method_bug5 ()

let rec is_subtype_bug6 classes sub sup =
    if type_equal sub sup then true
    else match sub, sup with
    | TyBot, _ -> true
    | _, TyBot -> false
    | TyClass (c1, a1), TyClass (c2, a2) when c1 = c2 ->
        args_contained_bug6 classes c1 a1 a2
    | TyParam i, TyParam j -> i = j
    | _ -> false

and args_contained_bug6 classes cr a1 a2 =
    let vs = tparam_variances_of classes cr in
    List.length a1 = List.length a2 && List.length a1 = List.length vs &&
    List.for_all2 (fun (x, y) v ->
        match v with
        | Invariant -> type_equal x y
        | Covariant -> is_subtype_bug6 classes x y
        | Contravariant -> is_subtype_bug6 classes y x
    ) (List.combine a1 a2) vs

let check_bug6 = make_check
    ~is_subtype:is_subtype_bug6
    ~fields_of:fields_of_normal
    ~lookup_method:lookup_method_normal ()

let is_subtype_bug7 _classes = type_equal

let check_bug7 = make_check
    ~is_subtype:is_subtype_bug7
    ~fields_of:fields_of_normal
    ~lookup_method:lookup_method_normal ()

let lambda_result_bug8 pty bt = TyClass (Prelude "Function", [bt; pty])

let check_bug8 = make_check
    ~is_subtype:is_subtype_normal
    ~fields_of:fields_of_normal
    ~lookup_method:lookup_method_normal
    ~lambda_result:lambda_result_bug8 ()

let invk_result_bug9 pts ret =
    match pts with
    | [] -> ret
    | first :: _ -> first

let check_bug9 = make_check
    ~is_subtype:is_subtype_normal
    ~fields_of:fields_of_normal
    ~lookup_method:lookup_method_normal
    ~invk_result:invk_result_bug9 ()

let rec subst_typaram_bug10 args = function
    | TyParam i ->
        (try List.nth args (i + 1)
         with Failure _ | Invalid_argument _ -> TyParam i)
    | TyClass (cr, ts) -> TyClass (cr, List.map (subst_typaram_bug10 args) ts)
    | TVar _ as t -> t
    | TyBot -> TyBot

let rec fields_of_bug10 classes cr args =
    match cr with
    | Prelude _ -> []
    | Synth i ->
        (match class_of classes i with
         | None -> []
         | Some ce ->
             let (par_cr, par_args) = ce.cc_parent in
             let par_args' = List.map (subst_typaram_bug10 args) par_args in
             let parent_fs = fields_of_bug10 classes par_cr par_args' in
             let own = List.map (fun (fl, ft) ->
                 (fl, subst_typaram_bug10 args ft)) ce.cc_fields in
             parent_fs @ own)

let rec lookup_method_bug10 classes methods cr args ml =
    match cr with
    | Prelude n ->
        (match n, ml with
         | "Function", -1 ->
             Some ([subst_typaram_bug10 args (TyParam 0)],
                   subst_typaram_bug10 args (TyParam 1))
         | _ ->
             match prelude_parent n with
             | None -> None
             | Some p -> lookup_method_bug10 classes methods p [] ml)
    | Synth i ->
        (match List.find_opt (fun m ->
            m.cm_class = i && m.cm_label = ml) methods with
         | Some m ->
             Some (List.map (fun (_, pt) -> subst_typaram_bug10 args pt) m.cm_params,
                   subst_typaram_bug10 args m.cm_return)
         | None ->
             match class_of classes i with
             | None -> None
             | Some ce ->
                 let (pcr, pa) = ce.cc_parent in
                 let pa' = List.map (subst_typaram_bug10 args) pa in
                 lookup_method_bug10 classes methods pcr pa' ml)

let check_bug10 = make_check
    ~is_subtype:is_subtype_normal
    ~fields_of:fields_of_bug10
    ~lookup_method:lookup_method_bug10 ()

let rec lookup_method_bug11 classes methods cr args ml =
    match cr with
    | Prelude n ->
        (match n, ml with
         | "Function", -1 ->
             Some ([subst_typaram args (TyParam 0)],
                   subst_typaram args (TyParam 1))
         | _ ->
             match prelude_parent n with
             | None -> None
             | Some p -> lookup_method_bug11 classes methods p [] ml)
    | Synth i ->
        (match List.find_opt (fun m ->
            m.cm_class = i && m.cm_label = ml) methods with
         | Some m ->
             Some (List.map (fun (_, pt) -> subst_typaram args pt) m.cm_params,
                   subst_typaram args m.cm_return)
         | None ->
             match class_of classes i with
             | None -> None
             | Some ce ->
                 let (pcr, pa) = ce.cc_parent in
                 let pa' = match pcr with
                     | Prelude _ -> pa
                     | Synth _ -> List.map (subst_typaram args) pa
                 in
                 lookup_method_bug11 classes methods pcr pa' ml)

let check_bug11 = make_check
    ~is_subtype:is_subtype_normal
    ~fields_of:fields_of_normal
    ~lookup_method:lookup_method_bug11 ()

let rec is_subtype_bug12 classes sub sup =
    if type_equal sub sup then true
    else match sub, sup with
    | TyBot, _ -> true
    | _, TyBot -> false
    | TyClass (c1, a1), TyClass (c2, a2) ->
        if c1 = c2 then args_contained_bug12 classes c1 a1 a2
        else
            (match parent_of classes c1 with
             | None -> false
             | Some (pcr, pargs) ->
                 let pargs' = match pcr with
                     | Synth _ -> pargs
                     | Prelude _ -> List.map (subst_typaram a1) pargs
                 in
                 is_subtype_bug12 classes (TyClass (pcr, pargs')) sup)
    | TyParam i, TyParam j -> i = j
    | _ -> false

and args_contained_bug12 classes cr a1 a2 =
    let vs = tparam_variances_of classes cr in
    List.length a1 = List.length a2 && List.length a1 = List.length vs &&
    List.for_all2 (fun (x, y) v ->
        match v with
        | Invariant -> type_equal x y
        | Covariant -> is_subtype_bug12 classes x y
        | Contravariant -> is_subtype_bug12 classes y x
    ) (List.combine a1 a2) vs

let check_bug12 = make_check
    ~is_subtype:is_subtype_bug12
    ~fields_of:fields_of_normal
    ~lookup_method:lookup_method_normal ()

let rec lookup_method_bug13 classes methods cr args ml =
    match cr with
    | Prelude n ->
        (match n, ml with
         | "Function", -1 ->
             Some ([subst_typaram args (TyParam 0)],
                   subst_typaram args (TyParam 1))
         | _ ->
             match prelude_parent n with
             | None -> None
             | Some p -> lookup_method_bug13 classes methods p [] ml)
    | Synth i ->
        (match List.find_opt (fun m ->
            m.cm_class = i && m.cm_label = ml) methods with
         | Some m ->
             Some (List.map (fun (_, pt) -> subst_typaram args pt) m.cm_params,
                   subst_typaram args m.cm_return)
         | None ->
             match class_of classes i with
             | None -> None
             | Some ce ->
                 let (pcr, _pa) = ce.cc_parent in
                 lookup_method_bug13 classes methods pcr args ml)

let check_bug13 = make_check
    ~is_subtype:is_subtype_normal
    ~fields_of:fields_of_normal
    ~lookup_method:lookup_method_bug13 ()

let rec is_subtype_bug14 classes sub sup =
    if type_equal sub sup then true
    else match sub, sup with
    | TyBot, _ -> true
    | _, TyBot -> false
    | TyClass (c1, a1), TyClass (c2, a2) ->
        if c1 = c2 then args_contained_bug14 classes c1 a1 a2
        else
            (match parent_of classes c1 with
             | None -> false
             | Some (pcr, pargs) ->
                 let pargs' = match pcr with
                     | Prelude _ -> pargs
                     | Synth _   -> List.map (subst_typaram a1) pargs
                 in
                 is_subtype_bug14 classes (TyClass (pcr, pargs')) sup)
    | TyParam i, TyParam j -> i = j
    | _ -> false

and args_contained_bug14 classes cr a1 a2 =
    let vs = tparam_variances_of classes cr in
    List.length a1 = List.length a2 && List.length a1 = List.length vs &&
    List.for_all2 (fun (x, y) v ->
        match v with
        | Invariant -> type_equal x y
        | Covariant -> is_subtype_bug14 classes x y
        | Contravariant -> is_subtype_bug14 classes y x
    ) (List.combine a1 a2) vs

let check_bug14 = make_check
    ~is_subtype:is_subtype_bug14
    ~fields_of:fields_of_normal
    ~lookup_method:lookup_method_normal ()

let tparam_variances_bug15 classes = function
    | Prelude "Function" -> [Contravariant; Covariant]
    | Prelude _ -> []
    | Synth i ->
        (match class_of classes i with
         | Some ce -> List.map (fun _ -> Invariant) ce.cc_tparams
         | None -> [])

let rec is_subtype_bug15 classes sub sup =
    if type_equal sub sup then true
    else match sub, sup with
    | TyBot, _ -> true
    | _, TyBot -> false
    | TyClass (c1, a1), TyClass (c2, a2) ->
        if c1 = c2 then args_contained_bug15 classes c1 a1 a2
        else
            (match parent_of classes c1 with
             | None -> false
             | Some (pcr, pargs) ->
                 let pargs' = List.map (subst_typaram a1) pargs in
                 is_subtype_bug15 classes (TyClass (pcr, pargs')) sup)
    | TyParam i, TyParam j -> i = j
    | _ -> false

and args_contained_bug15 classes cr a1 a2 =
    let vs = tparam_variances_bug15 classes cr in
    List.length a1 = List.length a2 && List.length a1 = List.length vs &&
    List.for_all2 (fun (x, y) v ->
        match v with
        | Invariant -> type_equal x y
        | Covariant -> is_subtype_bug15 classes x y
        | Contravariant -> is_subtype_bug15 classes y x
    ) (List.combine a1 a2) vs

let check_bug15 = make_check
    ~is_subtype:is_subtype_bug15
    ~fields_of:fields_of_normal
    ~lookup_method:lookup_method_normal ()

let lambda_result_bug16 pty bt =
    match bt with
    | TyClass (Prelude "Function", _) ->
        TyClass (Prelude "Function", [bt; pty])
    | _ ->
        TyClass (Prelude "Function", [pty; bt])

let check_bug16 = make_check
    ~is_subtype:is_subtype_normal
    ~fields_of:fields_of_normal
    ~lookup_method:lookup_method_normal
    ~lambda_result:lambda_result_bug16 ()

let rec is_subtype_bug17 classes sub sup =
    if type_equal sub sup then true
    else match sub, sup with
    | TyBot, _ -> true
    | _, TyBot -> false
    | TyClass (c1, a1), TyClass (c2, a2) ->
        if c1 = c2 then args_contained_bug17 classes c1 a1 a2
        else
            (match parent_of classes c1 with
             | None -> false
             | Some (pcr, pargs) ->
                 let pargs' = List.map (subst_typaram a1) pargs in
                 is_subtype_bug17 classes (TyClass (pcr, pargs')) sup)
    | TyParam i, TyParam j -> i = j
    | _ -> false

and args_contained_bug17 classes cr a1 a2 =
    let vs = tparam_variances_of classes cr in
    List.length a1 = List.length a2 && List.length a1 = List.length vs &&
    List.for_all2 (fun (x, y) v ->
        match v with
        | Invariant -> type_equal x y
        | Covariant -> type_equal x y
        | Contravariant -> is_subtype_bug17 classes y x
    ) (List.combine a1 a2) vs

let check_bug17 = make_check
    ~is_subtype:is_subtype_bug17
    ~fields_of:fields_of_normal
    ~lookup_method:lookup_method_normal ()

let rec lookup_method_bug18 classes methods cr _args ml =
    match cr with
    | Prelude n ->
        (match n, ml with
         | "Function", -1 -> Some ([TyParam 0], TyParam 1)
         | _ ->
             match prelude_parent n with
             | None -> None
             | Some p -> lookup_method_bug18 classes methods p [] ml)
    | Synth i ->
        (match List.find_opt (fun m ->
            m.cm_class = i && m.cm_label = ml) methods with
         | Some m ->
             Some (List.map (fun (_, pt) -> pt) m.cm_params, m.cm_return)
         | None ->
             match class_of classes i with
             | None -> None
             | Some ce ->
                 let (pcr, _pa) = ce.cc_parent in
                 lookup_method_bug18 classes methods pcr [] ml)

let check_bug18 = make_check
    ~is_subtype:is_subtype_normal
    ~fields_of:fields_of_normal
    ~lookup_method:lookup_method_bug18 ()

let bound_mentions_typaram = function
    | TyParam _ -> true
    | TyClass (_, args) -> List.exists (function TyParam _ -> true | _ -> false) args
    | _ -> false

let classtable_ok_bug19 classes =
    List.for_all (fun ce ->
        List.for_all (fun tp -> not (bound_mentions_typaram tp.tp_bound))
            ce.cc_tparams
    ) classes

let check_bug19 = make_check
    ~is_subtype:is_subtype_normal
    ~fields_of:fields_of_normal
    ~lookup_method:lookup_method_normal
    ~classtable_ok:classtable_ok_bug19 ()

let bugs = [
    ("variance-flip", "heph-program", 1, `Medium,
     "args_contained uses covariant rule for contravariant slot",
     `Accept, check_bug1);
    ("subst-drop", "heph-program", 2, `Medium,
     "fields_of throws away parent args when walking inheritance",
     `Accept, check_bug2);
    ("prelude-method-miss", "heph-program", 3, `Shallow,
     "lookup_method returns None on prelude classes, losing Function.apply",
     `Accept, check_bug3);
    ("fields-no-inheritance", "heph-program", 4, `Medium,
     "fields_of drops the parent chain; inherited fields invisible",
     `Accept, check_bug4);
    ("lookup-no-inheritance", "heph-program", 5, `Medium,
     "lookup_method drops the parent chain; inherited methods invisible",
     `Accept, check_bug5);
    ("subtype-no-parent-walk", "heph-program", 6, `Medium,
     "is_subtype never walks the parent chain across class labels",
     `Accept, check_bug6);
    ("subtype-equality-only", "heph-program", 7, `Deep,
     "is_subtype collapses to type equality; no subtyping at all",
     `Accept, check_bug7);
    ("lambda-arrow-reversed", "heph-program", 8, `Shallow,
     "Lambda is typed Function<body, param> instead of Function<param, body>",
     `Accept, check_bug8);
    ("invk-returns-first-param", "heph-program", 9, `Shallow,
     "MethodInvoke synthesises the first param type instead of the declared return",
     `Accept, check_bug9);
    ("subst-off-by-one", "heph-program", 10, `Medium,
     "subst_typaram indexes args with i+1 instead of i",
     `Accept, check_bug10);
    ("lookup-prelude-boundary-subst-drop", "heph-program", 11, `Deep,
     "lookup_method skips subst only at the Synth\xe2\x86\x92Prelude hop",
     `Accept, check_bug11);
    ("subtype-synth-parent-subst-drop", "heph-program", 12, `Deep,
     "is_subtype parent walk skips subst only for Synth\xe2\x86\x92Synth hops",
     `Accept, check_bug12);
    ("lookup-parent-reuses-receiver-args", "heph-program", 13, `Deep,
     "lookup_method Synth\xe2\x86\x92Synth hop passes receiver args raw, without subst into parent's declared args",
     `Accept, check_bug13);
    ("subtype-prelude-parent-subst-drop", "heph-program", 14, `Deep,
     "is_subtype parent walk skips subst only for Synth\xe2\x86\x92Prelude hops",
     `Accept, check_bug14);
    ("synth-variance-ignored", "heph-program", 15, `Medium,
     "tparam_variances_of treats every Synth-class tparam as Invariant; Function's variances remain correct",
     `Accept, check_bug15);
    ("nested-lambda-flipped", "heph-program", 16, `Deep,
     "Lambda result swaps param/body types iff body is a Function type",
     `Accept, check_bug16);
    ("covariant-arg-as-invariant", "heph-program", 17, `Medium,
     "args_contained uses the invariant (equality) rule for a covariant slot (GROOVY-10082, GROOVY-10091)",
     `Accept, check_bug17);
    ("lookup-method-raw-subst", "heph-program", 18, `Medium,
     "lookup_method returns inherited/generic method signatures without type-argument substitution (GROOVY-9945)",
     `Accept, check_bug18);
    ("typaram-bound-cycle", "heph-program", 19, `Medium,
     "spurious cycle/error on a type parameter bounded by another (or the same) type parameter (GROOVY-10125, GROOVY-10115, GROOVY-10113)",
     `Accept, check_bug19);
]
