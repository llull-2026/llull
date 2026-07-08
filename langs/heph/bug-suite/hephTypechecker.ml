open HephPrograms
module IntMap = Map.Make(Int)

let rec subst_typaram args = function
    | TyParam i ->
        (try List.nth args i
         with Failure _ | Invalid_argument _ -> TyParam i)
    | TyClass (cr, ts) -> TyClass (cr, List.map (subst_typaram args) ts)
    | TVar _ as t -> t
    | TyBot -> TyBot

let class_of classes cl =
    List.find_opt (fun ce -> ce.cc_label = cl) classes

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

let rec fields_of classes cr args =
    match cr with
    | Prelude _ -> []
    | Synth i ->
        (match class_of classes i with
         | None -> []
         | Some ce ->
             let (par_cr, par_args) = ce.cc_parent in
             let par_args' = List.map (subst_typaram args) par_args in
             let parent_fs = fields_of classes par_cr par_args' in
             let own = List.map (fun (fl, ft) ->
                 (fl, subst_typaram args ft)) ce.cc_fields in
             parent_fs @ own)

let prelude_method_sig = function
    | "Function", -1 -> Some ([TyParam 0], TyParam 1)
    | _ -> None

let rec lookup_method classes methods cr args ml =
    match cr with
    | Prelude n ->
        (match prelude_method_sig (n, ml) with
         | Some (ps, ret) ->
             Some (List.map (subst_typaram args) ps, subst_typaram args ret)
         | None ->
             match prelude_parent n with
             | None -> None
             | Some p -> lookup_method classes methods p [] ml)
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
                 lookup_method classes methods pcr pa' ml)

let rec type_equal a b =
    match a, b with
    | TyBot, TyBot -> true
    | TyClass (c1, a1), TyClass (c2, a2) ->
        c1 = c2 && List.length a1 = List.length a2 &&
        List.for_all2 type_equal a1 a2
    | TyParam i, TyParam j -> i = j
    | TVar i, TVar j -> i = j
    | _ -> false

let rec is_subtype classes sub sup =
    if type_equal sub sup then true
    else match sub, sup with
    | TyBot, _ -> true
    | _, TyBot -> false
    | TyClass (c1, a1), TyClass (c2, a2) ->
        if c1 = c2 then args_contained classes c1 a1 a2
        else
            (match parent_of classes c1 with
             | None -> false
             | Some (pcr, pargs) ->
                 let pargs' = List.map (subst_typaram a1) pargs in
                 is_subtype classes (TyClass (pcr, pargs')) sup)
    | TyParam i, TyParam j -> i = j
    | _ -> false

and args_contained classes cr a1 a2 =
    let vs = tparam_variances_of classes cr in
    List.length a1 = List.length a2 && List.length a1 = List.length vs &&
    List.for_all2 (fun (x, y) v ->
        match v with
        | Invariant -> type_equal x y
        | Covariant -> is_subtype classes x y
        | Contravariant -> is_subtype classes y x
    ) (List.combine a1 a2) vs

let tparam_bounds_of classes = function
    | Prelude _ -> []
    | Synth i ->
        (match class_of classes i with
         | Some ce -> List.map (fun tp -> tp.tp_bound) ce.cc_tparams
         | None -> [])

let rec type_bounds_ok classes ty =
    match ty with
    | TyClass (cr, args) ->
        List.for_all (type_bounds_ok classes) args
        && (match tparam_bounds_of classes cr with
            | [] -> true
            | bounds when List.length bounds = List.length args ->
                List.for_all2 (fun b a ->
                    is_subtype classes a (subst_typaram args b)) bounds args
            | _ -> true)
    | _ -> true

let class_bounds_ok classes ce =
    let (pcr, pargs) = ce.cc_parent in
    type_bounds_ok classes (TyClass (pcr, pargs))
    && List.for_all (fun (_, ft) -> type_bounds_ok classes ft) ce.cc_fields

let classtable_bounds_ok classes =
    List.for_all (class_bounds_ok classes) classes

type env = {
    free_env : heph_type IntMap.t;
    bound_env : heph_type list;
}

let empty_env = { free_env = IntMap.empty; bound_env = [] }

let push_bound ty env = { env with bound_env = ty :: env.bound_env }

let rec synth_type env classes methods = function
    | Var id -> IntMap.find_opt id env.free_env
    | BVar i ->
        (try Some (List.nth env.bound_env i)
         with Failure _ | Invalid_argument _ -> None)
    | New (ty, args) ->
        (match ty with
         | TyClass (cr, class_args) ->
             let expected_fields = fields_of classes cr class_args in
             if List.length args <> List.length expected_fields then None
             else
                 let arg_oks = List.map2 (fun (_, field_type) arg ->
                     match synth_type env classes methods arg with
                     | None -> None
                     | Some arg_ty ->
                         if is_subtype classes arg_ty field_type
                         then Some ()
                         else None
                 ) expected_fields args in
                 if List.for_all (fun r -> r <> None) arg_oks
                 then Some ty
                 else None
         | _ -> None)
    | FieldAccess (e, fl) ->
        (match synth_type env classes methods e with
         | Some (TyClass (cr, args)) ->
             let fs = fields_of classes cr args in
             List.assoc_opt fl fs
         | _ -> None)
    | MethodInvoke (e, ml, args) ->
        (match synth_type env classes methods e with
         | Some (TyClass (cr, class_args)) ->
             (match lookup_method classes methods cr class_args ml with
              | None -> None
              | Some (param_tys, ret) ->
                  if List.length args <> List.length param_tys then None
                  else
                      let arg_oks = List.map2 (fun pt arg ->
                          match synth_type env classes methods arg with
                          | None -> None
                          | Some a_ty ->
                              if is_subtype classes a_ty pt then Some ()
                              else None
                      ) param_tys args in
                      if List.for_all (fun r -> r <> None) arg_oks
                      then Some ret
                      else None)
         | _ -> None)
    | Lambda (param_ty, body) ->
        let env' = push_bound param_ty env in
        (match synth_type env' classes methods body with
         | None -> None
         | Some body_ty ->
             Some (TyClass (Prelude "Function", [param_ty; body_ty])))
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

let method_well_typed classes methods m =
    let this_type =
        let owner = Synth m.cm_class in
        match class_of classes m.cm_class with
        | None -> TyClass (owner, [])
        | Some ce ->
            let n = List.length ce.cc_tparams in
            TyClass (owner, List.init n (fun i -> TyParam i))
    in
    let env0 = { empty_env with
        free_env = IntMap.add m.cm_this_sym this_type empty_env.free_env } in
    let env = List.fold_left (fun e (sid, ty) ->
        { e with free_env = IntMap.add sid ty e.free_env }
    ) env0 m.cm_params in
    match synth_type env classes methods m.cm_body with
    | None -> false
    | Some body_ty -> is_subtype classes body_ty m.cm_return

let check (fact : tagged_fact) : bool =
    let classes = fact.tf_classes in
    let methods = fact.tf_methods in
    let env = { empty_env with
        free_env = List.fold_left (fun m (sid, ty) ->
            IntMap.add sid ty m) IntMap.empty fact.tf_bindings } in
    classtable_bounds_ok classes
    && List.for_all (method_well_typed classes methods) methods
    && (match synth_type env classes methods fact.tf_main_term with
        | None -> false
        | Some ty -> is_subtype classes ty fact.tf_main_type)

let string_of_fact (fact : tagged_fact) = fact.tf_rendered
