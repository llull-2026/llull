open HephRwPrograms
module IntMap = Map.Make(Int)

let rec subst_typaram args = function
    | TyParam i ->
        (try List.nth args i
         with Failure _ | Invalid_argument _ -> TyParam i)
    | t -> map_type_children (subst_typaram args) t

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
    | Wild (v1, t1), Wild (v2, t2) -> v1 = v2 && type_equal t1 t2
    | MTParam i, MTParam j -> i = j
    | TyArray a, TyArray b -> type_equal a b
    | Hole i, Hole j -> i = j
    | _ -> false

let rec is_subtype ?(bounds=[]) classes sub sup =
    if type_equal sub sup then true
    else match sub, sup with
    | TyBot, _ -> true
    | _, TyBot -> false
    | TyClass (c1, a1), TyClass (c2, a2) ->
        if c1 = c2 then args_contained ~bounds classes c1 a1 a2
        else
            (match parent_of classes c1 with
             | None -> false
             | Some (pcr, pargs) ->
                 let pargs' = List.map (subst_typaram a1) pargs in
                 is_subtype ~bounds classes (TyClass (pcr, pargs')) sup)
    | TyParam i, TyParam j when i = j -> true
    | TyParam i, _ ->
        (match List.nth_opt bounds i with
         | Some b -> is_subtype ~bounds classes b sup
         | None -> false)
    | Wild (Covariant, b), _ -> is_subtype ~bounds classes b sup
    | Wild (_, _), _ -> is_subtype ~bounds classes (TyClass (Prelude "Object", [])) sup
    | MTParam i, MTParam j -> i = j
    | MTParam _, TyClass (Prelude "Object", []) -> true
    | TyArray a, TyArray b -> is_subtype ~bounds classes a b
    | _ -> false

and arg_contains ?(bounds=[]) classes v x y =
    match y with
    | Wild (Covariant, t) ->
        (match x with
         | Wild (Covariant, s) -> is_subtype ~bounds classes s t
         | Wild (Invariant, _) -> is_subtype ~bounds classes (TyClass (Prelude "Object", [])) t
         | Wild _ -> false
         | _ -> is_subtype ~bounds classes x t)
    | Wild (Contravariant, t) ->
        (match x with
         | Wild (Contravariant, s) -> is_subtype ~bounds classes t s
         | Wild _ -> false
         | _ -> is_subtype ~bounds classes t x)
    | Wild (Invariant, _) -> true
    | _ ->
        (match v with
         | Invariant -> type_equal x y
         | Covariant -> is_subtype ~bounds classes x y
         | Contravariant -> is_subtype ~bounds classes y x)

and args_contained ?(bounds=[]) classes cr a1 a2 =
    let vs = tparam_variances_of classes cr in
    List.length a1 = List.length a2 && List.length a1 = List.length vs &&
    List.for_all2 (fun (x, y) v -> arg_contains ~bounds classes v x y)
        (List.combine a1 a2) vs

let tparam_bounds_of classes = function
    | Prelude _ -> []
    | Synth i ->
        (match class_of classes i with
         | Some ce -> List.map (fun tp -> tp.tp_bound) ce.cc_tparams
         | None -> [])

let rec type_bounds_ok ?(bounds=[]) classes ty =
    match ty with
    | TyClass (cr, args) ->
        List.for_all (type_bounds_ok ~bounds classes) args
        && (match tparam_bounds_of classes cr with
            | [] -> true
            | tb when List.length tb = List.length args ->
                List.for_all2 (fun b a ->
                    is_subtype ~bounds classes a (subst_typaram args b)) tb args
            | _ -> true)
    | Wild (_, t) -> type_bounds_ok ~bounds classes t
    | TyArray t -> type_bounds_ok ~bounds classes t
    | _ -> true

let class_bounds_ok classes ce =
    let bounds = List.map (fun tp -> tp.tp_bound) ce.cc_tparams in
    let (pcr, pargs) = ce.cc_parent in
    type_bounds_ok ~bounds classes (TyClass (pcr, pargs))
    && List.for_all (fun (_, ft) -> type_bounds_ok ~bounds classes ft) ce.cc_fields

let classtable_bounds_ok classes =
    List.for_all (class_bounds_ok classes) classes

type env = {
    free_env : heph_type IntMap.t;
    bound_env : heph_type list;
}

let empty_env = { free_env = IntMap.empty; bound_env = [] }

let push_bound ty env = { env with bound_env = ty :: env.bound_env }

let boolean_ty = TyClass (Prelude "Boolean", [])
let object_ty = TyClass (Prelude "Object", [])

let correct_tparam_bound recur bounds i sup =
    match List.nth_opt bounds i with Some bd -> recur bd sup | None -> false

let correct_contain recur v x y =
    match y with
    | Wild (Covariant, t) ->
        (match x with
         | Wild (Covariant, s) -> recur s t
         | Wild (Invariant, _) -> recur object_ty t
         | Wild _ -> false
         | _ -> recur x t)
    | Wild (Contravariant, t) ->
        (match x with Wild (Contravariant, s) -> recur t s | Wild _ -> false | _ -> recur t x)
    | Wild (Invariant, _) -> true
    | _ ->
        (match v with
         | Invariant -> type_equal x y
         | Covariant -> recur x y
         | Contravariant -> recur y x)

let mk_subtype ?(mtparam_sup = fun _ _ _ -> false) tparam_bound contain =
    let rec sub bounds classes a b =
        if type_equal a b then true
        else match a, b with
        | TyBot, _ -> true
        | _, TyBot -> false
        | TyClass (c1, a1), TyClass (c2, a2) ->
            if c1 = c2 then
                let vs = tparam_variances_of classes c1 in
                List.length a1 = List.length a2 && List.length a1 = List.length vs &&
                List.for_all2 (fun (x, y) v -> contain (sub bounds classes) v x y)
                    (List.combine a1 a2) vs
            else
                (match parent_of classes c1 with
                 | None -> false
                 | Some (pcr, pargs) ->
                     sub bounds classes
                         (TyClass (pcr, List.map (subst_typaram a1) pargs)) b)
        | TyParam i, TyParam j when i = j -> true
        | TyParam i, _ -> tparam_bound (sub bounds classes) bounds i b
        | Wild (Covariant, w), _ -> sub bounds classes w b
        | Wild (_, _), _ -> sub bounds classes object_ty b
        | MTParam i, MTParam j when i = j -> true
        | MTParam _, TyClass (Prelude "Object", []) -> true
        | MTParam i, _ -> mtparam_sup (sub bounds classes) i b
        | TyArray a1, TyArray a2 -> sub bounds classes a1 a2
        | _ -> false
    in sub

let rec supertypes_of classes ty =
    ty :: (match ty with
        | TyClass (cr, args) ->
            (match parent_of classes cr with
             | None -> []
             | Some (pcr, pargs) ->
                 supertypes_of classes
                     (TyClass (pcr, List.map (subst_typaram args) pargs)))
        | _ -> [])

let lub classes t1 t2 =
    match List.find_opt (fun s -> is_subtype classes t2 s)
              (supertypes_of classes t1) with
    | Some s -> s
    | None -> object_ty

let rec resolve_holes classes cons = function
    | MTParam i | Hole i ->
        (match List.filter_map (fun (j, t) -> if j = i then Some t else None) cons with
         | [] -> object_ty
         | c :: rest -> List.fold_left (fun acc t -> lub classes acc t) c rest)
    | TyClass (cr, args) -> TyClass (cr, List.map (resolve_holes classes cons) args)
    | Wild (v, t) -> Wild (v, resolve_holes classes cons t)
    | t -> t

let rec collect_constraints form actual acc =
    match form, actual with
    | (MTParam i | Hole i), _ -> (i, actual) :: acc
    | TyClass (_, fa), TyClass (_, aa) when List.length fa = List.length aa ->
        List.fold_left2 (fun a f x -> collect_constraints f x a) acc fa aa
    | Wild (_, f), Wild (_, x) -> collect_constraints f x acc
    | _ -> acc

let has_mtparam ty =
    let rec go = function
        | MTParam _ -> true
        | TyClass (_, args) -> List.exists go args
        | Wild (_, t) -> go t
        | _ -> false
    in go ty

let has_hole ty =
    let rec go = function
        | Hole _ -> true
        | TyClass (_, args) -> List.exists go args
        | Wild (_, t) -> go t
        | _ -> false
    in go ty

let rec lookup_method_full classes methods cr args ml =
    match cr with
    | Prelude n ->
        (match prelude_method_sig (n, ml) with
         | Some (ps, ret) ->
             Some ([], List.map (subst_typaram args) ps, subst_typaram args ret)
         | None ->
             match prelude_parent n with
             | None -> None
             | Some p -> lookup_method_full classes methods p [] ml)
    | Synth i ->
        (match List.find_opt (fun m ->
            m.cm_class = i && m.cm_label = ml) methods with
         | Some m ->
             Some (List.map (fun tp -> subst_typaram args tp.tp_bound) m.cm_tparams,
                   List.map (fun (_, pt) -> subst_typaram args pt) m.cm_params,
                   subst_typaram args m.cm_return)
         | None ->
             match class_of classes i with
             | None -> None
             | Some ce ->
                 let (pcr, pa) = ce.cc_parent in
                 lookup_method_full classes methods pcr
                     (List.map (subst_typaram args) pa) ml)

let default_xsub bounds classes a b = is_subtype ~bounds classes a b
let default_xbounds bounds classes ty = type_bounds_ok ~bounds classes ty
let default_xlub _bounds classes t1 t2 = lub classes t1 t2
let correct_approx = function
    | Wild (Covariant, b) -> b
    | Wild (_, _) -> object_ty
    | t -> t

let make_check
    ?(is_subtype = default_xsub)
    ?(lub = default_xlub)
    ?(lookup = lookup_method_full)
    ?(type_bounds_ok = default_xbounds)
    ?(resolve_new = resolve_holes)
    ?(resolve_invoke = resolve_holes)
    ?(fields_of = fields_of)
    ?(cond_push = true)
    ?(approx_field = correct_approx)
    ?(check_mbounds = true)
    ?(new_arity_ok = (fun _cr nargs total _own -> nargs = total))
    ?(array_elem_relax = false)
    ?(target_infer_invoke = true)
    ?(lambda_result_check = true)
    ?(check_default = true)
    ?(typaram_field_check = true)
    ?(new_field_filter = fun (_ : heph_type) -> true)
    ?(invoke_param_filter = fun (_ : heph_type list) (_ : heph_type) -> true)
    ?(ctor_arg_infer = fun (_ : heph_type) -> true)
    ?(invoke_result = fun (t : heph_type) -> t)
    () =
    let xsub = is_subtype and xlub = lub and xlookup = lookup
    and xbounds = type_bounds_ok and xrnew = resolve_new
    and xrinvoke = resolve_invoke and xfields = fields_of
    and xcond_push = cond_push and xapprox = approx_field
    and xmbounds = check_mbounds and xarity = new_arity_ok
    and xrelax_arr = array_elem_relax and xtarget_infer = target_infer_invoke
    and xlambda_result = lambda_result_check and xdefault = check_default
    and xtfield = typaram_field_check
    and xnewfield = new_field_filter and xparamfilter = invoke_param_filter
    and xctorinfer = ctor_arg_infer and xresult = invoke_result in
    let rec check_type bounds env classes methods expected term =
        let sub a b = xsub bounds classes a b in
        let verify ty = match expected with
            | Some e -> if sub ty e then Some ty else None
            | None -> Some ty in
        match term with
        | Var id -> (match IntMap.find_opt id env.free_env with
            | Some ty -> verify ty | None -> None)
        | BVar i -> (match List.nth_opt env.bound_env i with
            | Some ty -> verify ty | None -> None)
        | New (ty, args) -> synth_new bounds env classes methods expected ty args
        | FieldAccess (e, fl) ->
            (match synth bounds env classes methods e with
             | Some (TyClass (cr, cargs)) ->
                 (match List.assoc_opt fl (xfields classes cr cargs) with
                  | Some ty -> verify (xapprox ty) | None -> None)
             | _ -> None)
        | MethodInvoke (e, ml, args) ->
            synth_invoke bounds env classes methods expected e ml args
        | Lambda (param_ty, body) ->
            (match synth bounds (push_bound param_ty env) classes methods body with
             | Some bt ->
                 let ft = TyClass (Prelude "Function", [param_ty; bt]) in
                 (match expected with
                  | Some (TyClass (Prelude "Function", [ep; _])) when not xlambda_result ->
                      if sub ep param_ty then Some ft else None
                  | _ -> verify ft)
             | None -> None)
        | Cond (c, t, e) ->
            (match synth bounds env classes methods c with
             | Some c_ty when sub c_ty boolean_ty ->
                 let chk b =
                     if xcond_push
                     then check_type bounds env classes methods expected b
                     else synth bounds env classes methods b in
                 (match chk t, chk e with
                  | Some t_ty, Some e_ty -> verify (xlub bounds classes t_ty e_ty)
                  | _ -> None)
             | _ -> None)
        | Null t -> if xbounds bounds classes t then verify t else None
        | If _ -> None
    and synth bounds env classes methods term =
        check_type bounds env classes methods None term
    and synth_new bounds env classes methods expected ty args =
        let sub a b = xsub bounds classes a b in
        match ty with
        | TyClass (cr, class_args) ->
            if not (List.exists has_hole class_args) then
                let fs = xfields classes cr class_args in
                let own = (match cr with
                    | Synth i ->
                        (match class_of classes i with
                         | Some ce -> List.length ce.cc_fields | None -> 0)
                    | _ -> 0) in
                if not (xarity cr (List.length args) (List.length fs) own) then None
                else if not (List.for_all (fun (_, ft) -> xnewfield ft) fs) then None
                else
                    let n = min (List.length args) (List.length fs) in
                    let take k l = List.filteri (fun i _ -> i < k) l in
                    if List.for_all2 (fun (_, ft) arg ->
                        match ft, arg with
                        | TyParam _, _ when not xtfield ->
                            synth bounds env classes methods arg <> None
                        | _, MethodInvoke _ when not (xctorinfer ft) ->
                            (match synth bounds env classes methods arg with
                             | Some at -> sub at ft
                             | None -> false)
                        | _ -> check_type bounds env classes methods (Some ft) arg <> None)
                        (take n fs) (take n args)
                    then (match expected with
                          | Some e -> if sub ty e then Some ty else None | None -> Some ty)
                    else None
            else
                let pfields = xfields classes cr class_args in
                if List.length args <> List.length pfields then None
                else
                    let arg_tys = List.map (synth bounds env classes methods) args in
                    if List.exists (fun o -> o = None) arg_tys then None
                    else
                        let arg_tys = List.map Option.get arg_tys in
                        let cons = List.fold_left2 (fun acc (_, ft) at ->
                            collect_constraints ft at acc) [] pfields arg_tys in
                        let cons = match expected with
                            | Some e -> collect_constraints ty e cons | None -> cons in
                        let solved = xrnew classes cons (TyClass (cr, class_args)) in
                        let solved_args =
                            match solved with TyClass (_, a) -> a | _ -> class_args in
                        let solved_fields = xfields classes cr solved_args in
                        if List.for_all2 (fun (_, ft) at -> sub at ft)
                               solved_fields arg_tys
                           && xbounds [] classes solved
                        then (match expected with
                              | Some e -> if sub solved e then Some solved else None
                              | None -> Some solved)
                        else None
        | TyArray comp ->
            let elem_ok e =
                check_type bounds env classes methods (Some comp) e <> None
                || (xrelax_arr &&
                    (match synth bounds env classes methods e with
                     | Some et -> sub comp et
                     | None -> false)) in
            if List.for_all elem_ok args then
                (match expected with
                 | Some e -> if sub (TyArray comp) e then Some (TyArray comp) else None
                 | None -> Some (TyArray comp))
            else None
        | _ -> None
    and synth_invoke bounds env classes methods expected recv ml args =
        let sub a b = xsub bounds classes a b in
        match synth bounds env classes methods recv with
        | Some (TyClass (cr, class_args)) ->
            (match xlookup classes methods cr class_args ml with
             | None -> None
             | Some (mbounds, param_tys, ret) ->
                 if List.length args <> List.length param_tys then None
                 else if not (List.for_all (xparamfilter bounds) param_tys) then None
                 else if mbounds = [] && not (has_mtparam ret)
                         && not (List.exists has_mtparam param_tys) then
                     (if List.for_all2 (fun pt arg ->
                          check_type bounds env classes methods (Some pt) arg <> None)
                          param_tys args
                      then (let ret = xresult ret in
                            match expected with
                            | Some e -> if sub ret e then Some ret else None
                            | None -> Some ret)
                      else None)
                 else
                     let arg_tys = List.map (synth bounds env classes methods) args in
                     if List.exists (fun o -> o = None) arg_tys then None
                     else
                         let arg_tys = List.map Option.get arg_tys in
                         let cons = List.fold_left2 (fun acc pt at ->
                             collect_constraints pt at acc) [] param_tys arg_tys in
                         let cons = match expected with
                             | Some e when xtarget_infer -> collect_constraints ret e cons
                             | _ -> cons in
                         let solved_params = List.map (xrinvoke classes cons) param_tys in
                         let solved_ret = xrinvoke classes cons ret in
                         let bounds_ok = List.for_all (fun (i, b) ->
                             sub (xrinvoke classes cons (MTParam i))
                                 (xrinvoke classes cons b))
                             (List.mapi (fun i b -> (i, b)) mbounds) in
                         if List.for_all2 (fun pt at -> sub at pt)
                                solved_params arg_tys
                            && (not xmbounds || bounds_ok)
                         then (let solved_ret = xresult solved_ret in
                               match expected with
                               | Some e -> if sub solved_ret e
                                           then Some solved_ret else None
                               | None -> Some solved_ret)
                         else None)
        | _ -> None
    in
    let method_well_typed classes methods m =
        let bounds = match class_of classes m.cm_class with
            | Some ce -> List.map (fun tp -> tp.tp_bound) ce.cc_tparams | None -> [] in
        let this_type =
            let owner = Synth m.cm_class in
            match class_of classes m.cm_class with
            | None -> TyClass (owner, [])
            | Some ce ->
                let n = List.length ce.cc_tparams in
                TyClass (owner, List.init n (fun i -> TyParam i)) in
        let env0 = { empty_env with
            free_env = IntMap.add m.cm_this_sym this_type empty_env.free_env } in
        let env = List.fold_left (fun e (sid, ty) ->
            { e with free_env = IntMap.add sid ty e.free_env }) env0 m.cm_params in
        check_type bounds env classes methods (Some m.cm_return) m.cm_body <> None
        && (match m.cm_default with
            | Some (ty, d) when xdefault ->
                check_type bounds env classes methods (Some ty) d <> None
            | _ -> true)
    in
    fun (fact : tagged_fact) ->
        let classes = fact.tf_classes and methods = fact.tf_methods in
        let env = { empty_env with
            free_env = List.fold_left (fun m (sid, ty) ->
                IntMap.add sid ty m) IntMap.empty fact.tf_bindings } in
        let class_ok ce =
            let cb = List.map (fun tp -> tp.tp_bound) ce.cc_tparams in
            let (pcr, pargs) = ce.cc_parent in
            xbounds cb classes (TyClass (pcr, pargs))
            && List.for_all (fun (_, ft) -> xbounds cb classes ft) ce.cc_fields in
        List.for_all class_ok classes
        && List.for_all (method_well_typed classes methods) methods
        && check_type [] env classes methods (Some fact.tf_main_type)
               fact.tf_main_term <> None

let check = make_check ()

let string_of_fact (fact : tagged_fact) = fact.tf_rendered
