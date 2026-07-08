open HephPrograms
module H = HephTypechecker
module IntMap = Map.Make(Int)

type env = H.env

type synth_fn =
    env
    -> concrete_class list
    -> concrete_method list
    -> term
    -> heph_type option

type rules = {
    var    : synth_fn -> env -> int -> heph_type option;
    bvar   : synth_fn -> env -> int -> heph_type option;
    new_   : synth_fn -> env -> concrete_class list
             -> concrete_method list -> heph_type -> term list
             -> heph_type option;
    field  : synth_fn -> env -> concrete_class list
             -> concrete_method list -> term -> int
             -> heph_type option;
    invk   : synth_fn -> env -> concrete_class list
             -> concrete_method list -> term -> int
             -> term list -> heph_type option;
    lambda : synth_fn -> env -> concrete_class list
             -> concrete_method list -> heph_type -> term
             -> heph_type option;
    if_    : synth_fn -> env -> concrete_class list
             -> concrete_method list -> heph_type -> term -> term -> term
             -> heph_type option;
    body_ok : concrete_class list -> concrete_method list
              -> heph_type -> heph_type -> bool;
    prog_ok : concrete_class list -> bool;
}

let make_synth (r : rules) : synth_fn =
    let rec go env classes methods = function
        | Var id -> r.var go env id
        | BVar i -> r.bvar go env i
        | New (ty, args) -> r.new_ go env classes methods ty args
        | FieldAccess (e, fl) -> r.field go env classes methods e fl
        | MethodInvoke (e, ml, args) -> r.invk go env classes methods e ml args
        | Lambda (pty, body) -> r.lambda go env classes methods pty body
        | If (rty, c, t, e) -> r.if_ go env classes methods rty c t e
    in
    go

let default_var _go (env : env) id = IntMap.find_opt id env.free_env

let default_bvar _go (env : env) i =
    try Some (List.nth env.bound_env i)
    with Failure _ | Invalid_argument _ -> None

let default_new go env classes methods ty args =
    match ty with
    | TyClass (cr, class_args) ->
        let expected = H.fields_of classes cr class_args in
        if List.length args <> List.length expected then None
        else
            let ok = List.for_all2 (fun (_, ft) arg ->
                match go env classes methods arg with
                | Some at -> H.is_subtype classes at ft
                | None -> false
            ) expected args in
            if ok then Some ty else None
    | _ -> None

let default_field go env classes methods e fl =
    match go env classes methods e with
    | Some (TyClass (cr, args)) ->
        List.assoc_opt fl (H.fields_of classes cr args)
    | _ -> None

let default_invk go env classes methods e ml args =
    match go env classes methods e with
    | Some (TyClass (cr, class_args)) ->
        (match H.lookup_method classes methods cr class_args ml with
         | None -> None
         | Some (param_tys, ret) ->
             if List.length args <> List.length param_tys then None
             else
                 let ok = List.for_all2 (fun pt arg ->
                     match go env classes methods arg with
                     | Some at -> H.is_subtype classes at pt
                     | None -> false
                 ) param_tys args in
                 if ok then Some ret else None)
    | _ -> None

let default_lambda go env classes methods pty body =
    let env' = H.push_bound pty env in
    match go env' classes methods body with
    | None -> None
    | Some body_ty ->
        Some (TyClass (Prelude "Function", [pty; body_ty]))

let default_if go env classes methods rty c t e =
    match go env classes methods c,
          go env classes methods t,
          go env classes methods e with
    | Some ct, Some tt, Some et ->
        if H.is_subtype classes ct (TyClass (Prelude "Boolean", []))
           && H.is_subtype classes tt rty
           && H.is_subtype classes et rty
        then Some rty else None
    | _ -> None

let default_body_ok classes _methods body_ty ret = H.is_subtype classes body_ty ret

let default_prog_ok classes = H.classtable_bounds_ok classes

let default_rules = {
    var = default_var; bvar = default_bvar; new_ = default_new;
    field = default_field; invk = default_invk; lambda = default_lambda;
    if_ = default_if;
    body_ok = default_body_ok; prog_ok = default_prog_ok;
}

let default_type = TyClass (Prelude "Object", [])

let bug_var_lookup = { default_rules with
    var = fun _go env id ->
        (match IntMap.find_opt id env.H.free_env with
         | Some t -> Some t
         | None -> Some default_type)
}

let bug_bvar_bounds = { default_rules with
    bvar = fun _go env i ->
        (try Some (List.nth env.H.bound_env i)
         with Failure _ | Invalid_argument _ -> Some default_type)
}

let bug_new_is_tyclass = { default_rules with
    new_ = fun go env classes methods ty args ->
        match ty with
        | TyClass _ -> default_new go env classes methods ty args
        | _ ->
            if List.for_all (fun a ->
                match go env classes methods a with Some _ -> true | None -> false
            ) args
            then Some ty
            else None
}

let bug_new_arity = { default_rules with
    new_ = fun go env classes methods ty args ->
        match ty with
        | TyClass (cr, class_args) ->
            let expected = H.fields_of classes cr class_args in
            let n = min (List.length expected) (List.length args) in
            let first k l = List.filteri (fun i _ -> i < k) l in
            let pairs = List.combine (first n expected) (first n args) in
            let ok = List.for_all (fun ((_, ft), arg) ->
                match go env classes methods arg with
                | Some at -> H.is_subtype classes at ft
                | None -> false
            ) pairs in
            if ok then Some ty else None
        | _ -> None
}

let bug_new_arg_subtype = { default_rules with
    new_ = fun go env classes methods ty args ->
        match ty with
        | TyClass (cr, class_args) ->
            let expected = H.fields_of classes cr class_args in
            if List.length args <> List.length expected then None
            else
                let ok = List.for_all (fun arg ->
                    match go env classes methods arg with
                    | Some _ -> true
                    | None -> false
                ) args in
                if ok then Some ty else None
        | _ -> None
}

let bug_field_receiver = { default_rules with
    field = fun go env classes methods e fl ->
        match go env classes methods e with
        | Some (TyClass (cr, args)) ->
            List.assoc_opt fl (H.fields_of classes cr args)
        | Some _ ->
            List.find_map (fun ce ->
                List.assoc_opt fl ce.cc_fields
            ) classes
        | None -> None
}

let bug_field_exists = { default_rules with
    field = fun go env classes methods e fl ->
        match go env classes methods e with
        | Some (TyClass (cr, args)) ->
            (match List.assoc_opt fl (H.fields_of classes cr args) with
             | Some t -> Some t
             | None -> Some default_type)
        | _ -> None
}

let bug_invk_receiver = { default_rules with
    invk = fun go env classes methods e ml args ->
        let try_call cr cargs =
            match H.lookup_method classes methods cr cargs ml with
            | None -> None
            | Some (param_tys, ret) ->
                if List.length args <> List.length param_tys then None
                else
                    let ok = List.for_all2 (fun pt arg ->
                        match go env classes methods arg with
                        | Some at -> H.is_subtype classes at pt
                        | None -> false
                    ) param_tys args in
                    if ok then Some ret else None
        in
        match go env classes methods e with
        | Some (TyClass (cr, cargs)) -> try_call cr cargs
        | Some _ ->
            List.find_map (fun ce -> try_call (Synth ce.cc_label) []) classes
        | None -> None
}

let bug_invk_method = { default_rules with
    invk = fun go env classes methods e ml args ->
        match go env classes methods e with
        | Some (TyClass (cr, class_args)) ->
            (match H.lookup_method classes methods cr class_args ml with
             | None ->
                 if List.for_all (fun a ->
                     match go env classes methods a with Some _ -> true | None -> false
                 ) args
                 then Some default_type
                 else None
             | Some (param_tys, ret) ->
                 if List.length args <> List.length param_tys then None
                 else
                     let ok = List.for_all2 (fun pt arg ->
                         match go env classes methods arg with
                         | Some at -> H.is_subtype classes at pt
                         | None -> false
                     ) param_tys args in
                     if ok then Some ret else None)
        | _ -> None
}

let bug_invk_arity = { default_rules with
    invk = fun go env classes methods e ml args ->
        match go env classes methods e with
        | Some (TyClass (cr, class_args)) ->
            (match H.lookup_method classes methods cr class_args ml with
             | None -> None
             | Some (param_tys, ret) ->
                 let n = min (List.length param_tys) (List.length args) in
                 let first k l = List.filteri (fun i _ -> i < k) l in
                 let pairs = List.combine (first n param_tys) (first n args) in
                 let ok = List.for_all (fun (pt, arg) ->
                     match go env classes methods arg with
                     | Some at -> H.is_subtype classes at pt
                     | None -> false
                 ) pairs in
                 if ok then Some ret else None)
        | _ -> None
}

let bug_invk_arg_subtype = { default_rules with
    invk = fun go env classes methods e ml args ->
        match go env classes methods e with
        | Some (TyClass (cr, class_args)) ->
            (match H.lookup_method classes methods cr class_args ml with
             | None -> None
             | Some (param_tys, ret) ->
                 if List.length args <> List.length param_tys then None
                 else
                     let ok = List.for_all (fun arg ->
                         match go env classes methods arg with
                         | Some _ -> true
                         | None -> false
                     ) args in
                     if ok then Some ret else None)
        | _ -> None
}

let bug_lambda_body = { default_rules with
    lambda = fun _go _env _classes _methods pty _body ->
        Some (TyClass (Prelude "Function", [pty; default_type]))
}

let bug_method_body_subtype = { default_rules with
    body_ok = fun _classes _methods _body_ty _ret -> true
}

let rec fields_without_subst classes cr _args =
    match cr with
    | Prelude _ -> []
    | Synth i ->
        (match H.class_of classes i with
         | None -> []
         | Some ce ->
             let (par_cr, _par_args) = ce.cc_parent in
             let parent_fs = fields_without_subst classes par_cr [] in
             parent_fs @ ce.cc_fields)

let rec lookup_method_without_subst classes methods cr _args ml =
    match cr with
    | Prelude n ->
        (match H.prelude_method_sig (n, ml) with
         | Some (ps, ret) -> Some (ps, ret)
         | None ->
             match H.prelude_parent n with
             | None -> None
             | Some p -> lookup_method_without_subst classes methods p [] ml)
    | Synth i ->
        (match List.find_opt (fun m ->
            m.cm_class = i && m.cm_label = ml) methods with
         | Some m ->
             Some (List.map snd m.cm_params, m.cm_return)
         | None ->
             match H.class_of classes i with
             | None -> None
             | Some ce ->
                 let (pcr, _pa) = ce.cc_parent in
                 lookup_method_without_subst classes methods pcr [] ml)

let bug_no_typaram_subst = {
    var = default_var;
    bvar = default_bvar;
    new_ = (fun go env classes methods ty args ->
        match ty with
        | TyClass (cr, class_args) ->
            let expected = fields_without_subst classes cr class_args in
            if List.length args <> List.length expected then None
            else
                let ok = List.for_all (fun a ->
                    match go env classes methods a with
                    | Some _ -> true
                    | None -> false
                ) args in
                if ok then Some ty else None
        | _ -> None);
    field = (fun go env classes methods e fl ->
        match go env classes methods e with
        | Some (TyClass (cr, args)) ->
            List.assoc_opt fl (fields_without_subst classes cr args)
        | _ -> None);
    invk = (fun go env classes methods e ml args ->
        match go env classes methods e with
        | Some (TyClass (cr, cargs)) ->
            (match lookup_method_without_subst classes methods cr cargs ml with
             | None -> None
             | Some (param_tys, ret) ->
                 if List.length args <> List.length param_tys then None
                 else
                     let ok = List.for_all (fun a ->
                         match go env classes methods a with
                         | Some _ -> true
                         | None -> false
                     ) args in
                     if ok then Some ret else None)
        | _ -> None);
    lambda = default_lambda;
    if_ = default_if;
    body_ok = default_body_ok;
    prog_ok = default_prog_ok;
}

let bug_no_bound_check = { default_rules with prog_ok = (fun _ -> true) }

let rec is_subtype_lax_args classes sub sup =
    if H.type_equal sub sup then true
    else match sub, sup with
    | TyBot, _ -> true
    | _, TyBot -> false
    | TyClass (c1, a1), TyClass (c2, _a2) ->
        if c1 = c2 then true
        else
            (match H.parent_of classes c1 with
             | None -> false
             | Some (pcr, pargs) ->
                 let pargs' = List.map (H.subst_typaram a1) pargs in
                 is_subtype_lax_args classes (TyClass (pcr, pargs')) sup)
    | TyParam i, TyParam j -> i = j
    | _ -> false

let bug_subtype_lax_args =
    let new_ go env classes methods ty args =
        match ty with
        | TyClass (cr, class_args) ->
            let expected = H.fields_of classes cr class_args in
            if List.length args <> List.length expected then None
            else
                let ok = List.for_all2 (fun (_, ft) arg ->
                    match go env classes methods arg with
                    | Some at -> is_subtype_lax_args classes at ft
                    | None -> false
                ) expected args in
                if ok then Some ty else None
        | _ -> None
    in
    let invk go env classes methods e ml args =
        match go env classes methods e with
        | Some (TyClass (cr, class_args)) ->
            (match H.lookup_method classes methods cr class_args ml with
             | None -> None
             | Some (param_tys, ret) ->
                 if List.length args <> List.length param_tys then None
                 else
                     let ok = List.for_all2 (fun pt arg ->
                         match go env classes methods arg with
                         | Some at -> is_subtype_lax_args classes at pt
                         | None -> false
                     ) param_tys args in
                     if ok then Some ret else None)
        | _ -> None
    in
    { default_rules with
        new_ = new_;
        invk = invk;
        body_ok = (fun classes _methods body_ty ret ->
            is_subtype_lax_args classes body_ty ret) }

let method_ok_with r classes methods m =
    let this_type =
        let owner = Synth m.cm_class in
        match H.class_of classes m.cm_class with
        | None -> TyClass (owner, [])
        | Some ce ->
            let n = List.length ce.cc_tparams in
            TyClass (owner, List.init n (fun i -> TyParam i))
    in
    let env0 = { H.empty_env with
        free_env = IntMap.add m.cm_this_sym this_type H.empty_env.free_env } in
    let env = List.fold_left (fun e (sid, ty) ->
        { e with H.free_env = IntMap.add sid ty e.H.free_env }
    ) env0 m.cm_params in
    match make_synth r env classes methods m.cm_body with
    | None -> false
    | Some body_ty -> r.body_ok classes methods body_ty m.cm_return

let check_with r (fact : tagged_fact) =
    let classes = fact.tf_classes in
    let methods = fact.tf_methods in
    let env = { H.empty_env with
        free_env = List.fold_left (fun m (sid, ty) ->
            IntMap.add sid ty m) IntMap.empty fact.tf_bindings } in
    r.prog_ok classes
    && List.for_all (method_ok_with r classes methods) methods
    && (match make_synth r env classes methods fact.tf_main_term with
        | None -> false
        | Some ty -> r.body_ok classes methods ty fact.tf_main_type)

let bug_exposed r fact =
    if H.check fact then false
    else check_with r fact

let make name bug_id sev desc r =
    (name, "heph-neg", bug_id, sev, desc, `Accept,
     (fun f -> not (bug_exposed r f)))

let bugs = [
    make "heph-neg-var" 1 `Shallow
        "Var: accepts unbound symbols (defaults their type)" bug_var_lookup;
    make "heph-neg-bvar" 2 `Shallow
        "BVar: accepts out-of-range bound indices" bug_bvar_bounds;
    make "heph-neg-new-is-tyclass" 3 `Medium
        "New: accepts non-class target types (TyParam / TyBot / TVar)" bug_new_is_tyclass;
    make "heph-neg-new-arity" 4 `Shallow
        "New: doesn't check arg count matches field count" bug_new_arity;
    make "heph-neg-new-arg-subtype" 5 `Shallow
        "New: doesn't check arg types are subtypes of field types" bug_new_arg_subtype;
    make "heph-neg-field-receiver" 6 `Shallow
        "FieldAccess: accepts non-class receiver types" bug_field_receiver;
    make "heph-neg-field-exists" 7 `Shallow
        "FieldAccess: accepts nonexistent field names" bug_field_exists;
    make "heph-neg-invk-receiver" 8 `Shallow
        "MethodInvoke: accepts non-class receiver types" bug_invk_receiver;
    make "heph-neg-invk-method" 9 `Shallow
        "MethodInvoke: accepts nonexistent method labels" bug_invk_method;
    make "heph-neg-invk-arity" 10 `Shallow
        "MethodInvoke: doesn't check arg count matches param count" bug_invk_arity;
    make "heph-neg-invk-arg-subtype" 11 `Shallow
        "MethodInvoke: doesn't check arg types are subtypes of param types" bug_invk_arg_subtype;
    make "heph-neg-lambda-body" 12 `Medium
        "Lambda: doesn't check the body typechecks" bug_lambda_body;
    make "heph-neg-method-body" 13 `Medium
        "Method body type not checked against declared return type" bug_method_body_subtype;
    make "heph-neg-typaram-subst" 14 `Medium
        "fields/method lookup forgets TyParam substitution for receiver's type args" bug_no_typaram_subst;
    make "heph-neg-subtype-lax-args" 15 `Deep
        "Subtyping ignores generic-argument containment (GROOVY-10625)" bug_subtype_lax_args;
    make "heph-neg-no-bound-check" 16 `Medium
        "Class table not checked against type-parameter upper bounds (GROOVY-10369)" bug_no_bound_check;
]
