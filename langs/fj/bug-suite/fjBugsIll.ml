module L = FjPrograms
module Fp = FjTypechecker
module IntMap = Map.Make(Int)

type synth_fn =
    L.concrete_type IntMap.t
    -> L.concrete_class_entry list
    -> L.concrete_method_entry list
    -> L.term
    -> L.concrete_type option

type rules = {
    var    : synth_fn -> L.concrete_type IntMap.t -> int -> L.concrete_type option;
    new_   : synth_fn -> L.concrete_type IntMap.t -> L.concrete_class_entry list -> L.concrete_method_entry list
             -> int -> L.term list -> L.concrete_type option;
    field  : synth_fn -> L.concrete_type IntMap.t -> L.concrete_class_entry list -> L.concrete_method_entry list
             -> L.term -> int -> L.concrete_type option;
    invk   : synth_fn -> L.concrete_type IntMap.t -> L.concrete_class_entry list -> L.concrete_method_entry list
             -> L.term -> int -> L.term list -> L.concrete_type option;
    body_ok : L.concrete_class_entry list -> L.concrete_method_entry list
              -> L.concrete_type -> L.concrete_type -> bool;
}

let rec synth_with (r : rules) env classes methods = function
    | L.Var id -> r.var (synth_with r) env id
    | L.New (-1, []) -> Some L.ConcreteObject
    | L.New (-1, _) -> None
    | L.New (c, args) -> r.new_ (synth_with r) env classes methods c args
    | L.FieldAccess (e, fl) -> r.field (synth_with r) env classes methods e fl
    | L.MethodInvoke (e, ml, args) ->
        r.invk (synth_with r) env classes methods e ml args

let make_synth (r : rules) : synth_fn = synth_with r

let default_var _go env id = IntMap.find_opt id env

let default_new go env classes methods c args =
    let expected = Fp.all_fields_of classes c in
    if List.length args <> List.length expected then None else
    let ok = List.for_all2 (fun (_, ft) arg ->
        match go env classes methods arg with
        | Some at -> Fp.is_subtype classes at ft
        | None -> false
    ) expected args in
    if ok then Some (L.ConcreteClass c) else None

let default_field go env classes methods e fl =
    match go env classes methods e with
    | Some (L.ConcreteClass c) -> List.assoc_opt fl (Fp.all_fields_of classes c)
    | _ -> None

let default_invk go env classes methods e ml args =
    match go env classes methods e with
    | Some (L.ConcreteClass c) ->
        (match Fp.lookup_method methods classes c ml with
         | None -> None
         | Some (param_tys, ret) ->
             if List.length args <> List.length param_tys then None else
             let ok = List.for_all2 (fun pt arg ->
                 match go env classes methods arg with
                 | Some at -> Fp.is_subtype classes at pt
                 | None -> false
             ) param_tys args in
             if ok then Some ret else None)
    | _ -> None

let default_body_ok classes _methods body_ty ret =
    Fp.is_subtype classes body_ty ret

let default_rules = {
    var = default_var;
    new_ = default_new;
    field = default_field;
    invk = default_invk;
    body_ok = default_body_ok;
}

let list_first k l = List.filteri (fun i _ -> i < k) l

let args_all_typed go env classes methods args =
    List.for_all (fun a ->
        match go env classes methods a with Some _ -> true | None -> false) args

let var_lookup_rule _go env id =
    match IntMap.find_opt id env with
    | Some t -> Some t
    | None -> Some L.ConcreteObject

let bug_var_lookup = { default_rules with var = var_lookup_rule }

let new_arity_rule go env classes methods c args =
    let expected = Fp.all_fields_of classes c in
    let n = min (List.length expected) (List.length args) in
    let pairs = List.combine (list_first n expected) (list_first n args) in
    let ok = List.for_all (fun ((_, ft), arg) ->
        match go env classes methods arg with
        | Some at -> Fp.is_subtype classes at ft
        | None -> false
    ) pairs in
    if ok then Some (L.ConcreteClass c) else None

let bug_new_arity = { default_rules with new_ = new_arity_rule }

let new_arg_subtype_rule go env classes methods c args =
    let expected = Fp.all_fields_of classes c in
    if List.length args <> List.length expected then None else
    if args_all_typed go env classes methods args
    then Some (L.ConcreteClass c) else None

let bug_new_arg_subtype = { default_rules with new_ = new_arg_subtype_rule }

let new_class_exists_rule go env classes methods c args =
    match Fp.class_of classes c with
    | Some _ -> default_new go env classes methods c args
    | None ->
        if args_all_typed go env classes methods args
        then Some (L.ConcreteClass c) else None

let bug_new_class_exists = { default_rules with new_ = new_class_exists_rule }

let field_receiver_rule go env classes methods e fl =
    match go env classes methods e with
    | Some (L.ConcreteClass c) -> List.assoc_opt fl (Fp.all_fields_of classes c)
    | Some L.ConcreteObject ->
        List.find_map (fun ce -> List.assoc_opt fl ce.L.cc_own_fields) classes
    | _ -> None

let bug_field_receiver = { default_rules with field = field_receiver_rule }

let field_exists_rule go env classes methods e fl =
    match go env classes methods e with
    | Some (L.ConcreteClass c) ->
        (match List.assoc_opt fl (Fp.all_fields_of classes c) with
         | Some t -> Some t
         | None -> Some L.ConcreteObject)
    | _ -> None

let bug_field_exists = { default_rules with field = field_exists_rule }

let try_invk_at go env classes methods ml args c =
    match Fp.lookup_method methods classes c ml with
    | None -> None
    | Some (param_tys, ret) ->
        if List.length args <> List.length param_tys then None else
        let ok = List.for_all2 (fun pt arg ->
            match go env classes methods arg with
            | Some at -> Fp.is_subtype classes at pt
            | None -> false
        ) param_tys args in
        if ok then Some ret else None

let invk_receiver_rule go env classes methods e ml args =
    match go env classes methods e with
    | Some (L.ConcreteClass c) -> try_invk_at go env classes methods ml args c
    | Some L.ConcreteObject ->
        List.find_map (fun ce ->
            try_invk_at go env classes methods ml args ce.L.cc_label) classes
    | _ -> None

let bug_invk_receiver = { default_rules with invk = invk_receiver_rule }

let invk_method_rule go env classes methods e ml args =
    match go env classes methods e with
    | Some (L.ConcreteClass c) ->
        (match Fp.lookup_method methods classes c ml with
         | None ->
             if args_all_typed go env classes methods args
             then Some L.ConcreteObject else None
         | Some _ -> try_invk_at go env classes methods ml args c)
    | _ -> None

let bug_invk_method = { default_rules with invk = invk_method_rule }

let invk_arity_rule go env classes methods e ml args =
    match go env classes methods e with
    | Some (L.ConcreteClass c) ->
        (match Fp.lookup_method methods classes c ml with
         | None -> None
         | Some (param_tys, ret) ->
             let n = min (List.length param_tys) (List.length args) in
             let pairs =
                 List.combine (list_first n param_tys) (list_first n args) in
             let ok = List.for_all (fun (pt, arg) ->
                 match go env classes methods arg with
                 | Some at -> Fp.is_subtype classes at pt
                 | None -> false
             ) pairs in
             if ok then Some ret else None)
    | _ -> None

let bug_invk_arity = { default_rules with invk = invk_arity_rule }

let invk_arg_subtype_rule go env classes methods e ml args =
    match go env classes methods e with
    | Some (L.ConcreteClass c) ->
        (match Fp.lookup_method methods classes c ml with
         | None -> None
         | Some (param_tys, ret) ->
             if List.length args <> List.length param_tys then None else
             if args_all_typed go env classes methods args
             then Some ret else None)
    | _ -> None

let bug_invk_arg_subtype = { default_rules with invk = invk_arg_subtype_rule }

let bug_method_body_subtype = { default_rules with
    body_ok = fun _classes _methods _body_ty _ret -> true
}

let method_ok_with r classes methods m =
    let this_type = L.ConcreteClass m.L.cm_class in
    let env0 = IntMap.singleton m.L.cm_this_sym this_type in
    let env = List.fold_left (fun e (sid, ty) ->
        IntMap.add sid ty e) env0 m.L.cm_params in
    match make_synth r env classes methods m.L.cm_body with
    | None -> false
    | Some body_ty -> r.body_ok classes methods body_ty m.L.cm_return

let check_with r (fact : L.tagged_fact) =
    let classes = fact.L.tf_classes in
    let methods = fact.L.tf_methods in
    let env = List.fold_left (fun m (sid, ty) ->
        IntMap.add sid ty m) IntMap.empty fact.L.tf_bindings in
    List.for_all (method_ok_with r classes methods) methods
    && (match make_synth r env classes methods fact.L.tf_main_term with
        | None -> false
        | Some ty -> r.body_ok classes methods ty fact.L.tf_main_type)

let bug_exposed r fact =
    if Fp.check fact then false else
    check_with r fact

let make name bug_id sev desc r =
    (name, "fj-program-neg", bug_id, sev, desc, `Accept,
     (fun f -> not (bug_exposed r f)))

let bugs = [
    make "fjp-neg-var" 1 `Shallow
        "Var: accepts unbound symbols (defaults their type)" bug_var_lookup;
    make "fjp-neg-new-arity" 2 `Shallow
        "New: doesn't check arg count matches field count" bug_new_arity;
    make "fjp-neg-new-arg-subtype" 3 `Shallow
        "New: doesn't check arg types are subtypes of field types" bug_new_arg_subtype;
    make "fjp-neg-new-class" 4 `Medium
        "New: accepts nonexistent class labels" bug_new_class_exists;
    make "fjp-neg-field-receiver" 5 `Shallow
        "FieldAccess: accepts non-class receiver types" bug_field_receiver;
    make "fjp-neg-field-exists" 6 `Shallow
        "FieldAccess: accepts nonexistent field names" bug_field_exists;
    make "fjp-neg-invk-receiver" 7 `Shallow
        "MethodInvoke: accepts non-class receiver types" bug_invk_receiver;
    make "fjp-neg-invk-method" 8 `Shallow
        "MethodInvoke: accepts nonexistent method labels" bug_invk_method;
    make "fjp-neg-invk-arity" 9 `Shallow
        "MethodInvoke: doesn't check arg count matches param count" bug_invk_arity;
    make "fjp-neg-invk-arg-subtype" 10 `Shallow
        "MethodInvoke: doesn't check arg types are subtypes of param types" bug_invk_arg_subtype;
    make "fjp-neg-method-body" 11 `Medium
        "Method body type not checked against declared return type" bug_method_body_subtype;
]
