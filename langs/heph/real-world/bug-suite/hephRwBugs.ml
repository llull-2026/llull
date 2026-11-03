open HephRwPrograms
module H = HephRwTypechecker

let lub_10330 _bounds classes t1 t2 =
    match t1, t2 with
    | TyParam i, TyParam j when i = j -> H.object_ty
    | _ -> H.lub classes t1 t2
let check_10330 = H.make_check ~lub:lub_10330 ()

let lub_10601 bounds classes t1 t2 =
    match t1, t2 with
    | TyParam i, TyParam j when i = j ->
        (match List.nth_opt bounds i with
         | Some (TyClass (_, _ :: _) as b) -> b
         | _ -> H.lub classes t1 t2)
    | _ -> H.lub classes t1 t2
let check_10601 = H.make_check ~lub:lub_10601 ()

let contain_10337 recur v x y =
    match y with
    | Wild (Covariant, t) ->
        (match x with
         | Wild _ -> H.correct_contain recur v x y
         | _ -> H.type_equal x t)
    | _ -> H.correct_contain recur v x y
let xsub_10337 = H.mk_subtype H.correct_tparam_bound contain_10337
let check_10337 = H.make_check ~is_subtype:xsub_10337 ()

let rec lookup_10364 classes methods cr args ml =
    match cr with
    | Prelude n ->
        (match H.prelude_method_sig (n, ml) with
         | Some (ps, ret) ->
             Some ([], List.map (H.subst_typaram args) ps, H.subst_typaram args ret)
         | None ->
             match H.prelude_parent n with
             | None -> None
             | Some p -> lookup_10364 classes methods p [] ml)
    | Synth i ->
        (match List.find_opt (fun m ->
            m.cm_class = i && m.cm_label = ml) methods with
         | Some m ->
             Some (List.map (fun tp -> H.subst_typaram args tp.tp_bound) m.cm_tparams,
                   List.map snd m.cm_params,
                   H.subst_typaram args m.cm_return)
         | None ->
             match H.class_of classes i with
             | None -> None
             | Some ce ->
                 let (pcr, pa) = ce.cc_parent in
                 lookup_10364 classes methods pcr
                     (List.map (H.subst_typaram args) pa) ml)
let check_10364 = H.make_check ~lookup:lookup_10364 ()

let tparam_bound_10629 recur bounds i sup =
    match List.nth_opt bounds i with
    | Some (TyParam j)
      when (match List.nth_opt bounds j with
            | Some b -> not (H.type_equal b H.object_ty)
            | None -> false) -> false
    | Some bd -> recur bd sup
    | None -> false
let xsub_10629 = H.mk_subtype tparam_bound_10629 H.correct_contain
let check_10629 = H.make_check ~is_subtype:xsub_10629 ()

let check_10222 = H.make_check ~target_infer_invoke:false ()

let rec resolve_invoke_10631 classes cons = function
    | MTParam i ->
        (match List.assoc_opt i cons with Some t -> t | None -> H.object_ty)
    | TyClass (cr, args) -> TyClass (cr, List.map (resolve_invoke_10631 classes cons) args)
    | Wild (v, t) -> Wild (v, resolve_invoke_10631 classes cons t)
    | t -> t
let check_10631 = H.make_check ~resolve_invoke:resolve_invoke_10631 ()

let resolve_new_10754 classes cons ty =
    let mentions j t =
        let rec go = function
            | TyParam k -> k = j
            | TyClass (_, a) -> List.exists go a
            | Wild (_, t) -> go t
            | TyArray t -> go t
            | _ -> false in
        go t in
    match ty with
    | TyClass (cr, args) ->
        let tbs = H.tparam_bounds_of classes cr in
        let referenced i =
            List.exists (fun (k, b) -> k <> i && mentions i b)
                (List.mapi (fun k b -> (k, b)) tbs) in
        TyClass (cr, List.mapi (fun i a ->
            match a with
            | Hole _ when i < List.length tbs && referenced i ->
                H.resolve_holes classes cons (List.nth tbs i)
            | _ -> H.resolve_holes classes cons a) args)
    | _ -> H.resolve_holes classes cons ty
let check_10754 = H.make_check ~resolve_new:resolve_new_10754 ()

let lub_47231 _bounds classes t1 t2 =
    match t1 with
    | TyClass (c1, [Wild (Contravariant, _)]) when H.type_equal t1 t2 ->
        TyClass (c1, [Wild (Covariant, H.object_ty)])
    | _ -> H.lub classes t1 t2
let check_47231 = H.make_check ~lub:lub_47231 ()

let check_10614 = H.make_check ~cond_push:false ()

let erase = function
    | TyClass (cr, (_ :: _ as args)) -> TyClass (cr, List.map (fun _ -> H.object_ty) args)
    | t -> t
let lub_10363 bounds classes t1 t2 =
    match t1, t2 with
    | TyParam i, TyParam j when i = j ->
        (match List.nth_opt bounds i with
         | Some (TyClass (_, _ :: _) as b) -> erase b
         | _ -> H.lub classes t1 t2)
    | _ -> H.lub classes t1 t2
let check_10363 = H.make_check ~lub:lub_10363 ()

let approx_47508 = function Wild _ -> H.object_ty | t -> t
let check_47508 = H.make_check ~approx_field:approx_47508 ()

let contain_10082 recur v x y =
    match y with
    | Wild _ -> H.correct_contain recur v x y
    | _ -> (match v with
        | Invariant -> H.type_equal x y
        | Covariant -> H.type_equal x y
        | Contravariant -> recur y x)
let xsub_10082 = H.mk_subtype H.correct_tparam_bound contain_10082
let check_10082 = H.make_check ~is_subtype:xsub_10082 ()

let lub_10603 _bounds classes t1 t2 =
    match t1, t2 with
    | TyClass _, TyClass _
      when not (H.is_subtype classes t1 t2)
           && not (H.is_subtype classes t2 t1)
           && not (H.type_equal (H.lub classes t1 t2) H.object_ty) ->
        H.object_ty
    | _ -> H.lub classes t1 t2
let check_10603 = H.make_check ~lub:lub_10603 ()

let contain_10267 recur v x y =
    match x, y with
    | Wild (Covariant, sb), Wild (Covariant, tb)
      when H.type_equal sb H.object_ty && H.type_equal tb H.object_ty -> false
    | _ -> H.correct_contain recur v x y
let xsub_10267 = H.mk_subtype H.correct_tparam_bound contain_10267
let check_10267 = H.make_check ~is_subtype:xsub_10267 ()

let rec normalize_10267 = function
    | Wild (Covariant, b) when H.type_equal b H.object_ty -> Wild (Invariant, b)
    | t -> map_type_children normalize_10267 t
let contain_10267_v2 recur v x y =
    match x, y with
    | Wild (Invariant, _), Wild (Covariant, _) -> false
    | _ -> H.correct_contain recur v x y
let check_10267_v2 = H.make_check ~invoke_result:normalize_10267
    ~is_subtype:(H.mk_subtype H.correct_tparam_bound contain_10267_v2) ()

let check_10482_v2 = H.make_check
    ~ctor_arg_infer:(function TyParam _ | MTParam _ -> false | _ -> true) ()

let rec mentions_tvar = function
    | TyParam _ | MTParam _ -> true
    | TyClass (_, args) -> List.exists mentions_tvar args
    | Wild (_, t) | TyArray t -> mentions_tvar t
    | _ -> false

let rec has_tvar_bound_wild = function
    | Wild (_, b) -> mentions_tvar b || has_tvar_bound_wild b
    | TyClass (_, args) -> List.exists has_tvar_bound_wild args
    | TyArray t -> has_tvar_bound_wild t
    | _ -> false

let check_10337_v2 = H.make_check
    ~new_field_filter:(fun ft -> not (has_tvar_bound_wild ft)) ()

let rec has_tvar_bounded_tvar_arg bounds = function
    | TyClass (_, args) ->
        List.exists (fun a ->
            (match a with
             | TyParam i ->
                 (match List.nth_opt bounds i with
                  | Some (TyParam _) -> true
                  | _ -> false)
             | _ -> false)
            || has_tvar_bounded_tvar_arg bounds a) args
    | Wild (_, t) | TyArray t -> has_tvar_bounded_tvar_arg bounds t
    | _ -> false

let check_10364_v2 = H.make_check
    ~invoke_param_filter:(fun bounds pt ->
        not (has_tvar_bounded_tvar_arg bounds pt)) ()

let resolve_invoke_10631_v2 classes cons =
    let rec go = function
        | MTParam i ->
            (match List.rev (List.filter_map
                (fun (j, t) -> if j = i then Some t else None) cons) with
             | [] -> H.object_ty
             | c :: _ -> c)
        | TyClass (cr, args) -> TyClass (cr, List.map go args)
        | Wild (v, t) -> Wild (v, go t)
        | t -> t
    in
    let _ = classes in
    go

let check_10631_v2 = H.make_check ~resolve_invoke:resolve_invoke_10631_v2 ()

let bugs = [
    ("conditional-lub-overwidens-typaram", "heph-rw", 10330, `Deep,
     "GROOVY-10330: the LUB of a conditional whose branches share a type parameter T widens to Object instead of T",
     `Accept, check_10330);
    ("wildcard-extends-containment-too-strict", "heph-rw", 10337, `Deep,
     "GROOVY-10337: '? extends B' containment demands equality with B instead of subtyping, rejecting a valid argument",
     `Accept, check_10337);
    ("method-param-typaram-subst-dropped", "heph-rw", 10364, `Deep,
     "GROOVY-10364: the enclosing class's type argument is not substituted into a method's formal parameter type B<T>",
     `Accept, check_10364);
    ("typaram-not-subtype-of-bound", "heph-rw", 10629, `Deep,
     "GROOVY-10629: a type variable is not treated as a subtype of its declared upper bound (T <: bound(T) missing)",
     `Accept, check_10629);
    ("method-typearg-not-inferred-from-target", "heph-rw", 10222, `Deep,
     "GROOVY-10222: a generic method's type argument is not inferred from the assignment target, leaving the method type variable unresolved",
     `Accept, check_10222);
    ("conditional-lub-widens-to-bound", "heph-rw", 10601, `Deep,
     "GROOVY-10601/10158: the conditional LUB of a bounded type parameter with itself over-widens to its bound instead of returning T",
     `Accept, check_10601);
    ("method-typearg-no-lub-of-args", "heph-rw", 10631, `Deep,
     "GROOVY-10631: a generic method's type argument is not inferred as the least-upper-bound of its argument types, so a wildcard-targeted call is wrongly rejected",
     `Accept, check_10631);
    ("diamond-inference-widened-to-object", "heph-rw", 10754, `Deep,
     "GROOVY-10754: diamond constructor type-argument inference produces Object instead of the inferred argument type",
     `Accept, check_10754);
    ("conditional-lub-flips-in-projection", "heph-rw", 47231, `Deep,
     "KT-47231: the conditional LUB of two identical contravariant (in) use-site projections flips them to a covariant (out) projection",
     `Accept, check_47231);
    ("target-type-not-pushed-through-conditional", "heph-rw", 10614, `Deep,
     "GROOVY-10614: the assignment target type is not propagated into conditional branches, so a diamond in a branch is not target-typed",
     `Accept, check_10614);
    ("conditional-lub-erases-bound-typeargs", "heph-rw", 10363, `Deep,
     "GROOVY-10363: the conditional LUB of a type parameter bounded by a generic type widens to the bound with its type arguments erased to Object",
     `Accept, check_10363);
    ("projection-read-approximates-to-object", "heph-rw", 47508, `Deep,
     "KT-47508: reading a member through a wildcard projection approximates its type to Object instead of the projection's declared upper bound",
     `Accept, check_47508);
    ("covariant-arg-requires-equality", "heph-rw", 10082, `Deep,
     "GROOVY-10082: a covariant type-argument slot is checked with the invariant (equality) rule, rejecting a valid subtype argument",
     `Accept, check_10082);
    ("conditional-lub-overwidens-classes", "heph-rw", 10603, `Deep,
     "GROOVY-10603: the conditional LUB of two distinct classes sharing a common supertype over-widens to Object instead of the nearest common supertype",
     `Accept, check_10603);
    ("wildcard-vs-wildcard-rejected", "heph-rw", 10267, `Deep,
     "GROOVY-10267: a covariant wildcard argument matched against an identical covariant wildcard target is wrongly rejected",
     `Accept, check_10267);
    ("extends-object-normalized-v2", "heph-rw", 10267, `Deep,
     "GROOVY-10267: a call's result type A<? extends Object> is rewritten to A<?>, which is then judged not assignable to A<? extends Object>",
     `Accept, check_10267_v2);
    ("generic-call-arg-not-target-inferred-v2", "heph-rw", 10482, `Deep,
     "GROOVY-10482: a generic method call passed to a constructor parameter of type-variable type does not infer its type argument from that parameter, leaving Object",
     `Accept, check_10482_v2);
    ("ctor-wildcard-tvar-bound-rejected-v2", "heph-rw", 10337, `Deep,
     "GROOVY-10337 (corrected model): a constructor call is rejected whenever a field type contains a wildcard whose bound mentions a type variable",
     `Accept, check_10337_v2);
    ("param-tvar-bounded-typearg-rejected-v2", "heph-rw", 10364, `Deep,
     "GROOVY-10364 (corrected model): a call is rejected when a parameter type uses, as a type argument, an enclosing-scope type variable bounded by another type variable",
     `Accept, check_10364_v2);
    ("method-typearg-first-arg-no-lub-v2", "heph-rw", 10631, `Deep,
     "GROOVY-10631 (corrected model): a generic method's type argument is taken from the first argument's constraint instead of the LUB of all constraints, so calls with heterogeneous arguments are rejected even under a valid target",
     `Accept, check_10631_v2);
]
