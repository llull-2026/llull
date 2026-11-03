open HephRwPrograms
module H = HephRwTypechecker

let xsub_10625 =
    let rec sub climbed bounds classes a b =
        if H.type_equal a b then true
        else match a, b with
        | TyBot, _ -> true
        | _, TyBot -> false
        | TyClass (c1, a1), TyClass (c2, a2) ->
            if class_ref_equal c1 c2 then
                let vs = H.tparam_variances_of classes c1 in
                List.length a1 = List.length a2 && List.length a1 = List.length vs &&
                List.for_all2 (fun (x, y) v ->
                    match y with
                    | Wild _ -> H.correct_contain (sub climbed bounds classes) v x y
                    | _ ->
                        (match v with
                         | Invariant ->
                             if climbed then sub climbed bounds classes x y
                             else H.type_equal x y
                         | Covariant -> sub climbed bounds classes x y
                         | Contravariant -> sub climbed bounds classes y x))
                    (List.combine a1 a2) vs
            else
                (match H.parent_of classes c1 with
                 | None -> false
                 | Some (pcr, pargs) ->
                     sub true bounds classes
                         (TyClass (pcr, List.map (H.subst_typaram a1) pargs)) b)
        | TyParam i, TyParam j when i = j -> true
        | TyParam i, _ -> H.correct_tparam_bound (sub climbed bounds classes) bounds i b
        | Wild (Covariant, w), _ -> sub climbed bounds classes w b
        | Wild (_, _), _ -> sub climbed bounds classes H.object_ty b
        | MTParam i, MTParam j when i = j -> true
        | MTParam _, TyClass (Prelude "Object", []) -> true
        | TyArray e1, TyArray e2 -> sub climbed bounds classes e1 e2
        | _ -> false
    in
    fun bounds classes a b -> sub false bounds classes a b
let check_10625 = H.make_check ~is_subtype:xsub_10625 ()

let bounds_10369 top_bounds classes ty =
    let rec ok ty =
        match ty with
        | TyClass (cr, args) ->
            List.for_all ok args
            && (match H.tparam_bounds_of classes cr with
                | [] -> true
                | tb when List.length tb = List.length args ->
                    List.for_all2 (fun b a ->
                        let b' = H.subst_typaram args b in
                        if not (H.type_equal b' b) then true
                        else H.is_subtype ~bounds:top_bounds classes a b') tb args
                | _ -> true)
        | Wild (_, t) -> ok t
        | TyArray t -> ok t
        | _ -> true
    in ok ty
let check_10369 = H.make_check ~type_bounds_ok:bounds_10369 ()

let contain_10371 recur v x y =
    match y, x, v with
    | Wild _, _, _ -> H.correct_contain recur v x y
    | _, Wild (Covariant, s), Invariant -> recur s y
    | _ -> H.correct_contain recur v x y
let xsub_10371 = H.mk_subtype H.correct_tparam_bound contain_10371
let check_10371 = H.make_check ~is_subtype:xsub_10371 ()

let mtparam_sup_10370 _recur _i b =
    match b with TyClass _ -> true | _ -> false
let xsub_10370 =
    H.mk_subtype ~mtparam_sup:mtparam_sup_10370 H.correct_tparam_bound H.correct_contain
let check_10370 = H.make_check ~is_subtype:xsub_10370 ()

let check_10251 = H.make_check ~check_mbounds:false ()

let new_arity_9960 cr nargs total own =
    nargs = total
    || (nargs = 0 && own = 0 && total > 0
        && (match cr with Synth _ -> true | _ -> false))
let check_9960 = H.make_check ~new_arity_ok:new_arity_9960 ()

let check_10277 = H.make_check ~lambda_result_check:false ()

let check_9994 = H.make_check ~array_elem_relax:true ()
let check_9952 = H.make_check ~typaram_field_check:false ()
let check_10094 = H.make_check ~check_default:false ()

let xsub_10625_v2 =
    let is_tvar = function TyParam _ | MTParam _ -> true | _ -> false in
    let rec sub climbed bounds classes a b =
        if H.type_equal a b then true
        else match a, b with
        | TyBot, _ -> true
        | _, TyBot -> false
        | TyClass (c1, a1), TyClass (c2, a2) ->
            if class_ref_equal c1 c2 then
                let vs = H.tparam_variances_of classes c1 in
                List.length a1 = List.length a2 && List.length a1 = List.length vs &&
                List.for_all2 (fun (x, y) v ->
                    match y with
                    | Wild _ -> H.correct_contain (sub climbed bounds classes) v x y
                    | _ ->
                        (match v with
                         | Invariant ->
                             H.type_equal x y || (climbed && is_tvar y)
                         | Covariant -> sub climbed bounds classes x y
                         | Contravariant -> sub climbed bounds classes y x))
                    (List.combine a1 a2) vs
            else
                (match H.parent_of classes c1 with
                 | None -> false
                 | Some (pcr, pargs) ->
                     sub true bounds classes
                         (TyClass (pcr, List.map (H.subst_typaram a1) pargs)) b)
        | TyParam i, TyParam j when i = j -> true
        | TyParam i, _ -> H.correct_tparam_bound (sub climbed bounds classes) bounds i b
        | Wild (Covariant, w), _ -> sub climbed bounds classes w b
        | Wild (_, _), _ -> sub climbed bounds classes H.object_ty b
        | MTParam i, MTParam j when i = j -> true
        | MTParam _, TyClass (Prelude "Object", []) -> true
        | TyArray e1, TyArray e2 -> sub climbed bounds classes e1 e2
        | _ -> false
    in
    fun bounds classes a b -> sub false bounds classes a b
let check_10625_v2 = H.make_check ~is_subtype:xsub_10625_v2 ()

let bugs = [
    ("invariant-containment-weakened", "heph-rw", 10625, `Deep,
     "GROOVY-10625: an invariant type argument is accepted under subtyping instead of equality, across a supertype climb",
     `Reject, check_10625);
    ("classtable-bound-check-off", "heph-rw", 10369, `Deep,
     "GROOVY-10369: a parameterized type whose argument violates the type-parameter upper bound is accepted",
     `Reject, check_10369);
    ("wildcard-super-containment-too-lax", "heph-rw", 10371, `Deep,
     "GROOVY-10371: '? super T' containment accepts an argument that is not a supertype of T",
     `Reject, check_10371);
    ("generic-method-return-typevar-vs-class", "heph-rw", 10370, `Deep,
     "GROOVY-10370: an unsubstituted generic-method type variable is wrongly accepted as a subtype of an unrelated class in the return-conformance check",
     `Reject, check_10370);
    ("generic-method-inferred-arg-bound-unchecked", "heph-rw", 10251, `Deep,
     "GROOVY-10251/KT-48765: an inferred generic-method type argument that violates the method type-parameter's upper bound is accepted",
     `Reject, check_10251);
    ("new-arity-unchecked", "heph-rw", 9960, `Medium,
     "GROOVY-9960: a constructor call whose argument count does not match the class's fields is accepted (heph models constructor presence as field arity)",
     `Reject, check_9960);
    ("covariant-result-unchecked", "heph-rw", 10277, `Deep,
     "GROOVY-10277: a value in a covariant type-argument position (e.g. a lambda/function result type) is accepted without checking it is a subtype of the expected type",
     `Reject, check_10277);
    ("array-initializer-element-unchecked", "heph-rw", 9994, `Medium,
     "GROOVY-9994/9985: an array initializer element whose type is not a subtype of the array component type is accepted",
     `Reject, check_9994);
    ("typaram-typed-field-init-unchecked", "heph-rw", 9952, `Deep,
     "GROOVY-9952: a value assigned to a field whose type is a type variable is not checked for conformance",
     `Reject, check_9952);
    ("default-value-type-unchecked", "heph-rw", 10094, `Medium,
     "GROOVY-10094: a method parameter's default value is not checked to conform to the parameter's declared type",
     `Reject, check_10094);
    ("climbed-invariant-tvar-unified-v2", "heph-rw", 10625, `Deep,
     "GROOVY-10625 (corrected model): after a supertype climb, an invariant argument slot whose declared argument is a type variable unifies with any actual argument",
     `Reject, check_10625_v2);
]
