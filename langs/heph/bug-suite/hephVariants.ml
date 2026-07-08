open HephPrograms

type tag = TVar | TBVar | TNew | TFieldAccess | TMethodInvoke | TLambda | TIf

let tag_of (t : term) =
    match t with
    | Var _          -> TVar
    | BVar _         -> TBVar
    | New _          -> TNew
    | FieldAccess _  -> TFieldAccess
    | MethodInvoke _ -> TMethodInvoke
    | Lambda _       -> TLambda
    | If _           -> TIf

let pp_tag = function
    | TVar -> "Var" | TBVar -> "BVar" | TNew -> "New"
    | TFieldAccess -> "FieldAccess" | TMethodInvoke -> "MethodInvoke"
    | TLambda -> "Lambda" | TIf -> "If"

let tag_eq (a : tag) b = a = b

let children (t : term) : term list =
    match t with
    | Var _ | BVar _ -> []
    | New (_, args) -> args
    | FieldAccess (e, _) -> [e]
    | MethodInvoke (recv, _, args) -> recv :: args
    | Lambda (_, body) -> [body]
    | If (_, c, t, e) -> [c; t; e]

let term_parent_child_pairs (root : term) : (tag * tag) list =
    let acc = ref [] in
    let rec go t =
        let pt = tag_of t in
        List.iter (fun c ->
            acc := (pt, tag_of c) :: !acc;
            go c
        ) (children t)
    in
    go root; !acc

let term_grandparent_grandchild_pairs (root : term) : (tag * tag) list =
    let acc = ref [] in
    let rec go grandparent parent t =
        let pt = tag_of t in
        (match grandparent with
         | Some gt -> acc := (gt, pt) :: !acc
         | None -> ());
        List.iter (go parent (Some pt)) (children t)
    in
    go None None root; !acc

let term_ancestor_descendant_pairs (root : term) : (tag * tag) list =
    let acc = ref [] in
    let rec go ancestors t =
        let dt = tag_of t in
        List.iter (fun a -> acc := (a, dt) :: !acc) ancestors;
        let ancestors' = dt :: ancestors in
        List.iter (go ancestors') (children t)
    in
    go [] root; !acc

let cid_of_class_ref (cr : class_ref) : int =
    match cr with
    | Synth i -> i
    | Prelude name ->
        - (Hashtbl.hash name land 0x3FFFFFFF) - 1

let class_ancestors_of (classes : concrete_class list) : (int * int) list =
    let parent_of label =
        match List.find_opt (fun (c : concrete_class) -> c.cc_label = label) classes with
        | Some c -> Some (fst c.cc_parent)
        | None -> None
    in
    let rec ancestors_from (label : int) : int list =
        match parent_of label with
        | None -> []
        | Some cr ->
            let pid = cid_of_class_ref cr in
            (match cr with
             | Synth _ -> pid :: ancestors_from pid
             | Prelude _ -> [pid])
    in
    List.concat_map (fun (c : concrete_class) ->
        List.map (fun a -> (c.cc_label, a)) (ancestors_from c.cc_label)
    ) classes

let adapter =
    ((fun (f : tagged_fact) -> term_parent_child_pairs f.tf_main_term),
     (fun (f : tagged_fact) -> term_grandparent_grandchild_pairs f.tf_main_term),
     (fun (f : tagged_fact) -> term_ancestor_descendant_pairs f.tf_main_term),
     (fun (f : tagged_fact) -> class_ancestors_of f.tf_classes),
     tag_eq,
     (fun (a : int) b -> a = b))

let med id atom = (id, `Medium, Some atom, None)
let hrd id atom = (id, `Hard, Some atom, None)
let cls difficulty n =
    (Printf.sprintf "class-depth>=%d" n, difficulty, None,
     Some (`ClassDepthAtLeast n))

let catalog = [
    med "New-has-Var"    (`Child (TNew,          TVar));
    med "New-has-BVar"   (`Child (TNew,          TBVar));
    med "New-has-New"    (`Child (TNew,          TNew));
    med "New-has-FA"     (`Child (TNew,          TFieldAccess));
    med "New-has-MI"     (`Child (TNew,          TMethodInvoke));
    med "New-has-Lambda" (`Child (TNew,          TLambda));
    med "FA-has-Var"     (`Child (TFieldAccess,  TVar));
    med "FA-has-BVar"    (`Child (TFieldAccess,  TBVar));
    med "FA-has-New"     (`Child (TFieldAccess,  TNew));
    med "FA-has-FA"      (`Child (TFieldAccess,  TFieldAccess));
    med "FA-has-MI"      (`Child (TFieldAccess,  TMethodInvoke));
    med "FA-has-Lambda"  (`Child (TFieldAccess,  TLambda));
    med "MI-has-Var"     (`Child (TMethodInvoke, TVar));
    med "MI-has-BVar"    (`Child (TMethodInvoke, TBVar));
    med "MI-has-New"     (`Child (TMethodInvoke, TNew));
    med "MI-has-FA"      (`Child (TMethodInvoke, TFieldAccess));
    med "MI-has-MI"      (`Child (TMethodInvoke, TMethodInvoke));
    med "MI-has-Lambda"  (`Child (TMethodInvoke, TLambda));
    med "Lambda-has-Var"    (`Child (TLambda, TVar));
    med "Lambda-has-BVar"   (`Child (TLambda, TBVar));
    med "Lambda-has-New"    (`Child (TLambda, TNew));
    med "Lambda-has-FA"     (`Child (TLambda, TFieldAccess));
    med "Lambda-has-MI"     (`Child (TLambda, TMethodInvoke));
    med "Lambda-has-Lambda" (`Child (TLambda, TLambda));
    cls `Medium 1;
    hrd "New-gc-Var"    (`Grandchild (TNew,          TVar));
    hrd "New-gc-BVar"   (`Grandchild (TNew,          TBVar));
    hrd "New-gc-New"    (`Grandchild (TNew,          TNew));
    hrd "New-gc-FA"     (`Grandchild (TNew,          TFieldAccess));
    hrd "New-gc-MI"     (`Grandchild (TNew,          TMethodInvoke));
    hrd "New-gc-Lambda" (`Grandchild (TNew,          TLambda));
    hrd "FA-gc-Var"     (`Grandchild (TFieldAccess,  TVar));
    hrd "FA-gc-BVar"    (`Grandchild (TFieldAccess,  TBVar));
    hrd "FA-gc-New"     (`Grandchild (TFieldAccess,  TNew));
    hrd "FA-gc-FA"      (`Grandchild (TFieldAccess,  TFieldAccess));
    hrd "FA-gc-MI"      (`Grandchild (TFieldAccess,  TMethodInvoke));
    hrd "FA-gc-Lambda"  (`Grandchild (TFieldAccess,  TLambda));
    hrd "MI-gc-Var"     (`Grandchild (TMethodInvoke, TVar));
    hrd "MI-gc-BVar"    (`Grandchild (TMethodInvoke, TBVar));
    hrd "MI-gc-New"     (`Grandchild (TMethodInvoke, TNew));
    hrd "MI-gc-FA"      (`Grandchild (TMethodInvoke, TFieldAccess));
    hrd "MI-gc-MI"      (`Grandchild (TMethodInvoke, TMethodInvoke));
    hrd "MI-gc-Lambda"  (`Grandchild (TMethodInvoke, TLambda));
    hrd "Lambda-gc-Var"    (`Grandchild (TLambda, TVar));
    hrd "Lambda-gc-BVar"   (`Grandchild (TLambda, TBVar));
    hrd "Lambda-gc-New"    (`Grandchild (TLambda, TNew));
    hrd "Lambda-gc-FA"     (`Grandchild (TLambda, TFieldAccess));
    hrd "Lambda-gc-MI"     (`Grandchild (TLambda, TMethodInvoke));
    hrd "Lambda-gc-Lambda" (`Grandchild (TLambda, TLambda));
    cls `Hard 2;
    cls `Hard 3;
]

let optout (_bug_name : string) (_pattern_id : string) : bool = false
