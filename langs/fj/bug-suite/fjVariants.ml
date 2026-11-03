module L = FjPrograms

type tag = TVar | TNew | TFieldAccess | TMethodInvoke

let tag_of (t : L.term) =
    match t with
    | L.Var _          -> TVar
    | L.New _          -> TNew
    | L.FieldAccess _  -> TFieldAccess
    | L.MethodInvoke _ -> TMethodInvoke

let pp_tag = function
    | TVar -> "Var" | TNew -> "New"
    | TFieldAccess -> "FieldAccess" | TMethodInvoke -> "MethodInvoke"

let tag_eq (a : tag) b = a = b

let children (t : L.term) : L.term list =
    match t with
    | L.Var _ -> []
    | L.New (_, args) -> args
    | L.FieldAccess (e, _) -> [e]
    | L.MethodInvoke (recv, _, args) -> recv :: args

let rec collect_parent_child acc t =
    let pt = tag_of t in
    List.iter (fun c ->
        acc := (pt, tag_of c) :: !acc;
        collect_parent_child acc c
    ) (children t)

let term_parent_child_pairs (root : L.term) : (tag * tag) list =
    let acc = ref [] in
    collect_parent_child acc root; !acc

let rec collect_grandparent_grandchild acc grandparent parent t =
    let pt = tag_of t in
    (match grandparent with
     | Some gt -> acc := (gt, pt) :: !acc
     | None -> ());
    List.iter (collect_grandparent_grandchild acc parent (Some pt)) (children t)

let term_grandparent_grandchild_pairs (root : L.term) : (tag * tag) list =
    let acc = ref [] in
    collect_grandparent_grandchild acc None None root; !acc

let rec collect_ancestor_descendant acc ancestors t =
    let dt = tag_of t in
    List.iter (fun a -> acc := (a, dt) :: !acc) ancestors;
    List.iter (collect_ancestor_descendant acc (dt :: ancestors)) (children t)

let term_ancestor_descendant_pairs (root : L.term) : (tag * tag) list =
    let acc = ref [] in
    collect_ancestor_descendant acc [] root; !acc

let parent_of (classes : L.concrete_class_entry list) label =
    match List.find_opt (fun (c : L.concrete_class_entry) -> c.cc_label = label) classes with
    | Some c -> Some c.cc_parent
    | None -> None

let rec ancestors_from classes label =
    match parent_of classes label with
    | None | Some -1 -> []
    | Some p -> p :: ancestors_from classes p

let class_ancestors_of (classes : L.concrete_class_entry list) : (int * int) list =
    List.concat_map (fun (c : L.concrete_class_entry) ->
        List.map (fun a -> (c.cc_label, a)) (ancestors_from classes c.cc_label)
    ) classes

let adapter =
    ((fun (f : L.tagged_fact) -> term_parent_child_pairs f.L.tf_main_term),
     (fun (f : L.tagged_fact) -> term_grandparent_grandchild_pairs f.L.tf_main_term),
     (fun (f : L.tagged_fact) -> term_ancestor_descendant_pairs f.L.tf_main_term),
     (fun (f : L.tagged_fact) -> class_ancestors_of f.L.tf_classes),
     tag_eq,
     (fun (a : int) b -> a = b))

let med id atom = (id, `Medium, Some atom, None)
let hrd id atom = (id, `Hard, Some atom, None)
let cls difficulty n =
    (Printf.sprintf "class-depth>=%d" n, difficulty, None,
     Some (`ClassDepthAtLeast n))

let catalog = [
    med "New-has-Var"  (`Child (TNew,          TVar));
    med "New-has-New"  (`Child (TNew,          TNew));
    med "New-has-FA"   (`Child (TNew,          TFieldAccess));
    med "New-has-MI"   (`Child (TNew,          TMethodInvoke));
    med "FA-has-Var"   (`Child (TFieldAccess,  TVar));
    med "FA-has-New"   (`Child (TFieldAccess,  TNew));
    med "FA-has-FA"    (`Child (TFieldAccess,  TFieldAccess));
    med "FA-has-MI"    (`Child (TFieldAccess,  TMethodInvoke));
    med "MI-has-Var"   (`Child (TMethodInvoke, TVar));
    med "MI-has-New"   (`Child (TMethodInvoke, TNew));
    med "MI-has-FA"    (`Child (TMethodInvoke, TFieldAccess));
    med "MI-has-MI"    (`Child (TMethodInvoke, TMethodInvoke));
    cls `Medium 1;
    hrd "Var-gc-of-New" (`Grandparent (TVar, TNew));
    hrd "Var-gc-of-FA"  (`Grandparent (TVar, TFieldAccess));
    hrd "Var-gc-of-MI"  (`Grandparent (TVar, TMethodInvoke));
    hrd "New-gc-New"   (`Grandchild (TNew,          TNew));
    hrd "New-gc-FA"    (`Grandchild (TNew,          TFieldAccess));
    hrd "New-gc-MI"    (`Grandchild (TNew,          TMethodInvoke));
    hrd "FA-gc-New"    (`Grandchild (TFieldAccess,  TNew));
    hrd "FA-gc-FA"     (`Grandchild (TFieldAccess,  TFieldAccess));
    hrd "FA-gc-MI"     (`Grandchild (TFieldAccess,  TMethodInvoke));
    hrd "MI-gc-New"    (`Grandchild (TMethodInvoke, TNew));
    hrd "MI-gc-FA"     (`Grandchild (TMethodInvoke, TFieldAccess));
    hrd "MI-gc-MI"     (`Grandchild (TMethodInvoke, TMethodInvoke));
    cls `Hard 2;
    cls `Hard 3;
]

let optout (_bug_name : string) (_pattern_id : string) : bool = false
