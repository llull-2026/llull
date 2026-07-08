module C = CombPrograms

type tag =
    | TVar | TLam | TApp | TConst
    | TTyLam | TTyApp
    | TMkRef | TDeref | TAssign | TSeq
    | TMinus | TIfz

let tag_of (t : C.term) =
    match t with
    | C.Var _      -> TVar
    | C.Lam _      -> TLam
    | C.App _      -> TApp
    | C.Const _    -> TConst
    | C.TyLam _    -> TTyLam
    | C.TyApp _    -> TTyApp
    | C.MkRef _    -> TMkRef
    | C.Deref _    -> TDeref
    | C.Assign _   -> TAssign
    | C.Seq _      -> TSeq
    | C.Minus _    -> TMinus
    | C.Ifz _      -> TIfz

let pp_tag = function
    | TVar -> "Var" | TLam -> "Lam" | TApp -> "App" | TConst -> "Const"
    | TTyLam -> "TyLam" | TTyApp -> "TyApp"
    | TMkRef -> "MkRef" | TDeref -> "Deref" | TAssign -> "Assign" | TSeq -> "Seq"
    | TMinus -> "Minus" | TIfz -> "Ifz"

let tag_eq (a : tag) b = a = b

let children (t : C.term) : C.term list =
    match t with
    | C.Var _ | C.Const _ -> []
    | C.Lam (_, body) -> [body]
    | C.App (m, n) -> [m; n]
    | C.TyLam body -> [body]
    | C.TyApp (e, _) -> [e]
    | C.MkRef e -> [e]
    | C.Deref e -> [e]
    | C.Assign (e1, e2) -> [e1; e2]
    | C.Seq (e1, e2) -> [e1; e2]
    | C.Minus (e1, e2) -> [e1; e2]
    | C.Ifz (e1, e2, e3) -> [e1; e2; e3]

let parent_child_pairs (f : C.fact) : (tag * tag) list =
    let acc = ref [] in
    let rec go t =
        let pt = tag_of t in
        List.iter (fun c ->
            acc := (pt, tag_of c) :: !acc;
            go c) (children t) in
    go f.C.term;
    !acc

let grandparent_grandchild_pairs (f : C.fact) : (tag * tag) list =
    let acc = ref [] in
    let rec go grandparent parent t =
        let pt = tag_of t in
        (match grandparent with
         | Some gt -> acc := (gt, pt) :: !acc
         | None -> ());
        List.iter (go parent (Some pt)) (children t) in
    go None None f.C.term;
    !acc

let ancestor_descendant_pairs (f : C.fact) : (tag * tag) list =
    let acc = ref [] in
    let rec go ancestors t =
        let dt = tag_of t in
        List.iter (fun a -> acc := (a, dt) :: !acc) ancestors;
        let ancestors' = dt :: ancestors in
        List.iter (go ancestors') (children t) in
    go [] f.C.term;
    !acc

let cid_eq () () = true

let adapter =
    (parent_child_pairs, grandparent_grandchild_pairs, ancestor_descendant_pairs,
     (fun _ -> []), tag_eq, cid_eq)

let catalog = [
    ("parent=Lam",        `Medium, Some (`Parent      (TApp, TLam)),    None);
    ("parent=App",        `Medium, Some (`Parent      (TApp, TApp)),    None);
    ("parent=TyApp",      `Medium, Some (`Parent      (TTyApp, TTyLam)), None);
    ("child=Deref",       `Medium, Some (`Child       (TDeref, TVar)),  None);
    ("child=Assign",      `Medium, Some (`Child       (TAssign, TVar)), None);
    ("grandparent=Lam",   `Hard,   Some (`Grandparent (TApp, TLam)),    None);
    ("grandparent=MkRef", `Hard,   Some (`Grandparent (TVar, TMkRef)),  None);
    ("grandchild=Const",  `Hard,   Some (`Grandchild  (TLam, TConst)),  None);
    ("under-TyLam",       `Medium, Some (`Ancestor    (TApp, TTyLam)),  None);
    ("ref-under-Lam",     `Medium, Some (`Ancestor    (TMkRef, TLam)),  None);
]

let optout (_bug_name : string) (_pattern_id : string) : bool = false
