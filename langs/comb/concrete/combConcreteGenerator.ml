open CombPrograms
open CombConcretePrototerms

type prototerm = CombConcretePrototerms.prototerm
type fact = CombPrograms.fact

type config = CombConcretePrototerms.config

let parse_config kvs =
    let int_of k default = match List.assoc_opt k kvs with
        | Some s -> (match int_of_string_opt s with Some v -> v | None -> default)
        | None -> default in
    { basis_depth = int_of "basis_depth" 1;
      max_ctx = int_of "max_ctx" 2;
      max_tyvars = int_of "max_tyvars" 1;
      no_lists = (List.assoc_opt "no_lists" kvs = Some "true") }

let rec uses_tyvar_at depth = function
    | Int | Unit | ListInt | TVar _ -> false
    | TyVar i -> i = depth
    | Arrow (a, b) -> uses_tyvar_at depth a || uses_tyvar_at depth b
    | Forall body -> uses_tyvar_at (depth + 1) body
    | Ref t -> uses_tyvar_at depth t

type prototerm_key = term * typ * typ list * int
type fact_key = term * typ

let prototerm_key s = (s.sterm, s.styp, s.sctx, s.stylvl)
let fact_key (f : fact) = (f.term, f.typ)
let compare_prototerm_key = compare
let compare_fact_key = compare

let types_wf_at ~no_lists stylvl d =
    CombConcretization.types_up_to_depth_with_tyvars ~no_lists stylvl d

let enumerate_ctxs base_types max_len =
    let by_len = Array.make (max_len + 1) [] in
    by_len.(0) <- [[]];
    for k = 1 to max_len do
        by_len.(k) <-
            List.concat_map (fun ctx ->
                List.map (fun t -> t :: ctx) base_types) by_len.(k - 1)
    done;
    Array.fold_left (fun acc xs -> acc @ xs) [] by_len

type seed_state =
    | NotYet
    | Drained of prototerm list

let initial_seeds = NotYet

let materialize_seeds config =
    let consts =
        if config.no_lists then List.filter (fun c -> not (is_list_const c)) all_consts
        else all_consts in
    List.init (config.max_tyvars + 1) (fun stylvl -> stylvl)
    |> List.concat_map (fun stylvl ->
        let basis = types_wf_at ~no_lists:config.no_lists stylvl config.basis_depth in
        let ctxs = enumerate_ctxs basis config.max_ctx in
        List.concat_map (fun ctx ->
            List.mapi (fun i t ->
                { sterm = Var i; styp = t; sctx = ctx; stylvl }) ctx
            @ List.map (fun c ->
                { sterm = Const c; styp = const_type_of c; sctx = ctx; stylvl })
                consts) ctxs)

let next_seed config st =
    let queue = match st with
        | NotYet -> materialize_seeds config
        | Drained xs -> xs in
    match queue with
    | [] -> None
    | s :: rest -> Some (s, Drained rest)

let sort_count = 1
let prototerm_sort _ = 0
let output_sorts = [0]

let fact_depth = CombPrograms.fact_depth
let fact_nodes = CombPrograms.fact_nodes
let fact_unique_vars = CombPrograms.fact_unique_vars
let prototerm_min_size s = CombPrograms.term_nodes s.sterm

let mk sterm styp sctx stylvl = { sterm; styp; sctx; stylvl }

let rules config : prototerm Language.rule list =
    let r name arity expand =
        (name, List.init arity (fun _ -> 0), 0, (fun _ -> true), expand) in
    [
        r "app" 2 (function
            | [s1; s2] ->
                if s1.sctx <> s2.sctx || s1.stylvl <> s2.stylvl then Seq.empty
                else (match s1.styp with
                      | Arrow (dom, cod) when dom = s2.styp ->
                          Seq.return (mk (App (s1.sterm, s2.sterm)) cod s1.sctx s1.stylvl)
                      | _ -> Seq.empty)
            | _ -> Seq.empty);
        r "lam" 1 (function
            | [s] ->
                (match s.sctx with
                 | head :: rest ->
                     Seq.return
                         (mk (Lam (head, s.sterm)) (Arrow (head, s.styp)) rest s.stylvl)
                 | [] -> Seq.empty)
            | _ -> Seq.empty);
        r "tylam" 1 (function
            | [s] ->
                if s.stylvl < 1 then Seq.empty
                else if List.exists (fun t -> uses_tyvar_at 0 t) s.sctx then Seq.empty
                else
                let sctx' = List.map (shift_tyvar 0 (-1)) s.sctx in
                Seq.return (mk (TyLam s.sterm) (Forall s.styp) sctx' (s.stylvl - 1))
            | _ -> Seq.empty);
        r "tyapp" 1 (function
            | [s] ->
                (match s.styp with
                 | Forall body ->
                     types_wf_at ~no_lists:config.no_lists s.stylvl config.basis_depth
                     |> List.to_seq
                     |> Seq.map (fun t ->
                         mk (TyApp (s.sterm, t)) (subst_tyvar t body) s.sctx s.stylvl)
                 | _ -> Seq.empty)
            | _ -> Seq.empty);
        r "mkref" 1 (function
            | [s] -> Seq.return (mk (MkRef s.sterm) (Ref s.styp) s.sctx s.stylvl)
            | _ -> Seq.empty);
        r "deref" 1 (function
            | [s] ->
                (match s.styp with
                 | Ref inner -> Seq.return (mk (Deref s.sterm) inner s.sctx s.stylvl)
                 | _ -> Seq.empty)
            | _ -> Seq.empty);
        r "assign" 2 (function
            | [s1; s2] ->
                if s1.sctx <> s2.sctx || s1.stylvl <> s2.stylvl then Seq.empty
                else (match s1.styp with
                      | Ref inner when inner = s2.styp ->
                          Seq.return (mk (Assign (s1.sterm, s2.sterm)) Unit s1.sctx s1.stylvl)
                      | _ -> Seq.empty)
            | _ -> Seq.empty);
        r "seq" 2 (function
            | [s1; s2] ->
                if s1.sctx <> s2.sctx || s1.stylvl <> s2.stylvl then Seq.empty
                else if s1.styp <> Unit then Seq.empty
                else Seq.return (mk (Seq (s1.sterm, s2.sterm)) s2.styp s1.sctx s1.stylvl)
            | _ -> Seq.empty);
        r "minus" 2 (function
            | [s1; s2] ->
                if s1.sctx <> s2.sctx || s1.stylvl <> s2.stylvl then Seq.empty
                else if s1.styp <> Int || s2.styp <> Int then Seq.empty
                else Seq.return (mk (Minus (s1.sterm, s2.sterm)) Int s1.sctx s1.stylvl)
            | _ -> Seq.empty);
        r "ifz" 3 (function
            | [s1; s2; s3] ->
                if s1.sctx <> s2.sctx || s1.sctx <> s3.sctx then Seq.empty
                else if s1.stylvl <> s2.stylvl || s1.stylvl <> s3.stylvl then Seq.empty
                else if s1.styp <> Int then Seq.empty
                else if s2.styp <> s3.styp then Seq.empty
                else Seq.return
                    (mk (Ifz (s1.sterm, s2.sterm, s3.sterm)) s2.styp s1.sctx s1.stylvl)
            | _ -> Seq.empty);
    ]

let viable (_ : config) (_ : prototerm) = true

let concretize = CombConcreteConcretization.concretize

let techniques = CombConcreteIllTyped.techniques
