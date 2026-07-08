open CombPrograms
open CombPrototerms
open CombConcretization

type prototerm = CombPrototerms.prototerm
type fact = CombPrograms.fact

type config = CombPrototerms.config

let parse_config kvs =
    let bool_of k default = match List.assoc_opt k kvs with
        | Some "true" -> true | Some "false" -> false | _ -> default in
    { simple_types = bool_of "simple_types" false;
      type_depth_bound =
        (match List.assoc_opt "max_type_depth" kvs with
         | Some s -> int_of_string_opt s | None -> None);
      auto_close = bool_of "auto_close" true;
      no_lists = bool_of "no_lists" false }

let try_app s1 s2 =
    let (s2'', merged_sym) = merge2 s1 s2 in
    match s1.styp with
    | Arrow (dom, cod) ->
        let new_eqs = (dom, s2''.styp) :: s1.type_eqs @ s2''.type_eqs in
        Some { sterm = SApp (s1.sterm, s2''.sterm);
               styp = cod;
               sym_map = merged_sym;
               type_eqs = new_eqs;
               type_neqs = s1.type_neqs @ s2''.type_neqs;
               next_tvar = s2''.next_tvar;
               next_sym = s2''.next_sym }
    | _ ->
        let dom = TVar s2''.next_tvar in
        let cod = TVar (s2''.next_tvar + 1) in
        let new_eqs = (s1.styp, Arrow (dom, cod)) :: (dom, s2''.styp) ::
                      s1.type_eqs @ s2''.type_eqs in
        Some { sterm = SApp (s1.sterm, s2''.sterm);
               styp = cod;
               sym_map = merged_sym;
               type_eqs = new_eqs;
               type_neqs = s1.type_neqs @ s2''.type_neqs;
               next_tvar = s2''.next_tvar + 2;
               next_sym = s2''.next_sym }

let try_lam s =
    let candidate_list = IntMap.bindings s.sym_map in
    let bound_cases = List.map (fun (id, info) ->
        let new_sterm = subst_free_with_bound id info.sym_type 0 s.sterm in
        let new_sym_map = IntMap.remove id s.sym_map in
        { s with
          sterm = SLam (info.sym_type, new_sterm);
          styp = Arrow (info.sym_type, s.styp);
          sym_map = new_sym_map }) candidate_list in
    let free_cases =
        let shifted_sym_map = s.sym_map in
        let existing_tvars = IntSet.elements @@ tvars_in_sym_map shifted_sym_map in
        let same_cases = List.map (fun tv ->
            { s with
              sterm = SLam (TVar tv, s.sterm);
              styp = Arrow (TVar tv, s.styp);
              sym_map = shifted_sym_map }) existing_tvars in
        let fresh = TVar s.next_tvar in
        let neqs = List.map (fun tv -> (fresh, TVar tv)) existing_tvars in
        let diff_case = { s with
            sterm = SLam (fresh, s.sterm);
            styp = Arrow (fresh, s.styp);
            sym_map = shifted_sym_map;
            type_neqs = neqs @ s.type_neqs;
            next_tvar = s.next_tvar + 1 } in
        same_cases @ [diff_case] in
    bound_cases @ free_cases

let rec bind_tvar_as_tyvar tv depth t =
    match t with
    | Int | Unit | ListInt | TyVar _ -> t
    | TVar j -> if j = tv then TyVar depth else t
    | Arrow (t1, t2) -> Arrow (bind_tvar_as_tyvar tv depth t1, bind_tvar_as_tyvar tv depth t2)
    | Forall body -> Forall (bind_tvar_as_tyvar tv (depth + 1) body)
    | Ref t -> Ref (bind_tvar_as_tyvar tv depth t)

let rec bind_tvar_as_tyvar_sterm tv depth t =
    match t with
    | SBound (i, info) ->
        SBound (i, Option.map (fun (id, ty) -> (id, bind_tvar_as_tyvar tv depth ty)) info)
    | SFree _ -> t
    | SLam (ty, body) ->
        SLam (bind_tvar_as_tyvar tv depth ty, bind_tvar_as_tyvar_sterm tv depth body)
    | SApp (t1, t2) ->
        SApp (bind_tvar_as_tyvar_sterm tv depth t1, bind_tvar_as_tyvar_sterm tv depth t2)
    | SConst _ -> t
    | STyLam body -> STyLam (bind_tvar_as_tyvar_sterm tv (depth + 1) body)
    | STyApp (e, ty) ->
        STyApp (bind_tvar_as_tyvar_sterm tv depth e, bind_tvar_as_tyvar tv depth ty)
    | SMkRef e -> SMkRef (bind_tvar_as_tyvar_sterm tv depth e)
    | SDeref e -> SDeref (bind_tvar_as_tyvar_sterm tv depth e)
    | SAssign (e1, e2) ->
        SAssign (bind_tvar_as_tyvar_sterm tv depth e1, bind_tvar_as_tyvar_sterm tv depth e2)
    | SSeq (e1, e2) ->
        SSeq (bind_tvar_as_tyvar_sterm tv depth e1, bind_tvar_as_tyvar_sterm tv depth e2)
    | SMinus (e1, e2) ->
        SMinus (bind_tvar_as_tyvar_sterm tv depth e1, bind_tvar_as_tyvar_sterm tv depth e2)
    | SIfz (e1, e2, e3) ->
        SIfz (bind_tvar_as_tyvar_sterm tv depth e1,
              bind_tvar_as_tyvar_sterm tv depth e2,
              bind_tvar_as_tyvar_sterm tv depth e3)

let bind_tvar_as_tyvar_eq tv depth (t1, t2) =
    (bind_tvar_as_tyvar tv depth t1, bind_tvar_as_tyvar tv depth t2)

let bind_tvar_as_tyvar_prototerm tv s =
    { s with
      sterm = bind_tvar_as_tyvar_sterm tv 0 s.sterm;
      styp = bind_tvar_as_tyvar tv 0 s.styp;
      sym_map = IntMap.map (fun info ->
        { sym_type = bind_tvar_as_tyvar tv 0 info.sym_type }) s.sym_map;
      type_eqs = List.map (bind_tvar_as_tyvar_eq tv 0) s.type_eqs;
      type_neqs = List.map (bind_tvar_as_tyvar_eq tv 0) s.type_neqs }

let try_tylam s =
    let all_tvars = IntSet.elements (tvars_in_prototerm s) in
    let sym_tvars = tvars_in_sym_map s.sym_map in
    let bindable_tvars = List.filter (fun tv -> not (IntSet.mem tv sym_tvars)) all_tvars in
    let bound_cases = List.map (fun tv ->
        let shifted = shift_tyvar_prototerm 0 1 s in
        let replaced = bind_tvar_as_tyvar_prototerm tv shifted in
        { replaced with
          sterm = STyLam replaced.sterm;
          styp = Forall replaced.styp }) bindable_tvars in
    let vacuous =
        let shifted = shift_tyvar_prototerm 0 1 s in
        { shifted with
          sterm = STyLam shifted.sterm;
          styp = Forall shifted.styp } in
    bound_cases @ [vacuous]

let try_tyapp s =
    match s.styp with
    | Forall body ->
        let fresh_arg = TVar s.next_tvar in
        let result_typ = subst_tyvar fresh_arg body in
        let subst_ext t = subst_tyvar fresh_arg t in
        let new_sym_map = IntMap.map (fun info ->
            { sym_type = subst_ext info.sym_type }) s.sym_map in
        let subst_eq (t1, t2) = (subst_ext t1, subst_ext t2) in
        Some { sterm = STyApp (s.sterm, fresh_arg);
               styp = result_typ;
               sym_map = new_sym_map;
               type_eqs = List.map subst_eq s.type_eqs;
               type_neqs = List.map subst_eq s.type_neqs;
               next_tvar = s.next_tvar + 1;
               next_sym = s.next_sym }
    | _ -> None

let try_mkref s =
    Some { s with
           sterm = SMkRef s.sterm;
           styp = Ref s.styp }

let try_deref s =
    match s.styp with
    | Ref inner ->
        Some { s with
               sterm = SDeref s.sterm;
               styp = inner }
    | _ ->
        let alpha = TVar s.next_tvar in
        Some { s with
               sterm = SDeref s.sterm;
               styp = alpha;
               type_eqs = (s.styp, Ref alpha) :: s.type_eqs;
               next_tvar = s.next_tvar + 1 }

let try_assign s1 s2 =
    let (s2'', merged_sym) = merge2 s1 s2 in
    match s1.styp with
    | Ref inner ->
        let new_eqs = (inner, s2''.styp) :: s1.type_eqs @ s2''.type_eqs in
        Some { sterm = SAssign (s1.sterm, s2''.sterm);
               styp = Unit;
               sym_map = merged_sym;
               type_eqs = new_eqs;
               type_neqs = s1.type_neqs @ s2''.type_neqs;
               next_tvar = s2''.next_tvar;
               next_sym = s2''.next_sym }
    | _ ->
        let alpha = TVar s2''.next_tvar in
        let new_eqs = (s1.styp, Ref alpha) :: (alpha, s2''.styp) :: s1.type_eqs @ s2''.type_eqs in
        Some { sterm = SAssign (s1.sterm, s2''.sterm);
               styp = Unit;
               sym_map = merged_sym;
               type_eqs = new_eqs;
               type_neqs = s1.type_neqs @ s2''.type_neqs;
               next_tvar = s2''.next_tvar + 1;
               next_sym = s2''.next_sym }

let try_seq s1 s2 =
    let (s2'', merged_sym) = merge2 s1 s2 in
    let new_eqs = (s1.styp, Unit) :: s1.type_eqs @ s2''.type_eqs in
    Some { sterm = SSeq (s1.sterm, s2''.sterm);
           styp = s2''.styp;
           sym_map = merged_sym;
           type_eqs = new_eqs;
           type_neqs = s1.type_neqs @ s2''.type_neqs;
           next_tvar = s2''.next_tvar;
           next_sym = s2''.next_sym }

let try_minus s1 s2 =
    let (s2'', merged_sym) = merge2 s1 s2 in
    let new_eqs = (s1.styp, Int) :: (s2''.styp, Int) :: s1.type_eqs @ s2''.type_eqs in
    Some { sterm = SMinus (s1.sterm, s2''.sterm);
           styp = Int;
           sym_map = merged_sym;
           type_eqs = new_eqs;
           type_neqs = s1.type_neqs @ s2''.type_neqs;
           next_tvar = s2''.next_tvar;
           next_sym = s2''.next_sym }

let try_ifz s1 s2 s3 =
    let (s2'', s3'', merged_sym) = merge3 s1 s2 s3 in
    let new_eqs = (s1.styp, Int) :: (s2''.styp, s3''.styp) ::
                  s1.type_eqs @ s2''.type_eqs @ s3''.type_eqs in
    Some { sterm = SIfz (s1.sterm, s2''.sterm, s3''.sterm);
           styp = s2''.styp;
           sym_map = merged_sym;
           type_eqs = new_eqs;
           type_neqs = s1.type_neqs @ s2''.type_neqs @ s3''.type_neqs;
           next_tvar = s3''.next_tvar;
           next_sym = s3''.next_sym }

let rec replace_sfree old_id new_id t =
    match t with
    | SBound _ | SConst _ -> t
    | SFree id -> if id = old_id then SFree new_id else t
    | SLam (ty, body) -> SLam (ty, replace_sfree old_id new_id body)
    | SApp (t1, t2) -> SApp (replace_sfree old_id new_id t1, replace_sfree old_id new_id t2)
    | STyLam body -> STyLam (replace_sfree old_id new_id body)
    | STyApp (e, ty) -> STyApp (replace_sfree old_id new_id e, ty)
    | SMkRef e -> SMkRef (replace_sfree old_id new_id e)
    | SDeref e -> SDeref (replace_sfree old_id new_id e)
    | SAssign (e1, e2) -> SAssign (replace_sfree old_id new_id e1, replace_sfree old_id new_id e2)
    | SSeq (e1, e2) -> SSeq (replace_sfree old_id new_id e1, replace_sfree old_id new_id e2)
    | SMinus (e1, e2) -> SMinus (replace_sfree old_id new_id e1, replace_sfree old_id new_id e2)
    | SIfz (e1, e2, e3) -> SIfz (replace_sfree old_id new_id e1, replace_sfree old_id new_id e2, replace_sfree old_id new_id e3)

let max_sharing_syms = 9

let sharing_variants base_next_sym prototerm =
    let all_syms = IntMap.bindings prototerm.sym_map in
    let base_ids = List.filter_map (fun (id, _) ->
        if id < base_next_sym then Some id else None) all_syms in
    let flex_syms = List.filter (fun (id, _) -> id >= base_next_sym) all_syms in
    if List.length all_syms > max_sharing_syms then Seq.return prototerm
    else if flex_syms = [] then Seq.return prototerm
    else
    let rec enumerate available_reps remaining =
        match remaining with
        | [] -> Seq.return []
        | (id, _info) :: rest ->
            let self_combos =
                Seq.map (fun combo -> (id, None) :: combo)
                    (enumerate (id :: available_reps) rest) in
            let join_combos =
                Seq.concat_map (fun rep_id ->
                    Seq.map (fun combo -> (id, Some rep_id) :: combo)
                        (enumerate available_reps rest))
                    (List.to_seq available_reps) in
            Seq.append self_combos join_combos in
    Seq.map (fun assignment ->
        List.fold_left (fun sk (flex_id, target) ->
            match target with
            | None -> sk
            | Some rep_id ->
                let flex_info = IntMap.find flex_id prototerm.sym_map in
                let rep_info = IntMap.find rep_id sk.sym_map in
                let new_sterm = replace_sfree flex_id rep_id sk.sterm in
                let new_sym_map = IntMap.remove flex_id sk.sym_map in
                let new_sym_map = IntMap.add rep_id rep_info new_sym_map in
                let eq = (rep_info.sym_type, flex_info.sym_type) in
                { sk with sterm = new_sterm; sym_map = new_sym_map;
                  type_eqs = eq :: sk.type_eqs }) prototerm assignment
    ) (enumerate base_ids flex_syms)

let sort_count = 1
let prototerm_sort _ = 0
let output_sorts = [0]

type prototerm_key = prototerm_term * typ * type_eq list
type fact_key = term * typ

let prototerm_key s = (s.sterm, s.styp, s.type_neqs)
let fact_key f = (f.term, f.typ)
let compare_prototerm_key = compare
let compare_fact_key = compare

let fact_depth = CombPrograms.fact_depth
let fact_nodes = CombPrograms.fact_nodes
let fact_unique_vars = CombPrograms.fact_unique_vars

let rec sterm_nodes = function
    | SBound _ | SFree _ | SConst _ -> 1
    | SLam (_, body) | STyLam body | SMkRef body | SDeref body ->
        1 + sterm_nodes body
    | STyApp (e, _) -> 1 + sterm_nodes e
    | SApp (e1, e2) | SAssign (e1, e2) | SSeq (e1, e2) | SMinus (e1, e2) ->
        1 + sterm_nodes e1 + sterm_nodes e2
    | SIfz (e1, e2, e3) -> 1 + sterm_nodes e1 + sterm_nodes e2 + sterm_nodes e3

let prototerm_min_size s = sterm_nodes s.sterm

type seed_state = { var_done : bool; const_idx : int }

let initial_seeds = { var_done = false; const_idx = 0 }

let rec next_seed config st =
    if not st.var_done then
        Some (make_var_prototerm (), { st with var_done = true })
    else if st.const_idx < List.length all_consts then
        let c = List.nth all_consts st.const_idx in
        let st' = { st with const_idx = st.const_idx + 1 } in
        if config.no_lists && is_list_const c then next_seed config st'
        else Some (make_const_prototerm c, st')
    else
        None

let rules _config : prototerm Language.rule list =
    let share s1 = function
        | None -> Seq.empty
        | Some sk -> sharing_variants s1.next_sym sk in
    let opt = function None -> Seq.empty | Some sk -> Seq.return sk in
    let r name arity expand =
        (name, List.init arity (fun _ -> 0), 0, (fun _ -> true),
         (fun sks -> expand sks |> Seq.filter_map solve_prototerm)) in
    [
        r "app"    2 (function [s1; s2] -> share s1 (try_app s1 s2) | _ -> Seq.empty);
        r "lam"    1 (function [s] -> List.to_seq (try_lam s) | _ -> Seq.empty);
        r "tylam"  1 (function [s] -> List.to_seq (try_tylam s) | _ -> Seq.empty);
        r "tyapp"  1 (function [s] -> opt (try_tyapp s) | _ -> Seq.empty);
        r "mkref"  1 (function [s] -> opt (try_mkref s) | _ -> Seq.empty);
        r "deref"  1 (function [s] -> opt (try_deref s) | _ -> Seq.empty);
        r "assign" 2 (function [s1; s2] -> share s1 (try_assign s1 s2) | _ -> Seq.empty);
        r "seq"    2 (function [s1; s2] -> share s1 (try_seq s1 s2) | _ -> Seq.empty);
        r "minus"  2 (function [s1; s2] -> share s1 (try_minus s1 s2) | _ -> Seq.empty);
        r "ifz"    3 (function [s1; s2; s3] -> share s1 (try_ifz s1 s2 s3) | _ -> Seq.empty);
    ]

let viable (_ : config) (_ : prototerm) = true

let concretize = CombConcretization.concretize

let techniques = CombIllTyped.techniques
