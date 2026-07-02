open CombPrograms

type prototerm_term =
    | SBound of int * (int * typ) option
    | SFree of int
    | SLam of typ * prototerm_term
    | SApp of prototerm_term * prototerm_term
    | SConst of const
    | STyLam of prototerm_term
    | STyApp of prototerm_term * typ
    | SMkRef of prototerm_term
    | SDeref of prototerm_term
    | SAssign of prototerm_term * prototerm_term
    | SSeq of prototerm_term * prototerm_term
    | SMinus of prototerm_term * prototerm_term
    | SIfz of prototerm_term * prototerm_term * prototerm_term

type config = {
    simple_types     : bool;
    type_depth_bound : int option;
    auto_close       : bool;
    no_lists         : bool;
}

type sym_info = { sym_type : typ }

type prototerm = {
    sterm : prototerm_term;
    styp : typ;
    sym_map : sym_info IntMap.t;
    type_eqs : type_eq list;
    type_neqs : type_eq list;
    next_tvar : int;
    next_sym : int;
}

let rec string_of_sterm t =
    match t with
    | SBound (i, _) -> string_of_int i
    | SFree id -> "x" ^ string_of_int id
    | SLam (ty, body) -> "lam[" ^ string_of_typ ty ^ "]." ^ string_of_sterm body
    | SApp (t1, t2) ->
        let s1 = match t1 with
            | SLam _ | STyLam _ -> "(" ^ string_of_sterm t1 ^ ")"
            | _ -> string_of_sterm t1 in
        let s2 = match t2 with
            | SApp _ | SLam _ | STyLam _ -> "(" ^ string_of_sterm t2 ^ ")"
            | _ -> string_of_sterm t2 in
        s1 ^ " " ^ s2
    | SConst c -> string_of_const c
    | STyLam body -> "Lam_T." ^ string_of_sterm body
    | STyApp (e, ty) -> string_of_sterm e ^ "[" ^ string_of_typ ty ^ "]"
    | SMkRef e -> "ref " ^ sparen_atom e
    | SDeref e -> "!" ^ sparen_atom e
    | SAssign (e1, e2) -> sparen_atom e1 ^ " := " ^ sparen_atom e2
    | SSeq (e1, e2) -> string_of_sterm e1 ^ "; " ^ string_of_sterm e2
    | SMinus (e1, e2) -> sparen_arith e1 ^ " - " ^ sparen_atom e2
    | SIfz (e1, e2, e3) ->
        "ifz " ^ string_of_sterm e1 ^ " then " ^ string_of_sterm e2 ^
        " else " ^ string_of_sterm e3

and sparen_atom t =
    match t with
    | SBound _ | SFree _ | SConst _ -> string_of_sterm t
    | _ -> "(" ^ string_of_sterm t ^ ")"

and sparen_arith t =
    match t with
    | SBound _ | SFree _ | SConst _ | SMinus _ -> string_of_sterm t
    | _ -> "(" ^ string_of_sterm t ^ ")"

let string_of_sym_map m =
    let bindings = IntMap.bindings m in
    let strs = List.map (fun (id, info) ->
        "x" ^ string_of_int id ^ ":" ^ string_of_typ info.sym_type) bindings in
    "{" ^ String.concat ", " strs ^ "}"

let string_of_prototerm s =
    string_of_sterm s.sterm ^ " : " ^ string_of_typ s.styp ^
    (if IntMap.is_empty s.sym_map then "" else ", " ^ string_of_sym_map s.sym_map)
