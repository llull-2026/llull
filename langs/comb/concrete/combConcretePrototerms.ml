open CombPrograms

type config = {
    basis_depth : int;
    max_ctx     : int;
    max_tyvars  : int;
    no_lists    : bool;
}

type prototerm = {
    sterm  : term;
    styp   : typ;
    sctx   : typ list;
    stylvl : int;
}

type fact = CombPrograms.fact

let string_of_ctx ctx =
    "[" ^ String.concat "; " (List.map string_of_typ ctx) ^ "]"

let string_of_prototerm s =
    let extra =
        (if s.sctx = [] then "" else " in " ^ string_of_ctx s.sctx) ^
        (if s.stylvl = 0 then "" else " tylvl=" ^ string_of_int s.stylvl) in
    string_of_term s.sterm ^ " : " ^ string_of_typ s.styp ^ extra
