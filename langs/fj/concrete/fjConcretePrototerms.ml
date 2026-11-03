open FjPrograms
open FjPrototerms

type concrete_method = {
    me_class  : int;
    me_label  : int;
    me_this   : int;
    me_params : (int * fj_type) list;
    me_ret    : fj_type;
    me_body   : term;
}

type concrete_program = {
    cp_classes  : class_entry list;
    cp_methods  : concrete_method list;
    cp_main_opt : (term * fj_type) option;
}

type concrete_expr = {
    ce_snapshot : class_entry list;
    ce_methods  : concrete_method list;
    ce_term     : term;
    ce_typ      : fj_type;
    ce_sctx     : fj_type list;
}

type prototerm =
    | Prog of concrete_program
    | Expr of concrete_expr

type config = {
    max_ctx     : int;
    max_classes : int;
    max_methods : int;
}

let string_of_ctype = function
    | ObjectType -> "Object"
    | ClassType i -> cl_name i
    | CVar i -> "?" ^ string_of_int i

let cterm_var_name this i =
    match this with
    | Some j when j = i -> "this"
    | _ -> "x" ^ string_of_int i

let rec string_of_cterm ?this t =
    match t with
    | Var i -> cterm_var_name this i
    | New (-1, []) -> "new Object()"
    | New (-1, args) ->
        "new Object(" ^
        String.concat ", " (List.map (string_of_cterm ?this) args) ^ ")"
    | New (cls, []) -> "new " ^ cl_name cls ^ "()"
    | New (cls, args) ->
        "new " ^ cl_name cls ^ "(" ^
        String.concat ", " (List.map (string_of_cterm ?this) args) ^ ")"
    | FieldAccess (e, fl) -> string_of_cterm_recv ?this e ^ "." ^ fl_name fl
    | MethodInvoke (e, ml, []) ->
        string_of_cterm_recv ?this e ^ "." ^ ml_name ml ^ "()"
    | MethodInvoke (e, ml, args) ->
        string_of_cterm_recv ?this e ^ "." ^ ml_name ml ^ "(" ^
        String.concat ", " (List.map (string_of_cterm ?this) args) ^ ")"
and string_of_cterm_recv ?this = function
    | New _ as t -> "(" ^ string_of_cterm ?this t ^ ")"
    | t -> string_of_cterm ?this t

let string_of_ctx ctx =
    "[" ^ String.concat "; " (List.map string_of_ctype ctx) ^ "]"

let string_of_method me =
    string_of_ctype me.me_ret ^ " " ^ ml_name me.me_label ^ "(" ^
    String.concat ", " (List.map (fun (j, t) ->
        string_of_ctype t ^ " x" ^ string_of_int j) me.me_params) ^
    ") { return " ^ string_of_cterm ~this:me.me_this me.me_body ^ "; }"

let string_of_prototerm = function
    | Prog p ->
        let nc = List.length p.cp_classes in
        let nf = List.fold_left
            (fun acc ce -> acc + List.length ce.cl_fields) 0 p.cp_classes in
        let nm = List.length p.cp_methods in
        let main = match p.cp_main_opt with
            | None -> "<no main>"
            | Some (t, ty) -> string_of_cterm t ^ " : " ^ string_of_ctype ty
        in
        Printf.sprintf "prog{classes=%d fields=%d methods=%d main=%s}"
            nc nf nm main
    | Expr e ->
        let snap = List.length e.ce_snapshot in
        let ctx = if e.ce_sctx = [] then "" else " in " ^ string_of_ctx e.ce_sctx in
        Printf.sprintf "expr{snap=%d}: %s : %s%s"
            snap (string_of_cterm e.ce_term) (string_of_ctype e.ce_typ) ctx

let string_of_sort = function 0 -> "program" | 1 -> "expr" | _ -> "?"
