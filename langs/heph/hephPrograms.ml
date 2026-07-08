module IntMap = Map.Make(Int)
module IntSet = Set.Make(Int)

type class_ref =
    | Prelude of string
    | Synth of int

let class_ref_equal a b =
    match a, b with
    | Prelude n1, Prelude n2 -> n1 = n2
    | Synth i1, Synth i2 -> i1 = i2
    | _ -> false

let string_of_class_ref = function
    | Prelude n -> n
    | Synth i -> "C" ^ string_of_int i

type variance = Invariant | Covariant | Contravariant

let string_of_variance = function
    | Invariant -> ""
    | Covariant -> "+"
    | Contravariant -> "-"

type heph_type =
    | TyClass of class_ref * heph_type list
    | TyParam of int
    | TVar of int
    | TyBot

type field_label = int
type method_label = int

let fl_name i = "f" ^ string_of_int i

type prelude_decl = {
    pr_name : string;
    pr_parent : class_ref option;
}

let prelude : prelude_decl list = [
    { pr_name = "Object";   pr_parent = None };
    { pr_name = "Number";   pr_parent = Some (Prelude "Object") };
    { pr_name = "Integer";  pr_parent = Some (Prelude "Number") };
    { pr_name = "String";   pr_parent = Some (Prelude "Object") };
    { pr_name = "Boolean";  pr_parent = Some (Prelude "Object") };
    { pr_name = "Function"; pr_parent = Some (Prelude "Object") };
]

let prelude_of_name n = List.find_opt (fun p -> p.pr_name = n) prelude

let prelude_parent n =
    match prelude_of_name n with
    | Some p -> p.pr_parent
    | None -> None

let prelude_names = List.map (fun p -> p.pr_name) prelude

let prelude_tparam_variances = function
    | "Function" -> [Contravariant; Covariant]
    | _ -> []

let prelude_method_signature name ml =
    match name, ml with
    | "Function", -1 -> Some ([TyParam 0], TyParam 1)
    | _ -> None

let prelude_methods_on = function
    | "Function" -> [-1]
    | _ -> []

let prelude_method_name = function
    | -1 -> "apply"
    | i -> "m" ^ string_of_int i

let ml_name i =
    if i < 0 then prelude_method_name i
    else "m" ^ string_of_int i

type term =
    | Var of int
    | BVar of int
    | New of heph_type * term list
    | FieldAccess of term * field_label
    | MethodInvoke of term * method_label * term list
    | Lambda of heph_type * term
    | If of heph_type * term * term * term

let rec string_of_type = function
    | TyClass (cr, []) -> string_of_class_ref cr
    | TyClass (cr, args) ->
        string_of_class_ref cr ^ "<" ^
        String.concat ", " (List.map string_of_type args) ^ ">"
    | TyParam i -> "P" ^ string_of_int i
    | TVar i -> "?" ^ string_of_int i
    | TyBot -> "Nothing"

let rec string_of_term t =
    match t with
    | Var id -> "x" ^ string_of_int id
    | BVar i -> "#" ^ string_of_int i
    | New (ty, []) -> "new " ^ string_of_type ty ^ "()"
    | New (ty, args) ->
        "new " ^ string_of_type ty ^ "(" ^
        String.concat ", " (List.map string_of_term args) ^ ")"
    | FieldAccess (e, fl) -> string_of_term_recv e ^ "." ^ fl_name fl
    | MethodInvoke (e, ml, []) -> string_of_term_recv e ^ "." ^ ml_name ml ^ "()"
    | MethodInvoke (e, ml, args) ->
        string_of_term_recv e ^ "." ^ ml_name ml ^ "(" ^
        String.concat ", " (List.map string_of_term args) ^ ")"
    | Lambda (t, body) ->
        "\\:" ^ string_of_type t ^ ". " ^ string_of_term body
    | If (_, c, t, e) ->
        "if (" ^ string_of_term c ^ ") " ^ string_of_term t ^
        " else " ^ string_of_term e

and string_of_term_recv t =
    match t with
    | New _ | Lambda _ | If _ -> "(" ^ string_of_term t ^ ")"
    | _ -> string_of_term t

type tparam_proto_term = {
    tp_variance : variance;
    tp_bound : heph_type;
}

type concrete_method = {
    cm_class : int;
    cm_label : method_label;
    cm_this_sym : int;
    cm_params : (int * heph_type) list;
    cm_return : heph_type;
    cm_body : term;
}

type concrete_class = {
    cc_label : int;
    cc_tparams : tparam_proto_term list;
    cc_parent : class_ref * heph_type list;
    cc_fields : (field_label * heph_type) list;
}

type tagged_fact = {
    tf_classes : concrete_class list;
    tf_methods : concrete_method list;
    tf_main_term : term;
    tf_main_type : heph_type;
    tf_bindings : (int * heph_type) list;
    tf_rendered : string;
}

let fact_nodes (f : tagged_fact) =
    let rec count_term = function
        | Var _ | BVar _ -> 1
        | New (_, args) -> 1 + List.fold_left (fun a t -> a + count_term t) 0 args
        | FieldAccess (e, _) -> 1 + count_term e
        | MethodInvoke (e, _, args) ->
            1 + count_term e + List.fold_left (fun a t -> a + count_term t) 0 args
        | Lambda (_, body) -> 1 + count_term body
        | If (_, c, t, e) -> 1 + count_term c + count_term t + count_term e
    in
    count_term f.tf_main_term

let fact_depth (f : tagged_fact) =
    let rec depth = function
        | Var _ | BVar _ -> 1
        | New (_, args) -> 1 + List.fold_left (fun a t -> max a (depth t)) 0 args
        | FieldAccess (e, _) -> 1 + depth e
        | MethodInvoke (e, _, args) ->
            1 + List.fold_left (fun a t -> max a (depth t)) (depth e) args
        | Lambda (_, body) -> 1 + depth body
        | If (_, c, t, e) -> 1 + max (depth c) (max (depth t) (depth e))
    in
    depth f.tf_main_term

let fact_unique_vars (f : tagged_fact) = List.length f.tf_bindings

let string_of_fact (f : tagged_fact) = f.tf_rendered

let json_escape s =
    let buf = Buffer.create (String.length s + 2) in
    Buffer.add_char buf '"';
    String.iter (fun c ->
        match c with
        | '"'  -> Buffer.add_string buf "\\\""
        | '\\' -> Buffer.add_string buf "\\\\"
        | '\n' -> Buffer.add_string buf "\\n"
        | '\r' -> Buffer.add_string buf "\\r"
        | '\t' -> Buffer.add_string buf "\\t"
        | c when Char.code c < 0x20 ->
            Buffer.add_string buf (Printf.sprintf "\\u%04x" (Char.code c))
        | c    -> Buffer.add_char buf c
    ) s;
    Buffer.add_char buf '"';
    Buffer.contents buf

let json_list items = "[" ^ String.concat "," items ^ "]"

let json_obj pairs =
    "{" ^ String.concat ","
        (List.map (fun (k, v) -> json_escape k ^ ":" ^ v) pairs) ^ "}"

let json_int i = string_of_int i

let json_of_class_ref = function
    | Prelude name ->
        json_obj [("kind", json_escape "Prelude"); ("name", json_escape name)]
    | Synth label ->
        json_obj [("kind", json_escape "Synth"); ("label", json_int label)]

let rec json_of_type = function
    | TyClass (cr, args) ->
        json_obj [
            ("kind", json_escape "Class");
            ("ref", json_of_class_ref cr);
            ("args", json_list (List.map json_of_type args));
        ]
    | TyParam i ->
        json_obj [("kind", json_escape "Param"); ("i", json_int i)]
    | TVar i ->
        json_obj [("kind", json_escape "TVar"); ("i", json_int i)]
    | TyBot ->
        json_obj [("kind", json_escape "Bot")]

let rec json_of_term = function
    | Var sym ->
        json_obj [("kind", json_escape "Var"); ("sym", json_int sym)]
    | BVar i ->
        json_obj [("kind", json_escape "BVar"); ("i", json_int i)]
    | New (t, args) ->
        json_obj [
            ("kind", json_escape "New");
            ("type", json_of_type t);
            ("args", json_list (List.map json_of_term args));
        ]
    | FieldAccess (e, fl) ->
        json_obj [
            ("kind", json_escape "FieldAccess");
            ("obj", json_of_term e);
            ("field", json_int fl);
        ]
    | MethodInvoke (e, ml, args) ->
        json_obj [
            ("kind", json_escape "MethodInvoke");
            ("recv", json_of_term e);
            ("method", json_int ml);
            ("args", json_list (List.map json_of_term args));
        ]
    | Lambda (pt, body) ->
        json_obj [
            ("kind", json_escape "Lambda");
            ("param_type", json_of_type pt);
            ("body", json_of_term body);
        ]
    | If (rty, c, t, e) ->
        json_obj [
            ("kind", json_escape "If");
            ("result_type", json_of_type rty);
            ("cond", json_of_term c);
            ("then", json_of_term t);
            ("else", json_of_term e);
        ]

let json_of_tparam (tp : tparam_proto_term) =
    json_obj [
        ("variance", json_escape (string_of_variance tp.tp_variance));
        ("bound", json_of_type tp.tp_bound);
    ]

let json_of_class (ce : concrete_class) =
    let (parent_ref, parent_args) = ce.cc_parent in
    json_obj [
        ("label", json_int ce.cc_label);
        ("tparams", json_list (List.map json_of_tparam ce.cc_tparams));
        ("parent", json_obj [
            ("ref", json_of_class_ref parent_ref);
            ("args", json_list (List.map json_of_type parent_args));
        ]);
        ("fields", json_list (List.map (fun (fl, ft) ->
            json_obj [("label", json_int fl); ("type", json_of_type ft)]
        ) ce.cc_fields));
    ]

let json_of_method (me : concrete_method) =
    json_obj [
        ("class", json_int me.cm_class);
        ("label", json_int me.cm_label);
        ("this_sym", json_int me.cm_this_sym);
        ("params", json_list (List.map (fun (sid, pt) ->
            json_obj [("sym", json_int sid); ("type", json_of_type pt)]
        ) me.cm_params));
        ("return", json_of_type me.cm_return);
        ("body", json_of_term me.cm_body);
    ]

let json_of_fact f =
    json_obj [
        ("classes", json_list (List.map json_of_class f.tf_classes));
        ("methods", json_list (List.map json_of_method f.tf_methods));
        ("main_term", json_of_term f.tf_main_term);
        ("main_type", json_of_type f.tf_main_type);
        ("bindings", json_list (List.map (fun (sid, t) ->
            json_obj [("sym", json_int sid); ("type", json_of_type t)]
        ) f.tf_bindings));
    ]
