module IntMap = Map.Make(Int)
module IntSet = Set.Make(Int)

type term =
    | Var of int
    | New of int * term list
    | FieldAccess of term * int
    | MethodInvoke of term * int * term list

type concrete_type = ConcreteObject | ConcreteClass of int

type concrete_class_entry = {
    cc_label : int;
    cc_parent : int;
    cc_own_fields : (int * concrete_type) list;
}

type concrete_method_entry = {
    cm_class : int;
    cm_label : int;
    cm_this_sym : int;
    cm_params : (int * concrete_type) list;
    cm_return : concrete_type;
    cm_body : term;
}

type tagged_fact = {
    tf_classes : concrete_class_entry list;
    tf_methods : concrete_method_entry list;
    tf_main_term : term;
    tf_main_type : concrete_type;
    tf_bindings : (int * concrete_type) list;
    tf_rendered : string;
}

let fl_name i = "f" ^ string_of_int i
let ml_name i = "m" ^ string_of_int i
let cl_name i = "C" ^ string_of_int i

let rec string_of_term t =
    match t with
    | Var id -> "x" ^ string_of_int id
    | New (-1, []) -> "new Object()"
    | New (-1, args) ->
        "new Object(" ^ String.concat ", " (List.map string_of_term args) ^ ")"
    | New (cls, []) -> "new ?" ^ string_of_int cls ^ "()"
    | New (cls, args) ->
        "new ?" ^ string_of_int cls ^ "(" ^
        String.concat ", " (List.map string_of_term args) ^ ")"
    | FieldAccess (e, fl) -> string_of_term_recv e ^ "." ^ fl_name fl
    | MethodInvoke (e, ml, []) -> string_of_term_recv e ^ "." ^ ml_name ml ^ "()"
    | MethodInvoke (e, ml, args) ->
        string_of_term_recv e ^ "." ^ ml_name ml ^ "(" ^
        String.concat ", " (List.map string_of_term args) ^ ")"

and string_of_term_recv t =
    match t with
    | New _ -> "(" ^ string_of_term t ^ ")"
    | Var _ | FieldAccess _ | MethodInvoke _ -> string_of_term t

let string_of_concrete_type = function
    | ConcreteObject -> "Object" | ConcreteClass i -> cl_name i

let string_of_fact (f : tagged_fact) = f.tf_rendered

let rec term_nodes_fj = function
    | Var _ -> 1
    | New (_, args) ->
        1 + List.fold_left (fun acc a -> acc + term_nodes_fj a) 0 args
    | FieldAccess (e, _) -> 1 + term_nodes_fj e
    | MethodInvoke (e, _, args) ->
        1 + term_nodes_fj e
          + List.fold_left (fun acc a -> acc + term_nodes_fj a) 0 args

let rec term_depth_fj = function
    | Var _ -> 1
    | New (_, args) ->
        1 + List.fold_left (fun acc a -> max acc (term_depth_fj a)) 0 args
    | FieldAccess (e, _) -> 1 + term_depth_fj e
    | MethodInvoke (e, _, args) ->
        1 + List.fold_left (fun acc a -> max acc (term_depth_fj a))
                (term_depth_fj e) args
