open FjPrograms

type fj_type =
    | ObjectType
    | CVar of int
    | ClassType of int

type field_label = int
type method_label = int

type demand =
    | NeedField of fj_type * field_label * fj_type
    | NeedMethod of fj_type * method_label * fj_type list * fj_type
    | FieldCount of fj_type * int
    | Subtype of fj_type * fj_type

type label_kind = LField | LMethod

type label_neq = label_kind * int * int

type proto_term =
    | SFree of int
    | SNew of fj_type * proto_term list
    | SFieldAccess of proto_term * field_label
    | SMethodInvoke of proto_term * method_label * proto_term list

type sym_info = { sym_type : fj_type }

type expr_prototerm = {
    sterm : proto_term;
    styp : fj_type;
    sym_map : sym_info IntMap.t;
    demands : demand list;
    label_neqs : label_neq list;
    next_cvar : int;
    next_sym : int;
    next_field_label : int;
    next_method_label : int;
}

type class_entry = {
    cl_label : int;
    cl_parent : int option;
    cl_fields : (field_label * fj_type) list;
}

type method_entry = {
    mt_class : int;
    mt_label : method_label;
    mt_this_sym : int;
    mt_params : (int * fj_type) list;
    mt_return : fj_type;
    mt_body : expr_prototerm;
}

type program_prototerm = {
    classes : class_entry list;
    methods : method_entry list;
    main : expr_prototerm option;
    all_demands : demand list;
    all_label_neqs : label_neq list;
    next_class_label : int;
    next_cvar : int;
    next_field_label : int;
    next_method_label : int;
}

type fault =
    | BreakDemand of (int * concrete_type) list
    | MutateVar
    | MutateNewClass
    | MutatePerturb of int
    | MutateMethodBody

type tagged_prototerm =
    | ExprPrototerm of expr_prototerm
    | ProgramPrototerm of program_prototerm
    | FaultedProgram of program_prototerm * fault

type config = {
    max_cvars : int;
}

let string_of_type = function
    | ObjectType -> "Object"
    | CVar i -> "?" ^ string_of_int i
    | ClassType c -> cl_name c

let rec string_of_sterm t =
    match t with
    | SFree id -> "x" ^ string_of_int id
    | SNew (typ, []) -> "new " ^ string_of_type typ ^ "()"
    | SNew (typ, args) ->
        "new " ^ string_of_type typ ^ "(" ^
        String.concat ", " (List.map string_of_sterm args) ^ ")"
    | SFieldAccess (e, fl) -> string_of_sterm_recv e ^ "." ^ fl_name fl
    | SMethodInvoke (e, ml, []) -> string_of_sterm_recv e ^ "." ^ ml_name ml ^ "()"
    | SMethodInvoke (e, ml, args) ->
        string_of_sterm_recv e ^ "." ^ ml_name ml ^ "(" ^
        String.concat ", " (List.map string_of_sterm args) ^ ")"

and string_of_sterm_recv t =
    match t with
    | SNew _ -> "(" ^ string_of_sterm t ^ ")"
    | SFree _ | SFieldAccess _ | SMethodInvoke _ -> string_of_sterm t

let string_of_sort = function 0 -> "program" | 1 -> "expr" | _ -> "?"

let string_of_demand = function
    | NeedField (recv, fl, res) ->
        string_of_type recv ^ "." ^ fl_name fl ^ " : " ^ string_of_type res
    | NeedMethod (recv, ml, params, ret) ->
        string_of_type recv ^ "." ^ ml_name ml ^ "("
        ^ String.concat ", " (List.map string_of_type params) ^ ") : "
        ^ string_of_type ret
    | FieldCount (t, k) ->
        "fields(" ^ string_of_type t ^ ") = " ^ string_of_int k
    | Subtype (a, b) ->
        string_of_type a ^ " <: " ^ string_of_type b

let string_of_label_neq (kind, l1, l2) =
    match kind with
    | LField -> fl_name l1 ^ " != " ^ fl_name l2
    | LMethod -> ml_name l1 ^ " != " ^ ml_name l2

let string_of_fault = function
    | BreakDemand fixed ->
        "BreakDemand {" ^ String.concat ", " (List.map (fun (i, t) ->
            "?" ^ string_of_int i ^ " := " ^ string_of_concrete_type t) fixed) ^ "}"
    | MutateVar -> "MutateVar"
    | MutateNewClass -> "MutateNewClass"
    | MutatePerturb k -> "MutatePerturb " ^ string_of_int k
    | MutateMethodBody -> "MutateMethodBody"

let string_of_sym_map sm =
    if IntMap.is_empty sm then "" else
    "  {" ^ String.concat ", " (List.map (fun (id, info) ->
        "x" ^ string_of_int id ^ " : " ^ string_of_type info.sym_type
    ) (IntMap.bindings sm)) ^ "}"

let constraints_block demands neqs =
    match List.map string_of_demand demands
          @ List.map string_of_label_neq neqs with
    | [] -> None
    | ls -> Some (String.concat "\n" ("where:" :: List.map (fun l -> "  " ^ l) ls))

let string_of_expr_prototerm s =
    let base = string_of_sterm s.sterm ^ " : " ^ string_of_type s.styp
               ^ string_of_sym_map s.sym_map in
    match constraints_block s.demands s.label_neqs with
    | None -> base
    | Some cs -> base ^ "\n" ^ cs

let string_of_class_entry ce =
    let parent = match ce.cl_parent with
        | None -> "Object" | Some p -> cl_name p in
    "class " ^ cl_name ce.cl_label ^ " extends " ^ parent ^ " {"
    ^ String.concat "" (List.map (fun (fl, ft) ->
        " " ^ string_of_type ft ^ " " ^ fl_name fl ^ ";") ce.cl_fields)
    ^ " }"

let string_of_method_entry me =
    let params = String.concat ", " (List.map (fun (sid, ty) ->
        string_of_type ty ^ " x" ^ string_of_int sid) me.mt_params) in
    let this_ty = match IntMap.find_opt me.mt_this_sym me.mt_body.sym_map with
        | Some info -> " : " ^ string_of_type info.sym_type
        | None -> "" in
    "  " ^ string_of_type me.mt_return ^ " " ^ ml_name me.mt_label
    ^ "(" ^ params ^ ") [this = x" ^ string_of_int me.mt_this_sym ^ this_ty ^ "]"
    ^ " { return " ^ string_of_sterm me.mt_body.sterm ^ "; }"

let string_of_program_prototerm p =
    let class_blocks = List.map (fun ce ->
        String.concat "\n"
            (string_of_class_entry ce
             :: List.filter_map (fun me ->
                 if me.mt_class <> ce.cl_label then None else
                 Some (string_of_method_entry me)) p.methods)
    ) (List.rev p.classes) in
    let main_block = match p.main with
        | None -> "main: (none)"
        | Some e -> "main: " ^ string_of_sterm e.sterm ^ " : "
                    ^ string_of_type e.styp ^ string_of_sym_map e.sym_map in
    let constraint_blocks =
        match constraints_block p.all_demands p.all_label_neqs with
        | None -> [] | Some cs -> [cs] in
    String.concat "\n\n" (class_blocks @ [main_block] @ constraint_blocks)

let string_of_prototerm = function
    | ExprPrototerm s -> string_of_expr_prototerm s
    | ProgramPrototerm p -> string_of_program_prototerm p
    | FaultedProgram (p, f) ->
        string_of_program_prototerm p ^ "\n\nfault: " ^ string_of_fault f

let dot_node_id t = "\"" ^ string_of_type t ^ "\""

let dot_type_node traits t =
    let tag = match List.assoc_opt t traits with
        | Some lines ->
            Printf.sprintf ", xlabel=<<font point-size=\"9\">%s</font>>"
                (String.concat "<br/>" lines)
        | None -> "" in
    let dash = match t with
        | CVar _ -> ", style=dashed"
        | ObjectType | ClassType _ -> "" in
    Printf.sprintf "    %s [shape=circle%s%s];" (dot_node_id t) dash tag

let fieldcount_traits demands =
    List.fold_left (fun acc d ->
        match d with
        | FieldCount (t, k) ->
            let line = "fields = " ^ string_of_int k in
            (match List.assoc_opt t acc with
             | Some ls -> (t, ls @ [line]) :: List.remove_assoc t acc
             | None -> (t, [line]) :: acc)
        | _ -> acc) [] demands

let rec types_in_sterm = function
    | SFree _ -> []
    | SNew (t, args) -> t :: List.concat_map types_in_sterm args
    | SFieldAccess (e, _) -> types_in_sterm e
    | SMethodInvoke (e, _, args) ->
        types_in_sterm e @ List.concat_map types_in_sterm args

let types_in_demand = function
    | NeedField (r, _, res) -> [r; res]
    | NeedMethod (r, _, _, _) -> [r]
    | FieldCount (t, _) -> [t]
    | Subtype (a, b) -> [a; b]

let types_in_expr s =
    s.styp :: types_in_sterm s.sterm
    @ List.map (fun (_, info) -> info.sym_type) (IntMap.bindings s.sym_map)
    @ List.concat_map types_in_demand s.demands

let dot_cell c = "<td border=\"1\" cellpadding=\"4\">" ^ c ^ "</td>"

let dot_method_node ~dashed j ml ~this_cell ~params ~ret =
    let param_cells = match params with
        | [] -> "<td cellpadding=\"4\">( )</td>"
        | ps -> String.concat "" (List.map dot_cell ps) in
    let corner = match this_cell with
        | Some c ->
            "<td align=\"right\"><font point-size=\"9\" color=\"#555555\">"
            ^ c ^ "</font></td>"
        | None -> "<td></td>" in
    Printf.sprintf
        ("    %s [shape=box%s, label=<<table border=\"0\" cellspacing=\"4\">"
         ^^ "<tr><td align=\"left\"><b>%s</b></td>%s</tr>"
         ^^ "<tr><td colspan=\"2\"><table border=\"0\" cellspacing=\"0\">"
         ^^ "<tr>%s<td cellpadding=\"4\">&#8594;</td>%s</tr>"
         ^^ "</table></td></tr></table>>];")
        j (if dashed then ", style=dashed" else "")
        (ml_name ml) corner param_cells (dot_cell ret)

let dot_demand_edges idx = function
    | Subtype (a, b) ->
        [Printf.sprintf "    %s -> %s [label=\"<:\", style=dashed];"
             (dot_node_id a) (dot_node_id b)]
    | FieldCount _ -> []
    | NeedField (r, fl, res) ->
        [Printf.sprintf "    %s -> %s [label=\".%s\", style=dashed];"
             (dot_node_id r) (dot_node_id res) (fl_name fl)]
    | NeedMethod (r, ml, ps, ret) ->
        let j = Printf.sprintf "\"demand%d\"" idx in
        [dot_method_node ~dashed:true j ml ~this_cell:None
             ~params:(List.map string_of_type ps)
             ~ret:(string_of_type ret);
         Printf.sprintf "    %s -> %s [style=dashed];" (dot_node_id r) j]

let dot_class_edges ce =
    let c = dot_node_id (ClassType ce.cl_label) in
    let parent = match ce.cl_parent with
        | None -> ObjectType | Some p -> ClassType p in
    Printf.sprintf "    %s -> %s [label=\"extends\"];" c (dot_node_id parent)
    :: List.map (fun (fl, ft) ->
           Printf.sprintf "    %s -> %s [label=\".%s\"];"
               c (dot_node_id ft) (fl_name fl)) ce.cl_fields

let dot_decl_method_edges idx me =
    let j = Printf.sprintf "\"decl%d\"" idx in
    let this_cell =
        match IntMap.find_opt me.mt_this_sym me.mt_body.sym_map with
        | Some info ->
            Some (Printf.sprintf "this x%d : %s" me.mt_this_sym
                      (string_of_type info.sym_type))
        | None -> None in
    [dot_method_node ~dashed:false j me.mt_label ~this_cell
         ~params:(List.map (fun (sid, ty) ->
             Printf.sprintf "x%d : %s" sid (string_of_type ty)) me.mt_params)
         ~ret:(string_of_type me.mt_return);
     Printf.sprintf "    %s -> %s;" (dot_node_id (ClassType me.mt_class)) j]

let type_of_concrete = function
    | ConcreteObject -> ObjectType
    | ConcreteClass c -> ClassType c

let dot_recipe_edges fixed =
    List.map (fun (i, ct) ->
        Printf.sprintf
            "    %s -> %s [label=\":=\", color=red, fontcolor=red, penwidth=2];"
            (dot_node_id (CVar i)) (dot_node_id (type_of_concrete ct))) fixed

let dot_graph traits nodes body =
    let node_lines =
        List.map (dot_type_node traits) (List.sort_uniq compare nodes) in
    String.concat "\n"
        (["digraph prototerm {";
          "    rankdir=LR;";
          "    node [fontname=\"Helvetica\", fontsize=11];";
          "    edge [fontname=\"Helvetica\", fontsize=10];"]
         @ node_lines @ body @ ["}"])

let dot_of_expr_prototerm s =
    dot_graph (fieldcount_traits s.demands)
        (types_in_expr s)
        (List.concat (List.mapi dot_demand_edges s.demands))

let dot_of_program_prototerm ?fault p =
    let recipe = match fault with
        | Some (BreakDemand fixed) -> fixed
        | _ -> [] in
    let nodes =
        List.concat_map (fun ce ->
            ClassType ce.cl_label
            :: (match ce.cl_parent with None -> ObjectType | Some pp -> ClassType pp)
            :: List.map snd ce.cl_fields) p.classes
        @ List.map (fun me -> ClassType me.mt_class) p.methods
        @ (match p.main with Some e -> types_in_expr e | None -> [])
        @ List.concat_map types_in_demand p.all_demands
        @ List.concat_map (fun (i, ct) -> [CVar i; type_of_concrete ct]) recipe in
    let body =
        List.concat_map dot_class_edges p.classes
        @ List.concat (List.mapi dot_decl_method_edges p.methods)
        @ List.concat (List.mapi dot_demand_edges p.all_demands)
        @ dot_recipe_edges recipe in
    dot_graph (fieldcount_traits p.all_demands) nodes body

let dot_of_prototerm = function
    | ExprPrototerm s -> dot_of_expr_prototerm s
    | ProgramPrototerm p -> dot_of_program_prototerm p
    | FaultedProgram (p, f) -> dot_of_program_prototerm ~fault:f p
