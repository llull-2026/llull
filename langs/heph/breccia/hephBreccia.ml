open HephPrograms

include BrecciaOutput

let class_ref = function
    | List [Atom "Synth"; i] -> Synth (int_of i)
    | List [Atom "ObjectClass"] -> Prelude "Object"
    | List [Atom "NumberClass"] -> Prelude "Number"
    | List [Atom "IntegerClass"] -> Prelude "Integer"
    | List [Atom "StringClass"] -> Prelude "String"
    | List [Atom "BooleanClass"] -> Prelude "Boolean"
    | List [Atom "FunctionClass"] -> Prelude "Function"
    | x -> bad "class ref" x

let rec ty = function
    | List [Atom "Param"; i] -> TyParam (int_of i)
    | List [Atom "Cls"; c; args] -> TyClass (class_ref c, types args)
    | x -> bad "type" x

and types x = List.map ty (list_of ~cons:"TCons" ~nil:"TNil" x)

let variance = function
    | List [Atom "Inv"] -> Invariant
    | List [Atom "Co"] -> Covariant
    | List [Atom "Contra"] -> Contravariant
    | x -> bad "variance" x

let rec env = function
    | List [Atom "Bind"; x; t; rest] -> (int_of x, ty t) :: env rest
    | List [Atom "Nil"] -> []
    | x -> bad "env" x

let rec term bound = function
    | List [Atom "Var"; _prog; _t; x] ->
        let x = int_of x in
        let rec index i = function
            | [] -> Var x
            | y :: _ when y = x -> BVar i
            | _ :: rest -> index (i + 1) rest in
        index 0 bound
    | List [Atom "New"; t; args] -> New (ty t, terms bound args)
    | List [Atom "Field"; e; f] -> FieldAccess (term bound e, int_of f)
    | List [Atom "Invoke"; e; m; args] ->
        let label = match m with
            | List [Atom "Apply"] -> -1
            | List [Atom "M"; i] -> int_of i
            | x -> bad "method ref" x in
        MethodInvoke (term bound e, label, terms bound args)
    | List [Atom "Lam"; t; x; e] -> Lambda (ty t, term (int_of x :: bound) e)
    | x -> bad "term" x

and terms bound x = List.map (term bound) (list_of ~cons:"ACons" ~nil:"ANil" x)

let program = function
    | List [Atom "Prog"; List [Atom "Table"; cs]; ms] ->
        let decls = Array.of_list (list_of ~cons:"CCons" ~nil:"CNil" cs) in
        let decl i = match decls.(i) with
            | List [Atom "Decl"; tps; parent; fields] ->
                (list_of ~cons:"TPCons" ~nil:"TPNil" tps, ty parent, types fields)
            | x -> bad "class" x in
        let rec inherited i =
            match decl i with
            | (_, TyClass (Synth j, _), _) ->
                let (_, _, fields) = decl j in
                inherited j + List.length fields
            | _ -> 0 in
        let classes = List.init (Array.length decls) (fun i ->
            let (tps, parent, fields) = decl i in
            let tparam = function
                | List [Atom "TP"; v; b] -> { tp_variance = variance v; tp_bound = ty b }
                | x -> bad "type parameter" x in
            let parent = match parent with
                | TyClass (c, args) -> (c, args)
                | _ -> bad "parent" decls.(i) in
            { cc_label = i;
              cc_tparams = List.map tparam tps;
              cc_parent = parent;
              cc_fields = List.mapi (fun j t -> (inherited i + j, t)) fields }) in
        let methods = List.mapi (fun i -> function
            | List [Atom "Meth"; c; this; params; ret; body] ->
                { cm_class = int_of c; cm_label = i; cm_this_sym = int_of this;
                  cm_params = env params; cm_return = ty ret; cm_body = term [] body;
                  cm_tparams = []; cm_default = None }
            | x -> bad "method" x) (list_of ~cons:"MCons" ~nil:"MNil" ms) in
        (classes, methods)
    | x -> bad "program" x

let string_of_class (methods : concrete_method list) (c : concrete_class) =
    let tparams =
        if c.cc_tparams = [] then ""
        else "<" ^ String.concat ", " (List.mapi (fun i tp ->
            string_of_variance tp.tp_variance ^ "P" ^ string_of_int i ^
            " extends " ^ string_of_type tp.tp_bound) c.cc_tparams) ^ ">" in
    let (pc, pargs) = c.cc_parent in
    let fields = List.map (fun (fl, t) -> string_of_type t ^ " " ^ fl_name fl ^ ";")
        c.cc_fields in
    let meths = List.filter_map (fun m ->
        if m.cm_class <> c.cc_label then None
        else Some (string_of_type m.cm_return ^ " " ^ ml_name m.cm_label ^ "(" ^
            String.concat ", " (List.map (fun (x, t) ->
                string_of_type t ^ " x" ^ string_of_int x) m.cm_params) ^
            ") { return " ^ string_of_term m.cm_body ^ "; }")) methods in
    "class " ^ string_of_class_ref (Synth c.cc_label) ^ tparams ^ " extends " ^
    string_of_type (TyClass (pc, pargs)) ^ " {" ^
    String.concat "" (List.map (fun s -> " " ^ s) (fields @ meths)) ^ " }"

let rec free_vars acc = function
    | Var x -> if List.mem x acc then acc else x :: acc
    | BVar _ -> acc
    | New (_, args) -> List.fold_left free_vars acc args
    | FieldAccess (e, _) -> free_vars acc e
    | MethodInvoke (e, _, args) -> List.fold_left free_vars (free_vars acc e) args
    | Lambda (_, e) -> free_vars acc e
    | If (_, c, t, e) -> List.fold_left free_vars acc [c; t; e]

let rec var_types acc = function
    | List [Atom "Var"; _; t; x] -> (int_of x, ty t) :: acc
    | List (Atom "Prog" :: _) -> acc
    | List items -> List.fold_left var_types acc items
    | Atom _ -> acc

let fact_of_heph = function
    | List [Atom "Main"; prog; main] ->
        let (classes, methods) = program prog in
        let main_term = term [] main in
        let types = var_types [] main in
        let bindings = List.sort compare (List.map (fun x -> (x, List.assoc x types))
            (free_vars [] main_term)) in
        let env = { HephTypechecker.free_env =
                        List.fold_left (fun m (x, t) -> IntMap.add x t m) IntMap.empty bindings;
                    bound_env = [] } in
        let main_type = match HephTypechecker.synth_type env classes methods main_term with
            | Some t -> t
            | None -> bad "ill-typed main" main in
        let rendered =
            String.concat "\n" (List.map (string_of_class methods) classes) ^
            (if classes = [] then "" else "\n") ^
            "main: " ^ string_of_term main_term ^ " : " ^ string_of_type main_type in
        { tf_classes = classes; tf_methods = methods; tf_main_term = main_term;
          tf_main_type = main_type; tf_bindings = bindings; tf_rendered = rendered }
    | x -> bad "heph" x

let facts_of_output (s : string) : tagged_fact list =
    List.map (function
        | [h] -> fact_of_heph h
        | row -> bad "HephTracking row" (List row)) (rows "HephTracking" (parse_sexps s))
