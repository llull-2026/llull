open FjPrograms
open BrecciaOutput

type cls = Obj | Sub of int * cls list * cls option

let rec cls = function
    | List [Atom "Object"] -> Obj
    | List [Atom "SubObject"; id; fs] -> Sub (int_of id, fields fs, None)
    | List [Atom "SubOther"; id; fs; sup] -> Sub (int_of id, fields fs, Some (cls sup))
    | x -> bad "class" x
and fields x = List.map cls (list_of ~cons:"FCons" ~nil:"FNil" x)

let class_list x = List.map cls (list_of ~cons:"UCons" ~nil:"UNil" x)

type expr =
    | This of cls
    | V of int * cls
    | Ctor of cls * expr list
    | Field of expr * int
    | Call of expr * int * expr list

let rec expr = function
    | List [Atom "ThisExpr"; c] -> This (cls c)
    | List [Atom "VarExpr"; n; c] -> V (int_of n, cls c)
    | List [Atom "CtorCallExpr"; c; args] -> Ctor (cls c, exprs args)
    | List [Atom "FieldAccessExpr"; e; f] -> Field (expr e, int_of f)
    | List [Atom "MethodCallExpr"; e; m; args] -> Call (expr e, int_of m, exprs args)
    | x -> bad "expression" x
and exprs x = List.map expr (list_of ~cons:"ECons" ~nil:"ENil" x)

type meth = int * cls * cls list * cls * expr

let meth = function
    | List [Atom "FJMethod"; List [Atom "MethodSignature"; n; recv; args; ret]; body] ->
        (int_of n, cls recv, class_list args, cls ret, expr body)
    | x -> bad "method" x

let methods x = List.map meth (list_of ~cons:"MSCons" ~nil:"MSNil" x)

let label_classes (roots : cls list) : (cls * int) list =
    let table = ref [] in
    let rec visit c = match c with
        | Obj -> ()
        | Sub (_, fs, sup) ->
            if not (List.mem_assoc c !table) then begin
                Option.iter visit sup;
                List.iter visit fs;
                if not (List.mem_assoc c !table) then
                    table := (c, List.length !table) :: !table
            end in
    List.iter visit roots;
    List.rev !table

let fact_of_row = function
    | [List [Atom "EWithContext"; e; ms]; _vars; _eclasses; typ] ->
        let main = expr e and ms = methods ms and main_ty = cls typ in
        let rec classes_of = function
            | This c | V (_, c) -> [c]
            | Ctor (c, args) -> c :: List.concat_map classes_of args
            | Field (e, _) -> classes_of e
            | Call (e, _, args) -> classes_of e @ List.concat_map classes_of args in
        let roots = main_ty :: classes_of main
            @ List.concat_map (fun (_, r, ps, ret, b) -> r :: ret :: ps @ classes_of b) ms in
        let labels = label_classes roots in
        let label = function Obj -> -1 | c -> List.assoc c labels in
        let ty = function Obj -> ConcreteObject | c -> ConcreteClass (label c) in
        let free = ref [] in
        let free_sym key c =
            match List.assoc_opt key !free with
            | Some (s, _) -> s
            | None -> let s = List.length !free in free := (key, (s, c)) :: !free; s in
        let rec term ~sym = function
            | This c -> Var (sym `This c)
            | V (n, c) -> Var (sym (`Var n) c)
            | Ctor (c, args) -> New (label c, List.map (term ~sym) args)
            | Field (e, f) -> FieldAccess (term ~sym e, f)
            | Call (e, m, args) -> MethodInvoke (term ~sym e, m, List.map (term ~sym) args) in
        let main_term = term ~sym:(fun k c -> free_sym (k, c) c) main in
        let method_entry (n, recv, params, ret, body) =
            let sym k c = match k with
                | `This -> 0
                | `Var _ ->
                    let rec index i = function
                        | [] -> bad "variable of no parameter class" (Atom "?")
                        | p :: _ when p = c -> i
                        | _ :: rest -> index (i + 1) rest in
                    1 + index 0 params in
            { cm_class = label recv; cm_label = n; cm_this_sym = 0;
              cm_params = List.mapi (fun i p -> (1 + i, ty p)) params;
              cm_return = ty ret; cm_body = term ~sym body } in
        let methods = List.map method_entry ms in
        let class_entry (c, l) = match c with
            | Obj -> assert false
            | Sub (_, fs, sup) ->
                let inherited = match sup with Some (Sub (_, sfs, _)) -> List.length sfs | _ -> 0 in
                { cc_label = l;
                  cc_parent = (match sup with None | Some Obj -> -1 | Some s -> label s);
                  cc_own_fields = List.filteri (fun i _ -> i >= inherited)
                      (List.mapi (fun i f -> (i, ty f)) fs) } in
        let classes = List.map class_entry labels in
        let rec render = function
            | Var s -> "x" ^ string_of_int s
            | New (-1, []) -> "new Object()"
            | New (c, args) -> "new " ^ cl_name c ^ "(" ^ String.concat ", " (List.map render args) ^ ")"
            | FieldAccess (e, f) -> render e ^ "." ^ fl_name f
            | MethodInvoke (e, m, args) ->
                render e ^ "." ^ ml_name m ^ "(" ^ String.concat ", " (List.map render args) ^ ")" in
        let buf = Buffer.create 256 in
        List.iter (fun ce ->
            Buffer.add_string buf (Printf.sprintf "class %s extends %s {" (cl_name ce.cc_label)
                (if ce.cc_parent = -1 then "Object" else cl_name ce.cc_parent));
            let rec all c = if c = -1 then [] else
                let e = List.find (fun e -> e.cc_label = c) classes in all e.cc_parent @ e.cc_own_fields in
            List.iter (fun (f, t) -> Buffer.add_string buf
                (Printf.sprintf " %s %s;" (string_of_concrete_type t) (fl_name f))) (all ce.cc_label);
            Buffer.add_string buf " }\n";
            List.iter (fun m -> if m.cm_class = ce.cc_label then
                Buffer.add_string buf (Printf.sprintf "  %s %s(%s) { return %s; }\n"
                    (string_of_concrete_type m.cm_return) (ml_name m.cm_label)
                    (String.concat ", " (List.map (fun (s, t) ->
                        string_of_concrete_type t ^ " x" ^ string_of_int s) m.cm_params))
                    (render m.cm_body))) methods) classes;
        let bindings = List.rev_map (fun (_, (s, c)) -> (s, ty c)) !free in
        if bindings <> [] then
            Buffer.add_string buf ("with " ^ String.concat ", " (List.map (fun (s, t) ->
                string_of_concrete_type t ^ " x" ^ string_of_int s) bindings) ^ "\n");
        Buffer.add_string buf ("main: " ^ render main_term ^ " : " ^ string_of_concrete_type (ty main_ty));
        { tf_classes = classes; tf_methods = methods; tf_main_term = main_term;
          tf_main_type = ty main_ty; tf_bindings = bindings;
          tf_rendered = Buffer.contents buf }
    | row -> bad "ExpressionWithContextTracking row" (List row)

let facts_of_output (s : string) : tagged_fact list =
    let facts = List.map fact_of_row (rows "ExpressionWithContextTracking" (parse_sexps s)) in
    let ok, rejected = List.partition FjTypechecker.check facts in
    if Sys.getenv_opt "BRECCIA_SHOW_REJECTED" <> None then
        List.iter (fun f -> prerr_endline ("--\n" ^ f.tf_rendered)) rejected;
    Printf.eprintf "[breccia] %d programs; dropped %d the reference typechecker rejects\n%!"
        (List.length facts) (List.length rejected);
    ok
