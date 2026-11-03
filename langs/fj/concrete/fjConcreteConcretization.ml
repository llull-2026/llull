open FjPrograms
open FjPrototerms
open FjConcretePrototerms

let render_program (cls : class_entry list) (methods : concrete_method list)
        (main : term) (mty : fj_type) =
    let buf = Buffer.create 128 in
    List.iter (fun ce ->
        let parent_s = match ce.cl_parent with
            | None -> "Object"
            | Some p -> cl_name p
        in
        Buffer.add_string buf ("class " ^ cl_name ce.cl_label ^
            " extends " ^ parent_s ^ " {");
        List.iter (fun (fl, ft) ->
            Buffer.add_string buf
                (" " ^ string_of_ctype ft ^ " " ^ fl_name fl ^ ";")
        ) ce.cl_fields;
        List.iter (fun me ->
            if me.me_class = ce.cl_label then
                Buffer.add_string buf (" " ^ string_of_method me)
        ) (List.rev methods);
        Buffer.add_string buf " }\n"
    ) (List.rev cls);
    Buffer.add_string buf ("main: " ^ string_of_cterm main ^
        " : " ^ string_of_ctype mty);
    Buffer.contents buf

let close_program p =
    if p.cp_main_opt <> None then p else
    { p with cp_main_opt = Some (New (-1, []), ObjectType) }

let to_ctype = function
    | ObjectType -> ConcreteObject
    | ClassType i -> ConcreteClass i
    | CVar _ -> assert false

let to_concrete_class (ce : class_entry) : concrete_class_entry =
    { cc_label = ce.cl_label;
      cc_parent = (match ce.cl_parent with None -> -1 | Some p -> p);
      cc_own_fields = List.map (fun (fl, ft) -> (fl, to_ctype ft)) ce.cl_fields }

let to_concrete_method (me : concrete_method) : concrete_method_entry =
    { cm_class = me.me_class;
      cm_label = me.me_label;
      cm_this_sym = me.me_this;
      cm_params = List.map (fun (j, t) -> (j, to_ctype t)) me.me_params;
      cm_return = to_ctype me.me_ret;
      cm_body = me.me_body }

let concretize ~search_budget:_ (_ : config) s : tagged_fact Seq.t =
    match s with
    | Expr _ -> Seq.empty
    | Prog p ->
        let p = close_program p in
        (match p.cp_main_opt with
         | None -> Seq.empty
         | Some (mt, mty) ->
             Seq.return { tf_classes = List.map to_concrete_class p.cp_classes;
                          tf_methods =
                              List.map to_concrete_method (List.rev p.cp_methods);
                          tf_main_term = mt;
                          tf_main_type = to_ctype mty;
                          tf_bindings = [];
                          tf_rendered =
                              render_program p.cp_classes p.cp_methods mt mty })
