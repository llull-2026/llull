type sexp = Atom of string | List of sexp list

let parse_sexps (s : string) : sexp list =
    let n = String.length s in
    let pos = ref 0 in
    let is_space c = c = ' ' || c = '\n' || c = '\t' || c = '\r' in
    let rec skip () = if !pos < n && is_space s.[!pos] then (incr pos; skip ()) in
    let rec one () =
        skip ();
        if s.[!pos] = '(' then begin
            incr pos;
            let items = ref [] in
            skip ();
            while s.[!pos] <> ')' do
                items := one () :: !items;
                skip ()
            done;
            incr pos;
            List (List.rev !items)
        end else begin
            let start = !pos in
            while !pos < n && not (is_space s.[!pos]) && s.[!pos] <> '(' && s.[!pos] <> ')' do
                incr pos
            done;
            Atom (String.sub s start (!pos - start))
        end
    in
    let out = ref [] in
    skip ();
    while !pos < n do
        out := one () :: !out;
        skip ()
    done;
    List.rev !out

let rec string_of_sexp = function
    | Atom a -> a
    | List l -> "(" ^ String.concat " " (List.map string_of_sexp l) ^ ")"

exception Bad of string

let bad what x = raise (Bad (what ^ ": " ^ string_of_sexp x))

let int_of = function Atom a -> int_of_string a | x -> bad "int" x

let rec list_of ~cons ~nil = function
    | List [Atom c; x; rest] when c = cons -> x :: list_of ~cons ~nil rest
    | List (Atom c :: _) when c = nil -> []
    | x -> bad "list" x

let rows rel (output : sexp list) : sexp list list =
    List.concat_map (function
        | List entries ->
            let rec go acc = function
                | List (Atom r :: args) :: Atom "->" :: _ :: rest when r = rel ->
                    go (args :: acc) rest
                | _ :: rest -> go acc rest
                | [] -> List.rev acc in
            go [] entries
        | Atom _ -> []) output

let read_file path =
    let ic = open_in_bin path in
    let s = really_input_string ic (in_channel_length ic) in
    close_in ic;
    s
