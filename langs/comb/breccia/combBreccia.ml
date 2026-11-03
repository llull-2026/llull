open CombPrograms
open BrecciaOutput

let rec typ = function
    | List [Atom "IntTy"] -> Int
    | List [Atom "UnitTy"] -> Unit
    | List [Atom "ListTy"] -> ListInt
    | List [Atom "Arrow"; a; b] -> Arrow (typ a, typ b)
    | List [Atom "Ref"; a] -> Ref (typ a)
    | List [Atom "Forall"; a] -> Forall (typ a)
    | List [Atom "TyVar"; i] -> TyVar (int_of i)
    | x -> bad "type" x

let const = function
    | List [Atom "CInt"; n] -> CInt (int_of n)
    | List [Atom "CUnit"] -> CUnit
    | List [Atom "CNil"] -> CNil
    | List [Atom "CCons"] -> CCons
    | List [Atom "CHd"] -> CHd
    | List [Atom "CTl"] -> CTl
    | List [Atom "CPlus"] -> CPlus
    | x -> bad "constant" x

let rec term bound = function
    | List [Atom "Var"; _; x] ->
        let x = int_of x in
        let rec index i = function
            | [] -> raise (Bad ("free variable x" ^ string_of_int x))
            | y :: _ when y = x -> Var i
            | _ :: rest -> index (i + 1) rest in
        index 0 bound
    | List [Atom "Lam"; t; x; e] -> Lam (typ t, term (int_of x :: bound) e)
    | List [Atom "App"; e1; e2] -> App (term bound e1, term bound e2)
    | List [Atom "Const"; c] -> Const (const c)
    | List [Atom "TyLam"; e] -> TyLam (term bound e)
    | List [Atom "TyApp"; e; t] -> TyApp (term bound e, typ t)
    | List [Atom "MkRef"; e] -> MkRef (term bound e)
    | List [Atom "Deref"; e] -> Deref (term bound e)
    | List [Atom "Assign"; e1; e2] -> Assign (term bound e1, term bound e2)
    | List [Atom "Seq"; e1; e2] -> Seq (term bound e1, term bound e2)
    | List [Atom "Minus"; e1; e2] -> Minus (term bound e1, term bound e2)
    | List [Atom "Ifz"; e1; e2; e3] -> Ifz (term bound e1, term bound e2, term bound e3)
    | x -> bad "term" x

let fact_of_closed = function
    | List [Atom "Closed"; e] ->
        let t = term [] e in
        (match CombTypechecker.typeof 0 [] t with
         | Some ty -> { term = t; typ = ty; bindings = [] }
         | None -> bad "ill-typed program" e)
    | x -> bad "program" x

let facts_of_output (s : string) : fact list =
    List.map (function
        | [p] -> fact_of_closed p
        | row -> bad "RefMutTracking row" (List row)) (rows "RefMutTracking" (parse_sexps s))
