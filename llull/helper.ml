let rec nats k () = Seq.Cons (k, nats (k + 1))

let rotate_list k = function
    | ([] | [_]) as xs -> xs
    | xs ->
        let arr = Array.of_list xs in
        let len = Array.length arr in
        let k = ((k mod len) + len) mod len in
        List.init len (fun i -> arr.((k + i) mod len))

let rec compositions d k =
    if k <= 1 then [[d]]
    else List.concat (List.init (d + 1) (fun i ->
        List.map (fun rest -> i :: rest) (compositions (d - i) (k - 1))))

let fair_product (s : 'a Seq.t) (k : int) : 'a list Seq.t =
    if k <= 0 then Seq.return []
    else
    let tbl = Hashtbl.create 64 in
    let rest = ref s and filled = ref 0 and len = ref (-1) in
    let get i =
        while !len < 0 && !filled <= i do
            match !rest () with
            | Seq.Nil -> len := !filled
            | Seq.Cons (x, tl) -> Hashtbl.replace tbl !filled x; incr filled; rest := tl
        done;
        if !len >= 0 && i >= !len then None else Hashtbl.find_opt tbl i in
    let rec diagonals d () =
        if !len >= 0 && d > k * (!len - 1) then Seq.Nil
        else
            let tuples = List.filter_map (fun idxs ->
                let elts = List.map get idxs in
                if List.exists (fun o -> o = None) elts then None
                else Some (List.map Option.get elts)) (compositions d k) in
            Seq.append (List.to_seq tuples) (diagonals (d + 1)) () in
    diagonals 0

let rec interleave (seqs : 'a Seq.t list) () =
    match seqs with
    | [] -> Seq.Nil
    | s :: rest ->
        match s () with
        | Seq.Nil -> interleave rest ()
        | Seq.Cons (x, s') -> Seq.Cons (x, interleave (rest @ [s']))
