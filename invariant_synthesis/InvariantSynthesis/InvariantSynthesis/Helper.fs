module Helper

    // Permutations

    let rec insertions x = function
        | []             -> [[x]]
        | (y :: ys) as l -> (x::l)::(List.map (fun x -> y::x) (insertions x ys))

    let rec permutations = function
        | []      -> seq [ [] ]
        | x :: xs -> Seq.concat (Seq.map (insertions x) (permutations xs))

    let all_permutations n =
        permutations (List.init n (fun i -> i))

    let permutation_to_fun lst =
        fun i -> List.item i lst

    let inv_permutation lst =
        List.init (List.length lst) (fun i -> List.findIndex (fun j -> j = i) lst)

    // Seq

    exception SeqEmpty
    let seq_min cmp seq =
        if Seq.isEmpty seq then raise SeqEmpty
        else Seq.fold (fun acc e -> if cmp e acc then e else acc) (Seq.head seq) (Seq.tail seq)

    // List

    let list_set i e lst =
        List.mapi (fun i' e' -> if i = i' then e else e') lst

    let unzip4 lst =
        let rec aux lst (acc1,acc2,acc3,acc4) =
            match lst with
            | [] -> (List.rev acc1,List.rev acc2,List.rev acc3,List.rev acc4)
            | (h1,h2,h3,h4)::lst -> aux lst (h1::acc1,h2::acc2,h3::acc3,h4::acc4)
        aux lst ([],[],[],[])

    // Misc

    let identity a = a

    let order_tuple (a,b) =
        if a < b then (a,b) else (b,a)

    // Mutable Dictionnary

    type System.Collections.Generic.Dictionary<'K, 'V> with
        member x.TryFind(key) =
            match x.TryGetValue(key) with
            | true, v -> Some v
            | _ -> None

