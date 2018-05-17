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

    // Misc

    let identity a = a
