Lemma clause_to_three_carry_correct : forall cl carry n,
    n > clause_max_var cl -> n > carry -> (length cl >= 2)%nat ->
    let (n', f') := clause_to_three_carry cl carry n in
    n' >= n /\ n' > cnf_max_var f' /\
    Forall (fun cl' => length cl' <= 3%nat) f' /\
    (forall (a : assignment),
        a carry = true ->
        exists (a' : assignment),
          (forall v, v < n -> a v = a' v) /\
          satisfies_clause a cl = satisfies_cnf_formula a' f') /\
    (forall (a : assignment),
        a carry = false ->
        exists (a' : assignment),
          (forall v, v < n -> a v = a' v) /\
          satisfies_cnf_formula a' f' = true) /\
    (forall (a : assignment),
        a carry = true ->
        satisfies_cnf_formula a f' = true ->
          satisfies_clause a cl = true).
