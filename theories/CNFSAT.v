Require Import Coq.micromega.Lia.
Require Import Coq.NArith.BinNat.
Require Import Coq.btauto.Btauto.
Require Import Coq.Lists.List.

Require Import Reduction SAT NPHard.

Import ListNotations.

(* definition of CNFSAT *)

Inductive literal :=
| PosLit : var -> literal
| NegLit : var -> literal
.
Definition clause : Type := list literal.
Definition cnf_formula : Type := list clause.

Definition cnf_formula_size (f : cnf_formula) : nat :=
  fold_left (fun x y => x + y + 1) (map (@length _) f) 0.

Definition satisfies_literal (a : var -> bool) (l : literal) : bool :=
  match l with
  | PosLit v => a v
  | NegLit v => negb (a v)
  end.

Fixpoint satisfies_clause (a : var -> bool) (c : clause) : bool :=
  match c with
  | nil => false
  | l :: c' => satisfies_literal a l || satisfies_clause a c'
  end.

Fixpoint satisfies_cnf_formula (a : var -> bool) (f : cnf_formula) : bool :=
  match f with
  | nil => true
  | c :: f' => satisfies_clause a c && satisfies_cnf_formula a f'
  end.

Definition cnf_satisfiable (f : cnf_formula) : Prop :=
  exists (a : var -> bool), satisfies_cnf_formula a f = true.

Instance CNFSAT : problem cnf_formula :=
  {| ProblemSize := cnf_formula_size;
     ProblemYes := cnf_satisfiable;
  |}.


(* Now for the reduction from SAT. First step: apply demorgans *)

Inductive dm_formula :=
| DMLit : literal -> dm_formula
| DMAnd : dm_formula -> dm_formula -> dm_formula
| DMOr : dm_formula -> dm_formula -> dm_formula
.

Fixpoint satisfies_dm (a : var -> bool) (f : dm_formula) : bool :=
  match f with
  | DMLit l => satisfies_literal a l
  | DMAnd f1 f2 => satisfies_dm a f1 && satisfies_dm a f2
  | DMOr f1 f2 => satisfies_dm a f1 || satisfies_dm a f2
  end.

Definition dm_satisfiable (f : dm_formula) : Prop :=
  exists a, satisfies_dm a f = true.

Fixpoint demorgans (f : formula) : dm_formula :=
  match f with
  | Var v => DMLit (PosLit v)
  | Not f' => demorgans_not f'
  | And f1 f2 => DMAnd (demorgans f1) (demorgans f2)
  | Or f1 f2 => DMOr (demorgans f1) (demorgans f2)
  end
  with demorgans_not (f : formula) : dm_formula :=
         match f with
         | Var v => DMLit (NegLit v)
         | Not f' => demorgans f'
         | And f1 f2 => DMOr (demorgans_not f1) (demorgans_not f2)
         | Or f1 f2 => DMAnd (demorgans_not f1) (demorgans_not f2)
         end.

Lemma demorgans_correct' : forall a f,
    satisfies a f = satisfies_dm a (demorgans f) /\
    satisfies_dm a (demorgans_not f) = negb (satisfies a f).
Proof.
  induction f; cbn; intuition;
    repeat match goal with
           | [ H : _ = _ |- _ ] => rewrite H
           end;
    btauto.
Qed.

Theorem demorgans_correct : forall a f,
    satisfies a f = satisfies_dm a (demorgans f).
Proof.
  apply demorgans_correct'.
Qed.

Corollary demorgans_correct_2 : forall f,
    satisfiable f <-> dm_satisfiable (demorgans f).
Proof.
  intros f.
  split.
  - destruct 1 as [a ?].
    eexists.
    erewrite <-demorgans_correct.
    eassumption.
  - destruct 1 as [a ?].
    eexists.
    erewrite demorgans_correct.
    eassumption.
Qed.

(* Second step: *)

Fixpoint add_lit_to_clauses (l : literal) (f : cnf_formula) : cnf_formula :=
  match f with
  | [] => []
  | c :: f' => (l :: c) :: add_lit_to_clauses l f'
  end.

Fixpoint to_cnf' (n : var) (f : dm_formula) : var * cnf_formula :=
  match f with
  | DMLit l => (n, [[l]])
  | DMAnd f1 f2 => let (n', f1') := to_cnf' n f1 in
                  let (n'', f2') := to_cnf' n' f2 in
                  (n'', f1' ++ f2')
  | DMOr f1 f2 => let (n', f1') := to_cnf' n f1 in
                 let (n'', f2') := to_cnf' n' f2 in
                 let f' := add_lit_to_clauses (PosLit n'') f1'
                        ++ add_lit_to_clauses (NegLit n'') f2' in
                 ((n'' + 1)%N, f')
  end.

Definition lit_var (l : literal) : var :=
  match l with
  | PosLit v => v
  | NegLit v => v
  end.

Fixpoint dm_max_var (f : dm_formula) : var :=
  match f with
  | DMLit l => lit_var l
  | DMAnd f1 f2 => N.max (dm_max_var f1) (dm_max_var f2)
  | DMOr f1 f2 => N.max (dm_max_var f1) (dm_max_var f2)
  end.

Fixpoint clause_max_var (c : clause) : var :=
  match c with
  | [] => 0%N
  | l :: c' => N.max (lit_var l) (clause_max_var c')
  end.

Fixpoint cnf_max_var (f : cnf_formula) : var :=
  match f with
  | [] => 0%N
  | c :: f' => N.max (clause_max_var c) (cnf_max_var f')
  end.

Definition to_cnf (f : dm_formula) : cnf_formula :=
  let n := (dm_max_var f + 1)%N in
  snd (to_cnf' n f).

Lemma satisfies_cnf_formula_app : forall a c1 c2,
    satisfies_cnf_formula a (c1 ++ c2) = (satisfies_cnf_formula a c1 && satisfies_cnf_formula a c2)%bool.
Proof.
  induction c1; cbn; auto.
  intros.
  rewrite IHc1.
  btauto.
Qed.

Lemma cnf_max_var_app : forall c1 c2,
    cnf_max_var (c1 ++ c2) = N.max (cnf_max_var c1) (cnf_max_var c2).
Proof.
  induction c1; cbn; intros.
  - change var with N in *.
    lia.
  - rewrite IHc1.
    change var with N in *.
    lia.
Qed.

Open Scope N_scope.

Lemma cnf_max_var_add_lit_to_clauses : forall l f,
    cnf_max_var (add_lit_to_clauses l f) <= N.max (lit_var l) (cnf_max_var f).
Proof.
  induction f; cbn; lia.
Qed.

Lemma cnf_max_var_add_lit_to_clauses' : forall l f,
    f = nil \/
    cnf_max_var (add_lit_to_clauses l f) = N.max (lit_var l) (cnf_max_var f).
Proof.
  induction f; cbn; auto.
  right.
  change var with N in *.
  destruct l; cbn in *; destruct IHf; subst; cbn; lia.
Qed.

Lemma satisfies_cnf_formula_add_lit_to_clauses_pos_false : forall a v c,
    a v = false ->
    satisfies_cnf_formula a (add_lit_to_clauses (PosLit v) c) = satisfies_cnf_formula a c.
Proof.
  induction c; cbn; auto.
  intros.
  intuition.
  rewrite H, H0.
  btauto.
Qed.

Lemma satisfies_cnf_formula_add_lit_to_clauses_pos_true : forall a v c,
    a v = true ->
    satisfies_cnf_formula a (add_lit_to_clauses (PosLit v) c) = true.
Proof.
  induction c; cbn; auto.
  intuition.
Qed.

Lemma satisfies_cnf_formula_add_lit_to_clauses_neg_false : forall a v c,
    a v = false ->
    satisfies_cnf_formula a (add_lit_to_clauses (NegLit v) c) = true.
Proof.
  induction c; cbn; auto.
  intros.
  rewrite H.
  auto.
Qed.

Lemma satisfies_cnf_formula_add_lit_to_clauses_neg_true : forall a v c,
    a v = true ->
    satisfies_cnf_formula a (add_lit_to_clauses (NegLit v) c) = satisfies_cnf_formula a c.
Proof.
  induction c; cbn; auto.
  intros.
  intuition.
  rewrite H, H0.
  btauto.
Qed.

Lemma satisfies_dm_subst : forall a a' f,
    (forall v, v <= dm_max_var f -> a v = a' v) ->
    satisfies_dm a f = satisfies_dm a' f.
Proof.
  induction f; cbn; intros.
  - destruct l; cbn in *; firstorder.
    rewrite H; auto || lia.
  - rewrite IHf1, IHf2; auto;
      intros; apply H; lia.
  - rewrite IHf1, IHf2; auto;
      intros; apply H; lia.
Qed.

Lemma satisfies_clause_subst : forall a a' c,
    (forall v, v <= clause_max_var c -> a v = a' v) ->
    satisfies_clause a c = satisfies_clause a' c.
Proof.
  induction c; cbn; auto.
  destruct a0; cbn;
    intros;
    rewrite H by lia;
    rewrite IHc by (intros; apply H; lia);
    reflexivity.
Qed.

Lemma satisfies_cnf_subst : forall a a' f,
    (forall v, v <= cnf_max_var f -> a v = a' v) ->
    satisfies_cnf_formula a f = satisfies_cnf_formula a' f.
Proof.
  induction f; cbn; intros; auto.
  rewrite satisfies_clause_subst with (a' := a') by (intros; apply H; lia).
  rewrite IHf by (intros; apply H; lia).
  reflexivity.
Qed.

Lemma to_cnf'_max_var : forall f n,
    let (n', f') := to_cnf' n f in
    dm_max_var f <= cnf_max_var f'.
Proof.
  induction f; cbn.
  - destruct l; intros; lia.
  - intros n.
    specialize (IHf1 n).
    destruct to_cnf'.
    specialize (IHf2 v).
    destruct to_cnf'.
    rewrite cnf_max_var_app.
    lia.
  - intros n.
    specialize (IHf1 n).
    destruct to_cnf'.
    specialize (IHf2 v).
    destruct to_cnf'.
    rewrite cnf_max_var_app.
    pose proof (cnf_max_var_add_lit_to_clauses' (PosLit v0) c).
    pose proof (cnf_max_var_add_lit_to_clauses' (NegLit v0) c0).
    cbn in *.
    destruct H, H0; subst; cbn in *; try lia.
    * rewrite H0.
      lia.
    * rewrite H.
      lia.
    * rewrite H, H0.
      lia.
Qed.

Hint Extern 2 (@eq N _ _) => lia.
Hint Extern 2 (@eq var _ _) => lia.
Hint Extern 2 (N.lt) => lia.
Hint Extern 2 (N.le) => lia.
  
Lemma to_cnf'_correct : forall f n,
    n > dm_max_var f ->
    let (n', f') := to_cnf' n f in
    n' >= n /\
    n' > cnf_max_var f' /\
    (forall a, exists a',
      (forall v, v < n -> a v = a' v) /\
      satisfies_dm a f = satisfies_cnf_formula a' f') /\
    (forall a, satisfies_cnf_formula a f' = true -> satisfies_dm a f = true).
Proof.
  induction f.
  - destruct l; (cbn; intuition; try lia;
      [ exists a;
          intuition;
          btauto
         |]).
    + rewrite Bool.andb_true_r, Bool.orb_false_r in H0.
      assumption.
    + rewrite Bool.andb_true_r, Bool.orb_false_r in H0.
      assumption.
  - cbn.
    intros.
    pose proof (to_cnf'_max_var f1 n).
    specialize (IHf1 n).
    destruct to_cnf'.
    pose proof (to_cnf'_max_var f2 v).
    specialize (IHf2 v).
    destruct (to_cnf' v f2).
    rewrite cnf_max_var_app.
    match goal with
    | [ H : n > dm_max_var f1 -> ?B |- _ ] =>
      assert B as H'1; [apply H; lia |]; clear H
    end.
    destruct H'1 as (? & ? & H''1 & ?).
    match goal with
    | [ H : _ -> ?B |- _ ] =>
      assert B as H'2; [apply H; lia |]; clear H
    end.
    destruct H'2 as (? & ? & H''2 & ?).
    intuition; try lia.
    + destruct (H''1 a) as (a' & Ha1 & Heq1).
      destruct (H''2 a') as (a'' & Ha2 & Heq2).
      exists a''.
      rewrite satisfies_cnf_formula_app.
      intuition.
      * transitivity (a' v1).
        -- apply Ha1.
           lia.
        -- apply Ha2.
           lia.
      * rewrite Heq1.
        rewrite satisfies_dm_subst with (a' := a') by (intros; apply Ha1; lia).
        rewrite Heq2.
        rewrite satisfies_cnf_subst with (a := a') (a' := a'') by (intros; apply Ha2; lia).
        reflexivity.
    + rewrite satisfies_cnf_formula_app in H8.
      auto.
  - cbn.
    intros.
    specialize (IHf1 n).
    destruct to_cnf'.
    specialize (IHf2 v).
    destruct (to_cnf' v f2).
    match goal with
    | [ H : n > dm_max_var f1 -> ?B |- _ ] =>
      assert B as H'1; [apply H; lia |]; clear H
    end.
    destruct H'1 as (? & ? & H''1 & ?).
    match goal with
    | [ H : _ -> ?B |- _ ] =>
      assert B as H'2; [apply H; lia |]; clear H
    end.
    destruct H'2 as (? & ? & H''2 & ?).
    rewrite cnf_max_var_app.
    pose proof (cnf_max_var_add_lit_to_clauses (PosLit v0) c) as H'; cbn in H'.
    pose proof (cnf_max_var_add_lit_to_clauses (NegLit v0) c0) as H''; cbn in H''.
    intuition; try lia.
    + destruct (H''1 a) as (a' & Ha1 & Heq1).
      destruct (H''2 a') as (a'' & Ha2 & Heq2).
      setoid_rewrite satisfies_cnf_formula_app.
      rewrite Heq1.
      rewrite satisfies_dm_subst with (a' := a') by (intros; apply Ha1; lia).
      rewrite Heq2.
      rewrite satisfies_cnf_subst with (a' := a'') by (intros; apply Ha2; lia).
      destruct (satisfies_cnf_formula a'' c) eqn:?.
      * exists (fun v => if N.eq_dec v v0 then false else a'' v).
        intuition.
        -- destruct N.eq_dec; subst; try lia.
           transitivity (a' v1).
           ++ now apply Ha1.
           ++ apply Ha2.
              lia.
        -- rewrite satisfies_cnf_formula_add_lit_to_clauses_neg_false;
             [| destruct N.eq_dec; congruence].
           rewrite satisfies_cnf_formula_add_lit_to_clauses_pos_false;
             [| destruct N.eq_dec; congruence].
           rewrite satisfies_cnf_subst
             with (a := fun v1 => if N.eq_dec v1 v0 then false else a'' v1)
                  (a' := a'')
             by (intros; destruct N.eq_dec; subst; lia || auto).
           rewrite Heqb.
           reflexivity.
      * exists (fun v => if N.eq_dec v v0 then true else a'' v).
        intuition.
        -- destruct N.eq_dec; subst; try lia.
           transitivity (a' v1).
           ++ now apply Ha1.
           ++ apply Ha2.
              lia.
        -- rewrite satisfies_cnf_formula_add_lit_to_clauses_neg_true;
             [| destruct N.eq_dec; congruence].
           rewrite satisfies_cnf_formula_add_lit_to_clauses_pos_true;
             [| destruct N.eq_dec; congruence].
           rewrite satisfies_cnf_subst
             with (a := fun v1 => if N.eq_dec v1 v0 then true else a'' v1)
                  (a' := a'')
             by (intros; destruct N.eq_dec; subst; lia || auto).
           btauto.
    + rewrite satisfies_cnf_formula_app in H6.
      apply andb_prop in H6.
      intuition.
      destruct (a v0) eqn:?.
      * rewrite satisfies_cnf_formula_add_lit_to_clauses_neg_true in H8 by auto.
        rewrite H5 by auto.
        btauto.
      * rewrite satisfies_cnf_formula_add_lit_to_clauses_pos_false in H7 by auto.
        rewrite H2 by auto.
        btauto.
Qed.

Lemma to_cnf_correct : forall f,
    dm_satisfiable f <-> cnf_satisfiable (to_cnf f).
Proof.
  unfold to_cnf.
  intros.
  split; intros.
  - destruct H as [a ?].
    pose proof (to_cnf'_correct f (dm_max_var f + 1)).
    destruct to_cnf'.
    assert (dm_max_var f + 1 > dm_max_var f) by lia.
    intuition.
    destruct (H3 a) as (a' &?&?).
    exists a'.
    cbn.
    congruence.
  - destruct H as [a ?].
    pose proof (to_cnf'_correct f (dm_max_var f + 1)).
    destruct to_cnf'.
    assert (dm_max_var f + 1 > dm_max_var f) by lia.
    intuition.
    exists a.
    apply H5.
    assumption.
Qed.

Definition formula_to_cnf (f : formula) : cnf_formula :=
  to_cnf (demorgans f).

Theorem cnf_sat_is_np_hard : np_hard CNFSAT.
Proof.
  exists formula_to_cnf.
  constructor; auto.
  cbn.
  intros f.
  unfold formula_to_cnf.
  transitivity (dm_satisfiable (demorgans f)).
  - apply demorgans_correct_2.
  - apply to_cnf_correct.
Qed.
