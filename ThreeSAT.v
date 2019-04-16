Require Import Coq.Bool.Bool.
Require Import Coq.NArith.BinNat.
Require Import Coq.micromega.Lia.
Require Import Coq.btauto.Btauto.
Require Import Coq.Lists.List.
Require Import ExtLib.Structures.Monad.

Require Import Reduction SAT CNFSAT Fresh NPHard.

Import MonadNotation.
Open Scope monad_scope.
Import ListNotations.

Definition threecnf_formula :=
  { f : cnf_formula | Forall (fun c => length c = 3%nat) f}.

Instance ThreeSAT : problem threecnf_formula :=
  {| ProblemSize := fun x => cnf_formula_size (proj1_sig x);
     ProblemYes := fun x => cnf_satisfiable (proj1_sig x);
  |}.

Fixpoint from_many (cl : clause) (carry : var) : Fresh (list clause) :=
  match cl with
  | [] | [_] => ret [] (* error case *)
  | [akm1; ak] => ret [[NegLit carry; akm1; ak]]
  | aip2 :: cl' => xip1 <- fresh ;;
                 rest <- from_many cl' xip1 ;;
                 ret ([NegLit carry; aip2; PosLit xip1] :: rest)
  end.

Definition clause_to_three (cl : clause) : Fresh (list clause) :=
  match cl with
  | [] => x <- fresh ;;
         ret [ [PosLit x; PosLit x; PosLit x]; [NegLit x; NegLit x; NegLit x] ]
  | [a] => x <- fresh ;;
          y <- fresh ;;
          ret [ [a; PosLit x; PosLit y]
              ; [a; NegLit x; PosLit y]
              ; [a; PosLit x; NegLit y]
              ; [a; NegLit x; NegLit y]
              ]
  | [a; b] => x <- fresh ;;
             ret [ [a; b; PosLit x]
                 ; [a; b; NegLit x]
                 ]
  | [a; b; c] => ret [ [a; b; c] ]
  | a :: b :: cl' => x1 <- fresh ;;
                  many <- from_many cl' x1 ;;
                  ret ([a; b; PosLit x1] :: many)
  end.

Fixpoint cnf_to_three'' (f : cnf_formula) : Fresh cnf_formula :=
  match f with
  | nil => ret nil
  | cl :: f' => cl' <- clause_to_three cl ;;
              f'' <- cnf_to_three'' f' ;;
              ret (cl' ++ f'')
  end.

Definition cnf_to_three' (f : cnf_formula) : cnf_formula :=
  snd (cnf_to_three'' f (cnf_max_var f + 1)).

Close Scope nat.
Open Scope N.

Hint Rewrite
orb_false_r (** b || false -> b *)
orb_false_l (** false || b -> b *)
orb_true_r (** b || true -> true *)
orb_true_l (** true || b -> true *)
andb_false_r (** b && false -> false *)
andb_false_l (** false && b -> false *)
andb_true_r (** b && true -> b *)
andb_true_l (** true && b -> b *)
negb_orb (** negb (b || c) -> negb b && negb c *)
negb_andb (** negb (b && c) -> negb b || negb c *)
negb_involutive (** negb( (negb b) -> b *)
: bool_simpl.

Tactic Notation "bool_simpl" :=
  autorewrite with bool_simpl.

Tactic Notation "bool_simpl" "in" "*" :=
  autorewrite with bool_simpl in *.

Lemma satisfies_literal_subst : forall a a' l,
    a (lit_var l) = a' (lit_var l) ->
    satisfies_literal a l = satisfies_literal a' l.
Proof.
  destruct l; cbn; congruence.
Qed.

Lemma from_many_correct : forall cl carry n,
    n > clause_max_var cl ->
    n > carry ->
    (length cl >= 2)%nat ->
    let (n', f') := from_many cl carry n in
    n' >= n /\
    n' > cnf_max_var f' /\
    Forall (fun cl' => length cl' = 3%nat) f' /\
    (forall a,
        a carry = true ->
        exists a',
          (forall v, v < n -> a v = a' v) /\
          satisfies_clause a cl = satisfies_cnf_formula a' f') /\
    (forall a,
        a carry = false ->
        exists a',
          (forall v, v < n -> a v = a' v) /\
          satisfies_cnf_formula a' f' = true) /\
    (forall a, a carry = true -> satisfies_cnf_formula a f' = true -> satisfies_clause a cl = true).
Proof.
  induction cl; intros; [| destruct cl]; [| | destruct cl].
  - destruct from_many; cbn in *; lia.
  - destruct from_many; cbn in *; lia.
  - cbn in *.
    destruct a, l; cbn in *;
      (intuition;
       try lia;
       [ exists a; intuition; cbn; rewrite H2; btauto
       | exists a; intuition; rewrite H2; btauto
       | cbn in *; rewrite H2 in *; bool_simpl in *; auto]).
  - cbv delta [from_many].
    cbv iota.
    fold from_many.
    cbv beta iota.
    remember (l :: l0 :: cl) as cl'.
    cbn.
    specialize (IHcl n (n + 1)).
    destruct from_many.
    cbn in *.
    assert (n > clause_max_var cl') by (destruct a; cbn in *; lia).
    match type of IHcl with
    | _ -> _ -> _ -> ?A =>
      assert A as IH by (apply IHcl; [| | rewrite Heqcl'; cbn; auto]; lia)
    end.
    destruct IH as (?&?&?&?&?).
    intuition; [| destruct a | | |]; try lia.
    + destruct (satisfies_literal a0 a) eqn:?.
      * set (a' := (fun v => if N.eq_dec v n then false else a0 v)).
        destruct (H8 a') as (a'' &?&?); [subst a'; cbn; destruct N.eq_dec; congruence |].
        assert (forall v, v < n -> a0 v = a'' v) as Ha. {
          intros.
          transitivity (a' v); [| apply H10; lia].
          subst a'; cbn.
          destruct N.eq_dec; lia || auto.
        }
        exists a''; intuition.
        rewrite satisfies_literal_subst with (a' := a'') in Heqb by (destruct a; cbn in *; apply Ha; lia).
        rewrite H11, Heqb.
        btauto.
      * set (a' := (fun v => if N.eq_dec v n then true else a0 v)).
        destruct (H6 a') as (a'' &?&?); [subst a'; cbn; destruct N.eq_dec; congruence |].
        assert (forall v, v < n -> a0 v = a'' v) as Ha. {
          intros.
          transitivity (a' v); [| apply H10; lia].
          subst a'; cbn.
          destruct N.eq_dec; lia || auto.
        }
        exists a''; intuition.
        rewrite satisfies_clause_subst with (a' := a') by (intros; subst a'; cbn; destruct N.eq_dec; lia || auto).
        rewrite H11.
        replace (a'' n) with true.
        2: {
          transitivity (a' n).
          { subst a'; cbn.
            destruct N.eq_dec; congruence.
          }
          { apply H10; lia. }
        }
        btauto.
    + set (a' := fun v => if v <? n then a0 v else false).
      destruct (H8 a') as (a'' &?&?); [subst a'; cbn; destruct (N.ltb_spec0 n n); lia || auto |].
      assert (forall v, v < n -> a0 v = a'' v) as Ha. {
        intros.
        transitivity (a' v); [| apply H10; lia].
        subst a'; cbn.
        destruct (N.ltb_spec0 v n); lia || auto.
      }
      exists a''; intuition.
      rewrite H11, <-(Ha carry), H7; [| lia].
      btauto.
    + rewrite H7 in *.
      bool_simpl in *.
      apply andb_prop in H10; intuition.
      apply orb_prop in H11; intuition.
Qed.

Lemma N_max_repeat : forall a b,
    N.max a (N.max a b) = N.max a b.
Proof.
  intros. lia.
Qed.

Lemma implb_prop : forall b1 b2,
    implb b1 b2 = true ->
    (b1 = true -> b2 = true).
Proof.
  destruct b1, b2; auto.
Qed.

Lemma clause_to_three_correct : forall cl n,
    n > clause_max_var cl ->
    let (n', f') := clause_to_three cl n in
    n' >= n /\
    n' > cnf_max_var f' /\
    (Forall (fun cl' => length cl' = 3%nat) f') /\
    (forall a, exists a',
          (forall v, v < n -> a v = a' v) /\
          satisfies_clause a cl = satisfies_cnf_formula a' f') /\
    (forall a, satisfies_cnf_formula a f' = true -> satisfies_clause a cl = true).
Proof.
  destruct cl as [|?[|?[|?[|??]]]].
  - cbn.
    intuition; try lia.
    + exists a; intuition.
      destruct (a n); reflexivity.
    + destruct (a n); cbn in *; congruence.
  - cbn.
    intuition; repeat rewrite N_max_repeat; try lia.
    + exists a; intuition.
      destruct (a n), (a (n + 1)); btauto.
    + generalize H0.
      apply implb_prop.
      unfold implb.
      btauto.
  - cbn.
    intuition; try lia.
    + exists a; intuition.
      destruct (a n); btauto.
    + generalize H0.
      apply implb_prop.
      unfold implb.
      btauto.
  - cbn.
    intuition; try lia.
    exists a; intuition.
    btauto.
  - cbv [clause_to_three].
    remember (l1 :: l2 :: l3) as cl'.
    cbn.
    intros.
    pose proof (from_many_correct cl' n (n + 1)).
    destruct from_many as [n' f'].
    destruct H0 as (?&?&?&?&?&?).
    { destruct l, l0; lia. }
    { lia. }
    { rewrite Heqcl'. cbn. lia. }
    intuition; cbn; try lia.
    + destruct (satisfies_literal a l) eqn:?, (satisfies_literal a l0) eqn:?.
      * set (a' := fun v => if N.eq_dec v n then false else a v).
        destruct (H4 a') as (a'' &?&?); [subst a'; cbn; destruct N.eq_dec; congruence |].
        assert (forall v, v < n -> a v = a'' v). {
          intros.
          transitivity (a' v); [| apply H6; lia].
          subst a'; cbn.
          destruct N.eq_dec; lia || auto.
        }
        exists a''; intuition.
        rewrite H7.
        rewrite satisfies_literal_subst with (a' := a'') in Heqb by (destruct l; cbn in *; apply H8; lia).
        rewrite Heqb.
        btauto.
      * set (a' := fun v => if N.eq_dec v n then false else a v).
        destruct (H4 a') as (a'' &?&?); [subst a'; cbn; destruct N.eq_dec; congruence |].
        assert (forall v, v < n -> a v = a'' v). {
          intros.
          transitivity (a' v); [| apply H6; lia].
          subst a'; cbn.
          destruct N.eq_dec; lia || auto.
        }
        exists a''; intuition.
        rewrite H7.
        rewrite satisfies_literal_subst with (a' := a'') in Heqb by (destruct l; cbn in *; apply H8; lia).
        rewrite Heqb.
        btauto.
      * set (a' := fun v => if N.eq_dec v n then false else a v).
        destruct (H4 a') as (a'' &?&?); [subst a'; cbn; destruct N.eq_dec; congruence |].
        assert (forall v, v < n -> a v = a'' v). {
          intros.
          transitivity (a' v); [| apply H6; lia].
          subst a'; cbn.
          destruct N.eq_dec; lia || auto.
        }
        exists a''; intuition.
        rewrite H7.
        rewrite satisfies_literal_subst with (a' := a'') in Heqb0 by (destruct l; cbn in *; apply H8; lia).
        rewrite Heqb0.
        btauto.
      * set (a' := fun v => if N.eq_dec v n then true else a v).
        destruct (H3 a') as (a'' &?&?); [subst a'; cbn; destruct N.eq_dec; congruence |].
        assert (forall v, v < n -> a v = a'' v). {
          intros.
          transitivity (a' v); [| apply H6; lia].
          subst a'; cbn.
          destruct N.eq_dec; lia || auto.
        }
        exists a''; intuition.
        bool_simpl.
        rewrite satisfies_clause_subst with (a := a) (a' := a') by (intros; subst a'; cbn; destruct N.eq_dec; lia || auto).
        rewrite H7, <-H6 by lia.
        subst a'; cbn.
        destruct N.eq_dec; try lia.
        btauto.
    + cbn in H6.
      apply andb_prop in H6; intuition.
      destruct (satisfies_literal a l), (satisfies_literal a l0); try btauto.
      bool_simpl in *.
      apply H5; auto.
Qed.

Lemma Forall_app : forall A (P : A -> Prop) l1 l2,
    Forall P l1 ->
    Forall P l2 ->
    Forall P (l1 ++ l2).
Proof.
  induction 1; cbn; auto.
Qed.

Hint Resolve Forall_app.

Hint Resolve satisfies_cnf_formula_app.

Lemma cnf_to_three''_correct : forall f n,
    n > cnf_max_var f ->
    let (n', f') := cnf_to_three'' f n in
    Forall (fun cl' => length cl' = 3%nat) f' /\
    (forall a, exists a',
          (forall v, v < n -> a v = a' v) /\
          satisfies_cnf_formula a f = satisfies_cnf_formula a' f') /\
    (forall a, satisfies_cnf_formula a f' = true -> satisfies_cnf_formula a f = true).
Proof.
  induction f; cbn.
  - intuition.
    exists a; intuition.
  - intros.
    pose proof (clause_to_three_correct a n).
    destruct clause_to_three.
    specialize (IHf n0).
    destruct cnf_to_three''.
    destruct IHf as (?&?&?), H0 as (?&?&?&?); [lia.. |].
    intuition.
    + destruct (H7 a0) as (a' &?&?).
      destruct (H2 a') as (a'' &?&?).
      assert (forall v, v < n -> a0 v = a'' v). {
        intros.
        transitivity (a' v); [apply H6 | apply H10]; lia.
      }
      exists a''; intuition.
      rewrite H9.
      rewrite satisfies_cnf_subst with (a := a') (a' := a'') by (intros; apply H10; lia).
      rewrite satisfies_cnf_subst with (a := a0) (a' := a') by (intros; apply H6; lia).
      rewrite H11.
      auto.
    + rewrite satisfies_cnf_formula_app in H6.
      apply andb_prop in H6; intuition.
Qed.

Lemma cnf_to_three'_correct : forall f,
    Forall (fun cl' => length cl' = 3%nat) (cnf_to_three' f) /\
    (cnf_satisfiable f <-> cnf_satisfiable (cnf_to_three' f)).
Proof.
  intros.
  unfold cnf_to_three'.
  pose proof (cnf_to_three''_correct f (cnf_max_var f + 1)).
  destruct cnf_to_three''; cbn in *.
  destruct H as (?&?&?); [lia |].
  intuition.
  - destruct H2 as [a ?].
    destruct (H0 a) as (a' &?&?).
    exists a'.
    congruence.
  - destruct H2 as [a ?].
    exists a.
    auto.
Qed.

Definition cnf_to_three (f : cnf_formula) : threecnf_formula.
  exists (cnf_to_three' f).
  apply cnf_to_three'_correct.
Defined.

Theorem three_sat_is_np_hard : np_hard ThreeSAT.
Proof.
  apply (np_hard_reduction CNFSAT) with (f := cnf_to_three); [apply cnf_sat_is_np_hard |].
  constructor; cbn; auto.
  intros.
  apply cnf_to_three'_correct.
Qed.
