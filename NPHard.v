Require Import Reduction SAT.

Generalizable Variables A B.

Definition np_hard `(PA : problem A) : Prop :=
  exists f, reduction SAT PA f.

Lemma SAT_np_hard : np_hard SAT.
Proof.
  exists (fun x => x).
  constructor; intuition.
Qed.

Lemma np_hard_reduction : forall `(PA : problem A) `(PB : problem B) (f : A -> B),
    np_hard PA ->
    reduction PA PB f ->
    np_hard PB.
Proof.
  intros * [g ?] H1.
  exists (fun x => f (g x)).
  eapply reduction_comp; eauto.
Qed.
