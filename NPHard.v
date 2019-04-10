Require Import Reduction SAT.

Generalizable Variables A B.

Definition np_hard `(PA : problem A) : Prop :=
  exists f, reduction SAT PA f.