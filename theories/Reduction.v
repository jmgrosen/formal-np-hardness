Generalizable Variables A B.

Class problem A :=
  { ProblemSize : A -> nat;
    ProblemYes : A -> Prop;
  }.

Inductive polytime `{problem A} `{problem B} (f : A -> B) : Prop :=
| PolyTime
.

Hint Constructors polytime.

Class reduction {A B} (PA : problem A) (PB : problem B) (f : A -> B) :=
  { ReductionPolytime : polytime f;
    ReductionCorrect : forall x, ProblemYes x <-> ProblemYes (f x);
  }.

Instance reduction_comp
         {A B C}
         (PA : problem A) (PB : problem B) (PC : problem C)
         (f : A -> B) (g : B -> C)
         (r1 : reduction PA PB f) (r2 : reduction PB PC g)
  : reduction PA PC (fun x => g (f x)).
Proof.
  destruct r1, r2.
  constructor; firstorder.
Qed.
