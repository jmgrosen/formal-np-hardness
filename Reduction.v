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