Require Import Coq.NArith.BinNat.

Require Import Reduction.

Definition var := N.

Inductive formula : Type :=
| Var : var -> formula
| Not : formula -> formula
| And : formula -> formula -> formula
| Or : formula -> formula -> formula
.

Fixpoint formula_size (f : formula) : nat :=
  match f with
  | Var _ => 1
  | Not f' => S (formula_size f')
  | And f1 f2 => S (formula_size f1 + formula_size f2)
  | Or f1 f2 => S (formula_size f1 + formula_size f2)
  end.

Fixpoint satisfies (a : var -> bool) (f : formula) : bool :=
  match f with
  | Var v => a v
  | Not f' => negb (satisfies a f')
  | And f1 f2 => satisfies a f1 && satisfies a f2
  | Or f1 f2 => satisfies a f1 || satisfies a f2
  end.

Definition satisfiable (f : formula) : Prop :=
  exists a, satisfies a f = true.

Instance SAT : problem formula :=
  { ProblemSize := formula_size;
    ProblemYes := satisfiable;
  }.