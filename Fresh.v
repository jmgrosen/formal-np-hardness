Require Import Coq.NArith.BinNat.

Require Import ExtLib.Structures.Monad.

Definition Fresh A :=
  N -> N * A.

Instance Monad_Fresh : Monad Fresh :=
  {| ret := fun _ x n => (n, x);
     bind := fun _ _ c1 c2 n => let (n', x) := c1 n in
                             c2 x n';
  |}.

Definition fresh : Fresh N :=
  fun n => (n + 1, n)%N.