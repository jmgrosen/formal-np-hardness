Require Import Coq.NArith.NArith.

Require Import Omega.

Fixpoint decode (n : nat) : nat * nat :=
  match n with
  | 0 => (0, 0)
  | S n => let '(a, b) := decode n in
           match a with
           | 0 => (S b, 0)
           | S a => (a, S b)
           end
  end.

(* sorta cheating but oh well *)
Definition decodeN (n : N) : N * N :=
  let n' := N.to_nat n in
  let '(a, b) := decode n' in
  (N.of_nat a, N.of_nat b).

Fixpoint encode_sum (s : nat) : nat -> nat :=
  fix es_helper b :=
    match b with
    | 0 => match s with
           | 0 => 0
           | S s => S (encode_sum s s)
           end
    | S b => S (es_helper b)
    end.

Definition encode ab := let '(a, b) := ab in encode_sum (a + b) b.

Definition encodeN ab :=
  let '(a, b) := ab in
  N.of_nat (encode (N.to_nat a, N.to_nat b)).

Lemma decode_encode ab : decode (encode ab) = ab.
Proof.
  destruct ab as [a b].
  revert a b.
  cbv [encode].
  enough (forall s b, b <= s -> decode (encode_sum s b) = (s - b, b)) as H.
  { intros.
    specialize (H (a + b) b).
    replace (a + b - b) with a in H by omega.
    apply H; omega.  }
  intros s.
  induction s; intros.
  { replace b with 0 by omega.
    cbn [encode_sum decode].
    reflexivity. }
  { induction b.
    { cbn [encode_sum decode].
      rewrite IHs by omega.
      replace (s - s) with 0 by omega.
      reflexivity. }
    { cbn [encode_sum decode] in IHb |- *.
      rewrite IHb by omega.
      replace (S s - b) with (S (S s - S b)) by omega.
      reflexivity. } }
Qed.

Lemma encode_decode n : encode (decode n) = n.
Proof.
  induction n.
  { reflexivity. }
  { cbn [decode].
    cbv [encode] in *.
    destruct (decode n) as [a b].
    destruct a.
    { cbn [plus] in IHn.
      replace (S b + 0) with (S b) by omega.
      cbn [encode_sum].
      omega. }
    { replace (S a + b) with (S (a + b)) in IHn by omega.
      replace (a + S b) with (S (a + b)) by omega.
      cbn [encode_sum] in IHn |- *.
      omega. } }
Qed.

Lemma decodeN_encodeN ab : decodeN (encodeN ab) = ab.
Proof.
  destruct ab as [a b].
  cbv [encodeN decodeN].
  now rewrite Nat2N.id, decode_encode, !N2Nat.id.
Qed.

Lemma encodeN_decodeN n : encodeN (decodeN n) = n.
Proof.
  cbv [encodeN decodeN].
  destruct decode eqn:Heq.
  now rewrite !Nat2N.id, <-Heq, encode_decode, N2Nat.id.
Qed.
