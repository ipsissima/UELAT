(** RationalBitBudget.v -- explicit rational coefficient bit-budget algebra for authoritative Proposition 6.4.

    The code-size theorem is encoding-relative. This file fixes the raw binary
    numerator/denominator accounting and derives a bounded-overlap safe envelope.
*)

From Coq Require Import Arith Lia Nia List.
Import ListNotations.

Module UELAT_V3_RationalBitBudget.

Record RawRationalBits := {
  numerator_bits : nat;
  denominator_bits : nat
}.

Definition rational_bits (q : RawRationalBits) : nat :=
  1 + numerator_bits q + denominator_bits q.

Definition raw_mul_bits (x y : RawRationalBits) : RawRationalBits :=
  {| numerator_bits := numerator_bits x + numerator_bits y;
     denominator_bits := denominator_bits x + denominator_bits y |}.

Definition raw_add_bits (x y : RawRationalBits) : RawRationalBits :=
  {| numerator_bits :=
       Nat.max (numerator_bits x + denominator_bits y)
               (numerator_bits y + denominator_bits x) + 1;
     denominator_bits := denominator_bits x + denominator_bits y |}.

Definition components_bounded (B : nat) (q : RawRationalBits) : Prop :=
  numerator_bits q <= B /\ denominator_bits q <= B.

Lemma raw_mul_component_bound : forall B x y,
  components_bounded B x -> components_bounded B y ->
  components_bounded (2 * B) (raw_mul_bits x y).
Proof.
  intros B x y [Hxn Hxd] [Hyn Hyd].
  unfold components_bounded, raw_mul_bits. simpl. split; nia.
Qed.

Lemma raw_add_component_bound : forall B x y,
  components_bounded B x -> components_bounded B y ->
  components_bounded (2 * B + 1) (raw_add_bits x y).
Proof.
  intros B x y [Hxn Hxd] [Hyn Hyd].
  unfold components_bounded, raw_add_bits. simpl. split.
  - apply Nat.add_le_mono_r. apply Nat.max_lub; nia.
  - nia.
Qed.

Fixpoint sum_budget (B : nat) (k : nat) : nat :=
  match k with O => B | S j => sum_budget B j + B + 1 end.

Lemma sum_budget_closed : forall B k,
  sum_budget B k = (S k) * B + k.
Proof. intros B k. induction k; simpl; nia. Qed.

Theorem bounded_overlap_raw_bit_growth : forall B k,
  sum_budget B k <= (S k) * (B + 1).
Proof. intros B k. rewrite sum_budget_closed. nia. Qed.

Definition overlap_log_budget (k : nat) : nat := S (Nat.log2 (k + 1)).

Lemma overlap_log_budget_positive : forall k,
  0 < overlap_log_budget k.
Proof. intro k. unfold overlap_log_budget. lia. Qed.

Theorem manuscript_style_overlap_budget : forall B k,
  sum_budget B k <= (S k) * (B + overlap_log_budget k).
Proof.
  intros B k. rewrite sum_budget_closed.
  pose proof (overlap_log_budget_positive k). nia.
Qed.

End UELAT_V3_RationalBitBudget.
