(** RationalBitBudget.v -- explicit rational coefficient bit-budget algebra.

    The manuscript's code-size proposition is encoding-relative.  This file
    fixes the standard raw numerator/denominator accounting used by the proof:
    multiplying two B-bit rational quantities may concatenate numerator and
    denominator bit scales, and adding rational quantities uses cross-products.
    The exact arithmetic implementation can normalize afterwards; normalization
    only decreases the raw numerator/denominator representation size.

    The purpose here is not to formalize machine integer arithmetic, but to
    replace an informal O-claim by a concrete recurrence from which the
    kappa[B+log(kappa+1)]-style safe upper budget follows for bounded overlap.
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

(** Safe raw-product encoding: sign/header plus concatenated multiplicative
    bit budgets. *)
Definition raw_mul_bits (x y : RawRationalBits) : RawRationalBits :=
  {| numerator_bits := numerator_bits x + numerator_bits y;
     denominator_bits := denominator_bits x + denominator_bits y |}.

(** Safe raw-sum encoding via (a/b)+(c/d)=(ad+bc)/(bd).  The extra bit in the
    numerator accounts for adding the two cross-products. *)
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
  unfold components_bounded, raw_mul_bits. simpl.
  split; nia.
Qed.

Lemma raw_add_component_bound : forall B x y,
  components_bounded B x -> components_bounded B y ->
  components_bounded (2 * B + 1) (raw_add_bits x y).
Proof.
  intros B x y [Hxn Hxd] [Hyn Hyd].
  unfold components_bounded, raw_add_bits. simpl.
  split.
  - apply Nat.add_le_mono_r.
    apply Nat.max_lub; nia.
  - nia.
Qed.

Fixpoint sum_budget (B : nat) (k : nat) : nat :=
  match k with
  | O => B
  | S j => sum_budget B j + B + 1
  end.

Lemma sum_budget_closed : forall B k,
  sum_budget B k = (S k) * B + k.
Proof.
  intros B k. induction k; simpl; nia.
Qed.

(** Repeatedly adding at most k+1 coefficients whose already-cross-multiplied
    numerator/denominator contributions each have B bits has linear raw bit
    growth.  This is the fixed-overlap fact needed by Proposition 6.4. *)
Theorem bounded_overlap_raw_bit_growth : forall B k,
  sum_budget B k <= (S k) * (B + 1).
Proof.
  intros B k. rewrite sum_budget_closed. nia.
Qed.

Definition overlap_log_budget (k : nat) : nat := S (Nat.log2 (k + 1)).

Lemma overlap_log_budget_positive : forall k,
  0 < overlap_log_budget k.
Proof. intro k. unfold overlap_log_budget. lia. Qed.

(** A convenient manuscript-form safe envelope.  The term kappa*(B+log kappa)
    dominates the linear raw recurrence once the harmless positive log/header
    term is included. *)
Theorem manuscript_style_overlap_budget : forall B k,
  sum_budget B k
    <= (S k) * (B + overlap_log_budget k).
Proof.
  intros B k.
  rewrite sum_budget_closed.
  pose proof (overlap_log_budget_positive k).
  nia.
Qed.

End UELAT_V3_RationalBitBudget.
