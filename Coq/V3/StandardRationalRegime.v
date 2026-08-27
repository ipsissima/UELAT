(** StandardRationalRegime.v -- dyadic normal form behind authoritative Corollary 7.5.

    At target exponent s the level is of order s/(r-1). Substitution into the
    O(2^n(n+1)) depth bound yields the discrete representatives of
    epsilon^{-1/(r-1)} and the logarithmic factor.
*)

From Coq Require Import Arith Lia Nia Reals.
From UELAT.V3 Require Import OrderNeutralDescent.

Module UELAT_V3_StandardRationalRegime.
Import UELAT_V3_OrderNeutralDescent.

Definition ceil_div (s alpha : nat) : nat :=
  match alpha with O => 0 | S a => (s + a) / S a end.

Definition precision_level (r s : nat) : nat := ceil_div s (r - 1).
Definition dyadic_tolerance (s : nat) : R := / INR (pow2 s).

Lemma dyadic_tolerance_positive : forall s,
  0 < dyadic_tolerance s.
Proof.
  intro s. unfold dyadic_tolerance.
  apply Rinv_0_lt_compat. apply lt_0_INR. apply pow2_positive.
Qed.

Definition inverse_alpha_proxy (r s : nat) : nat := pow2 (precision_level r s).
Definition logarithmic_proxy (r s : nat) : nat := S (precision_level r s).

Section Corollary.
  Variable M0 : nat.
  Hypothesis HM0 : 0 < M0.
  Variables beta payload_bits ordinary_bits : nat -> nat.
  Variables c_payload base_factor beta_factor : nat.
  Hypothesis beta_positive : forall n, 0 < beta n.
  Hypothesis beta_monotone : forall j n, j <= n -> beta j <= beta n.
  Hypothesis payload_level_bound : forall n,
      payload_bits n <= c_payload * (M0 * pow2 n) * beta n.
  Hypothesis baseline_dominates : forall n,
      (M0 * pow2 n) * beta n <= base_factor * ordinary_bits n.
  Hypothesis beta_linear : forall n,
      beta n <= beta_factor * S n.

  Theorem corollary_7_5_standard_rational_precision_bound : forall r s,
    2 <= r ->
    nsum_upto payload_bits (precision_level r s)
      <= 2 * c_payload * M0 * beta_factor
           * inverse_alpha_proxy r s * logarithmic_proxy r s.
  Proof.
    intros r s Hr.
    unfold inverse_alpha_proxy, logarithmic_proxy.
    eapply standard_rational_depth_bound; eauto.
  Qed.

  Theorem corollary_7_5_relative_to_baseline : forall r s,
    2 <= r ->
    nsum_upto payload_bits (precision_level r s)
      <= 2 * c_payload * base_factor
           * ordinary_bits (precision_level r s).
  Proof.
    intros r s Hr.
    eapply order_neutral_relative_to_baseline; eauto.
  Qed.
End Corollary.

End UELAT_V3_StandardRationalRegime.
