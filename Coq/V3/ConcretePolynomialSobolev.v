(**
  ConcretePolynomialSobolev.v -- actual real-analysis instance of the
  rational polynomial W^{1,2} code core (Sections 5.2/5.6 of v3).

  Unlike an abstract "positive integral" record, this file invokes
  Stdlib's continuous Riemann integral on [0,1]. It proves that the
  interpreted rational polynomial has the derivative computed by the
  compiler and is continuous, hence that the squared L2/derivative
  energy is an integrable *real function* with nonnegative integral.

  This is the polynomial subspace, NOT yet all W^{1,2}(0,1).
  Separate work is needed for the piecewise gluing/weak derivative,
  completeness, the effective metric realization, and final 5.6/7.2.
  All source proofs remain unverified until Rocq 9.2 CI/coqchk passes.
*)
From Stdlib Require Import Reals QArith Qreals List Lra Ring Ranalysis1 RiemannInt.
Import ListNotations.
Local Open Scope R_scope.

From UELAT.V3 Require Import
  RationalSobolev RationalRealPolynomialSemantics.

Module UELAT_V3_ConcretePolynomialSobolev.
Import UELAT_V3_RationalSobolev.
Import UELAT_V3_RationalRealPolynomialSemantics.

Lemma deriv_from_real_step : forall n ps x,
  rpoly_eval (qpoly_deriv_from (S n) ps) x =
    rpoly_eval (qpoly_deriv_from n ps) x + rpoly_eval ps x.
Proof.
  intros n ps. revert n.
  induction ps as [|a ps IH]; intros n x; simpl.
  - ring.
  - rewrite !Q2R_mult.
    rewrite Q2R_plus, Q2R_one.
    rewrite (IH (S n) x).
    ring.
Qed.

Lemma deriv_from_real_zero : forall ps x,
  rpoly_eval (qpoly_deriv_from 0 ps) x =
    x * rpoly_eval (qpoly_deriv ps) x.
Proof.
  intros [|a ps] x; simpl.
  - ring.
  - rewrite Q2R_mult, Q2R_zero_local.
    ring.
Qed.

Lemma real_derivative_horner_step : forall a ps x,
  rpoly_eval (qpoly_deriv (a :: ps)) x =
    rpoly_eval ps x + x * rpoly_eval (qpoly_deriv ps) x.
Proof.
  intros a ps x.
  change (rpoly_eval (qpoly_deriv_from 1 ps) x =
    rpoly_eval ps x + x * rpoly_eval (qpoly_deriv ps) x).
  rewrite (deriv_from_real_step 0 ps x).
  rewrite deriv_from_real_zero.
  ring.
Qed.

(** Every finite rational polynomial denotes a genuinely differentiable
    function on R; its derivative is the semantics of qpoly_deriv. *)
Theorem polynomial_has_concrete_real_derivative : forall p x,
  derivable_pt_lim (rpoly_eval p) x
    (rpoly_eval (qpoly_deriv p) x).
Proof.
  intro p. induction p as [|a ps IH]; intro x.
  - change (derivable_pt_lim (fct_cte 0) x 0).
    apply derivable_pt_lim_const.
  - rewrite (real_derivative_horner_step a ps x).
    replace (rpoly_eval ps x +
             x * rpoly_eval (qpoly_deriv ps) x)
      with (0 +
        (1 * rpoly_eval ps x +
          x * rpoly_eval (qpoly_deriv ps) x)) by ring.
    change (derivable_pt_lim
      (plus_fct (fct_cte (Q2R a))
        (mult_fct id (rpoly_eval ps))) x
      (0 +
        (1 * rpoly_eval ps x +
          x * rpoly_eval (qpoly_deriv ps) x))).
    apply derivable_pt_lim_plus.
    + apply derivable_pt_lim_const.
    + apply derivable_pt_lim_mult.
      * apply derivable_pt_lim_id.
      * apply IH.
Qed.

Theorem polynomial_is_continuous : forall p x,
  continuity_pt (rpoly_eval p) x.
Proof.
  intros p x.
  apply derivable_continuous_pt.
  exists (rpoly_eval (qpoly_deriv p) x).
  apply polynomial_has_concrete_real_derivative.
Qed.

Lemma real_unit_interval_order : 0 <= 1.
Proof. lra. Qed.

Definition concrete_polynomial_integrable_01 (p : QPoly) :
  Riemann_integrable (rpoly_eval p) 0 1.
Proof.
  apply continuity_implies_RiemannInt.
  - apply real_unit_interval_order.
  - intros x Hx. apply polynomial_is_continuous.
Defined.

Definition polynomial_energy_code (p : QPoly) : QPoly :=
  qpoly_add (qpoly_mul p p)
    (qpoly_mul (qpoly_deriv p) (qpoly_deriv p)).

Definition concrete_polynomial_energy_integrand (p : QPoly) (x : R) : R :=
  rpoly_eval (polynomial_energy_code p) x.

Theorem polynomial_energy_is_actual_squared_norm_integrand :
  forall p x,
    concrete_polynomial_energy_integrand p x =
      (rpoly_eval p x) ^ 2 +
      (rpoly_eval (qpoly_deriv p) x) ^ 2.
Proof.
  intros p x.
  unfold concrete_polynomial_energy_integrand, polynomial_energy_code.
  rewrite rpoly_eval_add_sound.
  repeat rewrite rpoly_eval_mul_sound.
  ring.
Qed.

Theorem polynomial_energy_pointwise_nonnegative : forall p x,
  0 <= concrete_polynomial_energy_integrand p x.
Proof.
  intros p x.
  rewrite polynomial_energy_is_actual_squared_norm_integrand.
  pose proof (pow2_ge_0 (rpoly_eval p x)).
  pose proof (pow2_ge_0 (rpoly_eval (qpoly_deriv p) x)).
  lra.
Qed.

Definition concrete_polynomial_energy_integrable (p : QPoly) :
  Riemann_integrable (concrete_polynomial_energy_integrand p) 0 1 :=
  concrete_polynomial_integrable_01 (polynomial_energy_code p).

(** This is a genuine [0,1] Riemann integral of the continuously
    differentiable rational polynomial and its true derivative squared. *)
Definition concrete_polynomial_w12_energy (p : QPoly) : R :=
  RiemannInt (concrete_polynomial_energy_integrable p).

Theorem concrete_polynomial_w12_energy_nonnegative : forall p,
  0 <= concrete_polynomial_w12_energy p.
Proof.
  intro p.
  pose proof
    (RiemannInt_P19
      (fct_cte 0) (concrete_polynomial_energy_integrand p)
      0 1
      (RiemannInt_P14 0 1 0)
      (concrete_polynomial_energy_integrable p)) as Hmon.
  assert (H01 : 0 <= 1) by lra.
  specialize (Hmon H01).
  assert (Hpoint : forall x, 0 < x < 1 ->
    fct_cte 0 x <= concrete_polynomial_energy_integrand p x).
  { intros x Hx. unfold fct_cte.
    apply polynomial_energy_pointwise_nonnegative. }
  specialize (Hmon Hpoint).
  unfold concrete_polynomial_w12_energy.
  rewrite RiemannInt_P15 in Hmon.
  lra.
Qed.

End UELAT_V3_ConcretePolynomialSobolev.
