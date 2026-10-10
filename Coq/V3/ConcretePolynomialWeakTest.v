(**
  ConcretePolynomialWeakTest.v -- a genuine continuous integration-by-parts
  identity for the rational polynomial carrier and polynomial test functions.

  This is NOT an axiom: it derives the derivative of p*phi from the
  C1 derivatives of the ACTUAL rational codes, and invokes the standard
  Riemann FTC. If phi vanishes at both endpoints, its weak test pairing
  has the expected sign. Integrability is supplied by continuity.

  This proves the integration-by-parts identity for polynomial tests
  on one interval. It is not yet the full distributional statement
  for all smooth compactly supported tests or the piecewise seam proof.
*)
From Stdlib Require Import Reals QArith Qreals List Lra Ring
  Ranalysis1 RiemannInt.
Import ListNotations.
Local Open Scope R_scope.

From UELAT.V3 Require Import
  RationalSobolev RationalRealPolynomialSemantics
  ConcretePolynomialSobolev.

Module UELAT_V3_ConcretePolynomialWeakTest.
Import UELAT_V3_RationalSobolev.
Import UELAT_V3_RationalRealPolynomialSemantics.
Import UELAT_V3_ConcretePolynomialSobolev.

Definition real_polynomial_product (p phi : QPoly) (x : R) : R :=
  rpoly_eval p x * rpoly_eval phi x.

Definition real_polynomial_product_derivative
    (p phi : QPoly) (x : R) : R :=
  rpoly_eval (qpoly_deriv p) x * rpoly_eval phi x
    + rpoly_eval p x * rpoly_eval (qpoly_deriv phi) x.

Lemma real_polynomial_product_has_correct_derivative :
  forall p phi x,
    derivable_pt_lim (real_polynomial_product p phi) x
      (real_polynomial_product_derivative p phi x).
Proof.
  intros p phi x.
  unfold real_polynomial_product, real_polynomial_product_derivative.
  change (derivable_pt_lim
    (mult_fct (rpoly_eval p) (rpoly_eval phi)) x
    (rpoly_eval (qpoly_deriv p) x * rpoly_eval phi x
     + rpoly_eval p x * rpoly_eval (qpoly_deriv phi) x)).
  apply derivable_pt_lim_mult;
    apply polynomial_has_concrete_real_derivative.
Qed.

Lemma real_polynomial_product_derivative_continuous :
  forall p phi x,
    continuity_pt (real_polynomial_product_derivative p phi) x.
Proof.
  intros p phi x.
  unfold real_polynomial_product_derivative.
  change (continuity_pt
    (plus_fct
      (mult_fct (rpoly_eval (qpoly_deriv p)) (rpoly_eval phi))
      (mult_fct (rpoly_eval p) (rpoly_eval (qpoly_deriv phi)))) x).
  apply continuity_pt_plus.
  - apply continuity_pt_mult; apply polynomial_is_continuous.
  - apply continuity_pt_mult; apply polynomial_is_continuous.
Qed.

Definition real_polynomial_product_C1 (p phi : QPoly) : C1_fun.
Proof.
  refine {| c1 := real_polynomial_product p phi;
    diff0 := fun x =>
      exist _ (real_polynomial_product_derivative p phi x)
        (real_polynomial_product_has_correct_derivative p phi x) |}.
  intro x.
  change (continuity_pt
    (real_polynomial_product_derivative p phi) x).
  apply real_polynomial_product_derivative_continuous.
Defined.

Definition real_polynomial_product_derivative_integrable
    (p phi : QPoly) (a b : R) (Hab : a <= b) :
  Riemann_integrable (real_polynomial_product_derivative p phi) a b.
Proof.
  apply continuity_implies_RiemannInt.
  - exact Hab.
  - intros x Hx. apply real_polynomial_product_derivative_continuous.
Defined.

Theorem real_polynomial_product_FTC :
  forall p phi a b (Hab : a <= b),
    RiemannInt
      (real_polynomial_product_derivative_integrable p phi a b Hab)
    = real_polynomial_product p phi b
      - real_polynomial_product p phi a.
Proof.
  intros p phi a b Hab.
  exact (FTC_Riemann (real_polynomial_product_C1 p phi) a b
    (real_polynomial_product_derivative_integrable p phi a b Hab)).
Qed.

(** The combined-integrand weak test identity for a polynomial test
    vanishing at the endpoints. No integration-by-parts premise is used. *)
Theorem rational_polynomial_weak_test_combined :
  forall p phi a b (Hab : a <= b),
    rpoly_eval phi a = 0 ->
    rpoly_eval phi b = 0 ->
    RiemannInt
      (real_polynomial_product_derivative_integrable p phi a b Hab) = 0.
Proof.
  intros p phi a b Hab Ha Hb.
  rewrite real_polynomial_product_FTC.
  unfold real_polynomial_product.
  rewrite Ha, Hb.
  ring.
Qed.

Definition weak_term_derivative_times_test
    (p phi : QPoly) (x : R) : R :=
  rpoly_eval (qpoly_deriv p) x * rpoly_eval phi x.

Definition weak_term_value_times_test_derivative
    (p phi : QPoly) (x : R) : R :=
  rpoly_eval p x * rpoly_eval (qpoly_deriv phi) x.

Lemma weak_term_left_continuous : forall p phi x,
  continuity_pt (weak_term_derivative_times_test p phi) x.
Proof.
  intros p phi x. unfold weak_term_derivative_times_test.
  change (continuity_pt
    (mult_fct (rpoly_eval (qpoly_deriv p)) (rpoly_eval phi)) x).
  apply continuity_pt_mult; apply polynomial_is_continuous.
Qed.

Lemma weak_term_right_continuous : forall p phi x,
  continuity_pt (weak_term_value_times_test_derivative p phi) x.
Proof.
  intros p phi x. unfold weak_term_value_times_test_derivative.
  change (continuity_pt
    (mult_fct (rpoly_eval p) (rpoly_eval (qpoly_deriv phi))) x).
  apply continuity_pt_mult; apply polynomial_is_continuous.
Qed.

Definition weak_term_left_integrable
    (p phi : QPoly) (a b : R) (Hab : a <= b) :
  Riemann_integrable (weak_term_derivative_times_test p phi) a b.
Proof.
  apply continuity_implies_RiemannInt.
  - exact Hab.
  - intros x Hx. apply weak_term_left_continuous.
Defined.

Definition weak_term_right_integrable
    (p phi : QPoly) (a b : R) (Hab : a <= b) :
  Riemann_integrable
    (weak_term_value_times_test_derivative p phi) a b.
Proof.
  apply continuity_implies_RiemannInt.
  - exact Hab.
  - intros x Hx. apply weak_term_right_continuous.
Defined.

(** Real integration by parts WITH the boundary term. This is the
    engine for cancellation at internal rational-mesh knots. *)
Theorem rational_polynomial_interval_integration_by_parts :
  forall p phi a b (Hab : a <= b),
    RiemannInt (weak_term_left_integrable p phi a b Hab)
      + RiemannInt (weak_term_right_integrable p phi a b Hab)
    = real_polynomial_product p phi b
      - real_polynomial_product p phi a.
Proof.
  intros p phi a b Hab.
  set (f := weak_term_derivative_times_test p phi).
  set (g := weak_term_value_times_test_derivative p phi).
  set (prf := weak_term_left_integrable p phi a b Hab).
  set (prg := weak_term_right_integrable p phi a b Hab).
  pose (prsum := RiemannInt_P10 f g a b 1 prf prg).
  pose proof (RiemannInt_P12 f g a b 1 prf prg prsum Hab)
    as Hline.
  pose proof
    (RiemannInt_P18 (fun x => f x + 1 * g x)
      (real_polynomial_product_derivative p phi)
      a b prsum
      (real_polynomial_product_derivative_integrable p phi a b Hab)
      Hab) as Hext.
  assert (Heq : forall x, a < x < b ->
    f x + 1 * g x =
      real_polynomial_product_derivative p phi x).
  { intros x Hx. unfold f, g,
      real_polynomial_product_derivative,
      weak_term_derivative_times_test,
      weak_term_value_times_test_derivative.
    ring. }
  specialize (Hext Heq).
  pose proof (real_polynomial_product_FTC p phi a b Hab) as HFTC.
  rewrite Hext in Hline.
  rewrite HFTC in Hline.
  unfold prf, prg in Hline.
  lra.
Qed.

(** Weak-derivative identity for polynomial tests zero at the endpoints.
    General distributional tests are not yet covered by this module. *)
Theorem rational_polynomial_weak_derivative_test :
  forall p phi a b (Hab : a <= b),
    rpoly_eval phi a = 0 ->
    rpoly_eval phi b = 0 ->
    RiemannInt (weak_term_right_integrable p phi a b Hab)
      = - RiemannInt (weak_term_left_integrable p phi a b Hab).
Proof.
  intros p phi a b Hab Ha Hb.
  pose proof
    (rational_polynomial_interval_integration_by_parts p phi a b Hab)
      as H.
  unfold real_polynomial_product in H.
  rewrite Ha, Hb in H.
  lra.
Qed.

End UELAT_V3_ConcretePolynomialWeakTest.
