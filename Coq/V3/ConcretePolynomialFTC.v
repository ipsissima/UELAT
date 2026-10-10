(**
  ConcretePolynomialFTC.v -- the actual Fundamental Theorem of Calculus
  for rational polynomial CODE semantics, using Stdlib.RiemannInt.

  Each rational code p is lifted to a C1 real function, with the
  derivative provided by qpoly_deriv -- not by an opaque derivative
  oracle. The library's FTC_Riemann then identifies the continuous
  Riemann integral of that coded derivative with its boundary
  difference on arbitrary ordered real endpoints.

  This is an essential step toward an honest weak-derivative/gluing
  proof for the piecewise rational W^{1,2} carrier. It does not yet
  identify rational closed-form antiderivative arithmetic with the
  Riemann integral, nor prove the full piecewise Sobolev theorem.
*)
From Stdlib Require Import Reals QArith Qreals List Lra Ranalysis1 RiemannInt.
Import ListNotations.
Local Open Scope R_scope.

From UELAT.V3 Require Import
  RationalSobolev RationalRealPolynomialSemantics
  ConcretePolynomialSobolev.

Module UELAT_V3_ConcretePolynomialFTC.
Import UELAT_V3_RationalSobolev.
Import UELAT_V3_RationalRealPolynomialSemantics.
Import UELAT_V3_ConcretePolynomialSobolev.

Definition polynomial_derivability_witness (p : QPoly) :
  derivable (rpoly_eval p).
Proof.
  intro x.
  exists (rpoly_eval (qpoly_deriv p) x).
  apply polynomial_has_concrete_real_derivative.
Defined.

(** A genuine Stdlib C1_fun is constructed from the code-level
    derivative, with a continuous derivative -- no added axioms. *)
Definition rational_polynomial_C1 (p : QPoly) : C1_fun.
Proof.
  refine {| c1 := rpoly_eval p;
            diff0 := polynomial_derivability_witness p |}.
  intro x.
  change (continuity_pt (rpoly_eval (qpoly_deriv p)) x).
  apply polynomial_is_continuous.
Defined.

Lemma rational_polynomial_C1_derivative : forall p x,
  derive (rational_polynomial_C1 p)
    (diff0 (rational_polynomial_C1 p)) x =
      rpoly_eval (qpoly_deriv p) x.
Proof.
  intros p x. reflexivity.
Qed.

(** Fundamental theorem for the CODE derivative and a concrete real
    Riemann integral. True on every ordered interval, not only [0,1]. *)
Theorem real_polynomial_coded_FTC :
  forall (p : QPoly) (a b : R) (Hab : a <= b),
    RiemannInt
      (concrete_polynomial_integrable_interval
        (qpoly_deriv p) a b Hab)
      = rpoly_eval p b - rpoly_eval p a.
Proof.
  intros p a b Hab.
  exact (FTC_Riemann (rational_polynomial_C1 p) a b
    (concrete_polynomial_integrable_interval
      (qpoly_deriv p) a b Hab)).
Qed.

End UELAT_V3_ConcretePolynomialFTC.
