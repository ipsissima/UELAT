(**
  ConcreteRiemannPUFEM56.v -- direct continuous-integral bridge for
  the localized PUFEM defect estimate in v3 manuscript Theorem 5.6.

  This uses the ACTUAL [Stdlib.Reals.RiemannInt] type and the verified
  Riemann integral monotonicity theorem, not a generic integral record
  and not finite quadrature.

  The pointwise inequality is already constructed in
  [PUFEMPointwiseCore]. The hypotheses here concern the remaining
  analytic facts: Riemann integrability of the two concrete integrands
  on [0,1] and certified finite active support on that interval.

  For rational polynomial integrands continuity/integrability can
  be established in [ConcretePolynomialSobolev]. The full piecewise
  W^{1,2}(0,1) decoding and effective local approximation estimates
  remain separate unproved obligations. Kernel validation pending.
*)
From Stdlib Require Import Reals RiemannInt Lra List.
Import ListNotations.
Local Open Scope R_scope.

From UELAT.V3 Require Import
  PUFEMPointwiseCore PUFEMIntegralBridge.

Module UELAT_V3_ConcreteRiemannPUFEM56.
Import UELAT_V3_PUFEMPointwiseCore.
Import UELAT_V3_PUFEMIntegralBridge.

Section ActualContinuousIntegral.
  Variable Cinf : R.
  Variable kappa : nat.
  Variable incidences : R -> list (SupportIncidence Cinf).

  Definition real_localized_error_integrand (x : R) : R :=
    (sumR (map (fun z => value_term (si_incidence z))
      (incidences x))) ^ 2
    + (sumR (map (fun z => derivative_term (si_incidence z))
      (incidences x))) ^ 2.

  Definition real_localized_budget_integrand (x : R) : R :=
    INR kappa *
      sumR (map (fun z => total_allowance (si_incidence z))
        (incidences x)).

  Hypothesis certified_active_overlap :
    forall x, 0 < x < 1 ->
      (length (filter si_active (incidences x)) <= kappa)%nat.

  Hypothesis continuous_error_integrable :
    Riemann_integrable real_localized_error_integrand 0 1.

  Hypothesis continuous_budget_integrable :
    Riemann_integrable real_localized_budget_integrand 0 1.

  Theorem real_riemann_integral_localized_56 :
    RiemannInt continuous_error_integrable <=
      RiemannInt continuous_budget_integrable.
  Proof.
    apply RiemannInt_P19.
    - lra.
    - intros x Hx.
      unfold real_localized_error_integrand,
        real_localized_budget_integrand.
      apply localized_integrand_supported_56.
      apply certified_active_overlap. exact Hx.
  Qed.

  (** The result says nothing about the weak derivative until the
      interpreted derivative terms are proved to be the weak derivative
      of the global synthesized function. *)
End ActualContinuousIntegral.

End UELAT_V3_ConcreteRiemannPUFEM56.
