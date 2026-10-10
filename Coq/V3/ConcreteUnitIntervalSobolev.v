(**
  ConcreteUnitIntervalSobolev.v -- restrict the existing well-formed
  rational piecewise polynomial codes to the manuscript's EXACT
  domain [0,1]. The old [RationalPiecewiseCode] record requires
  positive continuous cells, but does not fix its outer endpoints.

  A code carrying both endpoint certificates is a concrete,
  piecewise-C1 real function on the full unit interval. In particular,
  its polynomial test-function integration-by-parts identity has no
  internal boundary term; the cancellation uses the real seam-value
  equality proved from the rational code certificates.

  This is a necessary foundation for a W^{1,2}(0,1) realization,
  NOT yet a full weak derivative in the distributional sense:
  rational-polynomial test functions alone are insufficient.
  Candidate source, unverified until kernel CI and assumption audit.
*)
From Stdlib Require Import Reals QArith Qreals List Lra.
Local Open Scope R_scope.

From UELAT.V3 Require Import
  RationalSobolev RationalRealPolynomialSemantics
  ConcretePiecewiseSobolev ConcretePiecewiseWeakTest.

Module UELAT_V3_ConcreteUnitIntervalSobolev.
Import UELAT_V3_RationalSobolev.
Import UELAT_V3_RationalRealPolynomialSemantics.
Import UELAT_V3_ConcretePiecewiseSobolev.
Import UELAT_V3_ConcretePiecewiseWeakTest.

Record UnitIntervalRationalCode := {
  unit_code : RationalPiecewiseCode;
  unit_left_endpoint :
    Qeq (initial_endpoint (rpc_pieces unit_code)) (0%Q);
  unit_right_endpoint :
    Qeq (terminal_endpoint (rpc_pieces unit_code)) (1%Q)
}.

Arguments unit_code _.

Theorem unit_code_real_start : forall u : UnitIntervalRationalCode,
  Q2R (initial_endpoint (rpc_pieces (unit_code u))) = Q2R (0%Q).
Proof.
  intro u.
  apply Qeq_eqR.
  apply unit_left_endpoint.
Qed.

Theorem unit_code_real_end : forall u : UnitIntervalRationalCode,
  Q2R (terminal_endpoint (rpc_pieces (unit_code u))) = Q2R (1%Q).
Proof.
  intro u.
  apply Qeq_eqR.
  apply unit_right_endpoint.
Qed.

Definition unit_piecewise_real_energy (u : UnitIntervalRationalCode) : R :=
  code_real_w12_energy (unit_code u).

Theorem unit_piecewise_real_energy_nonnegative :
  forall u : UnitIntervalRationalCode,
    0 <= unit_piecewise_real_energy u.
Proof.
  intro u.
  unfold unit_piecewise_real_energy.
  apply every_well_formed_code_has_finite_nonnegative_real_energy.
Qed.

(** The endpoint-zero condition can now be stated at the actual
    manuscript endpoints 0 and 1, not floating code endpoints. *)
Theorem unit_code_polynomial_test_weak_derivative :
  forall (u : UnitIntervalRationalCode) (phi : QPoly),
    rpoly_eval phi (Q2R (0%Q)) = 0 ->
    rpoly_eval phi (Q2R (1%Q)) = 0 ->
    code_weak_right (unit_code u) phi =
      - code_weak_left (unit_code u) phi.
Proof.
  intros u phi Hzero Hone.
  apply piecewise_polynomial_weak_test_endpoint_zero.
  - rewrite unit_code_real_start.
    exact Hzero.
  - rewrite unit_code_real_end.
    exact Hone.
Qed.

(** The *precise* semantic boundary: proving the above for all
    C_c^\infty((0,1)) real test functions, identifying the code
    derivative as an L2 weak derivative, and showing exact equality
    of Stdlib Riemann energy with Q2R of rational finite-code energy
    are still outstanding. *)
End UELAT_V3_ConcreteUnitIntervalSobolev.
