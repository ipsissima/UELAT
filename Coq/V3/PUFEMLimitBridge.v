(**
  PUFEMLimitBridge.v -- limit-closed finite-support PUFEM estimates.

  No positive-linear continuous-integral structure is postulated here.
  The proof passes from finite weighted quadratures to their specified
  real-number limits by an epsilon argument. It is independent of any
  external measure-theory library.

  The genuinely remaining analytic obligation is to exhibit actual
  convergent quadratures for the W^{1,2}(0,1) polynomial/hat-code
  integrands and identify their limits with the semantic squared
  Sobolev norms and the manuscript's defect sums.

  This module is a bridge, not a claim that v3 Theorem 5.6 or
  Theorem 7.2 is checked.
*)
From Coq Require Import Reals List Arith Lia Lra Ring.
Import ListNotations.
Local Open Scope R_scope.
From UELAT.V3 Require Import PUFEMPointwiseCore.

Module UELAT_V3_PUFEMLimitBridge.
Import UELAT_V3_PUFEMPointwiseCore.

Definition sequence_converges (u : nat -> R) (limit : R) : Prop :=
  forall eps : R, 0 < eps ->
    exists N : nat, forall n : nat, (N <= n)%nat ->
      Rabs (u n - limit) < eps.

(** A fully internal epsilon proof of the order-preservation principle:
    two convergent real sequences preserve pointwise inequalities in
    the limit. This uses only the Archimedean real-order interface. *)
Lemma sequence_order_limit :
  forall (u v : nat -> R) (a b : R),
    (forall n, u n <= v n) ->
    sequence_converges u a ->
    sequence_converges v b ->
    a <= b.
Proof.
  intros u v a b Horder Hu Hv.
  destruct (Rlt_dec b a) as [Hbad|Hnot].
  - exfalso.
    set (eps := (a - b) / 4).
    assert (Heps : 0 < eps) by (unfold eps; lra).
    destruct (Hu eps Heps) as [Nu HNu].
    destruct (Hv eps Heps) as [Nv HNv].
    specialize (HNu (Nat.max Nu Nv) (Nat.le_max_l Nu Nv)).
    specialize (HNv (Nat.max Nu Nv) (Nat.le_max_r Nu Nv)).
    specialize (Horder (Nat.max Nu Nv)).
    assert (Hlower :
      a - u (Nat.max Nu Nv) <=
        Rabs (u (Nat.max Nu Nv) - a)).
    {
      replace (a - u (Nat.max Nu Nv))
        with (-(u (Nat.max Nu Nv) - a)) by ring.
      pose proof (Rle_abs (-(u (Nat.max Nu Nv) - a))) as Habs.
      rewrite Rabs_Ropp in Habs.
      exact Habs.
    }
    assert (Hupper :
      v (Nat.max Nu Nv) - b <=
        Rabs (v (Nat.max Nu Nv) - b)).
    { apply Rle_abs. }
    unfold eps in *.
    lra.
  - lra.
Qed.

Section QuadratureLimit.
  Variable Cinf : R.
  Variable kappa : nat.
  Variable quadratures : nat -> list (SupportedSample Cinf kappa).

  Definition quadrature_error_energy (n : nat) : R :=
    sumR (map (@supported_sample_defect Cinf kappa) (quadratures n)).

  Definition quadrature_local_budget (n : nat) : R :=
    sumR (map (@supported_sample_budget Cinf kappa) (quadratures n)).

  Lemma every_quadrature_has_56_bound :
    forall n, quadrature_error_energy n <= quadrature_local_budget n.
  Proof.
    intro n. unfold quadrature_error_energy, quadrature_local_budget.
    apply finite_supported_quadrature_56.
  Qed.

  (** The continuous inequality follows from *convergence*, not from
      treating a finite quadrature as already equal to an integral. *)
  Theorem integrated_localized_56_from_quadrature_limits :
    forall energy_limit budget_limit,
      sequence_converges quadrature_error_energy energy_limit ->
      sequence_converges quadrature_local_budget budget_limit ->
      energy_limit <= budget_limit.
  Proof.
    intros energy_limit budget_limit He Hb.
    eapply sequence_order_limit.
    - apply every_quadrature_has_56_bound.
    - exact He.
    - exact Hb.
  Qed.

  (** Transfer of a scale-sensitive budget already established from
      local approximation rates. No rate is smuggled into convergence. *)
  Corollary scale_sensitive_72_from_quadrature_limits :
    forall energy_limit budget_limit scale_coefficient h_rate source_norm,
      sequence_converges quadrature_error_energy energy_limit ->
      sequence_converges quadrature_local_budget budget_limit ->
      budget_limit <= scale_coefficient * h_rate ^ 2 * source_norm ^ 2 ->
      energy_limit <= scale_coefficient * h_rate ^ 2 * source_norm ^ 2.
  Proof.
    intros energy_limit budget_limit scale_coefficient h_rate source_norm
      He Hb Hbudget.
    eapply Rle_trans.
    - apply integrated_localized_56_from_quadrature_limits; assumption.
    - exact Hbudget.
  Qed.
End QuadratureLimit.

End UELAT_V3_PUFEMLimitBridge.
