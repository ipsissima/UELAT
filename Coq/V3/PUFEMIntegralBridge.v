(**
  PUFEMIntegralBridge.v -- bridge from pointwise overlap estimates to
  integrated energy inequalities for manuscript Theorems 5.6 and 7.2.

  This file does NOT assume the global PUFEM inequality. Instead it
  derives it from (i) the pointwise estimate proved in
  PUFEMPointwiseCore.v and (ii) the standard algebraic laws of a
  positive linear integral. All sums remain finite.

  A fully constructive finite weighted-sample realization is supplied
  below. The intended W^{1,2}(0,1) realization still requires a
  verified continuous integral, weak-product rule, and the
  identification of its energy with the represented Sobolev norm.
  A finite quadrature is NOT a proof of the continuous statement.
*)
From Coq Require Import Reals List Lra Ring.
Import ListNotations.
Local Open Scope R_scope.

From UELAT.V3 Require Import PUFEMPointwiseCore.

Module UELAT_V3_PUFEMIntegralBridge.
Import UELAT_V3_PUFEMPointwiseCore.

Record PositiveLinearIntegral (X : Type) := {
  integral : (X -> R) -> R;
  integral_ext : forall f g,
    (forall x, f x = g x) -> integral f = integral g;
  integral_add : forall f g,
    integral (fun x => f x + g x) = integral f + integral g;
  integral_scale : forall c f,
    integral (fun x => c * f x) = c * integral f;
  integral_monotone : forall f g,
    (forall x, f x <= g x) -> integral f <= integral g
}.

Arguments integral {X} _ _.
Arguments integral_ext {X} _ _ _ _.
Arguments integral_add {X} _ _ _.
Arguments integral_scale {X} _ _ _.
Arguments integral_monotone {X} _ _ _ _.

Lemma integral_three_terms :
    forall (X : Type) (I : PositiveLinearIntegral X)
      (f g h : X -> R) (a b c : R),
      integral I (fun x => a * f x + b * g x + c * h x)
        = a * integral I f + b * integral I g + c * integral I h.
Proof.
  intros X I f g h a b c.
  transitivity
    (integral I (fun x => a * f x + (b * g x + c * h x))).
  - apply integral_ext. intro x. ring.
  - rewrite (integral_add I
      (fun x => a * f x) (fun x => b * g x + c * h x)).
    rewrite (integral_add I
      (fun x => b * g x) (fun x => c * h x)).
    repeat rewrite integral_scale.
    ring.
Qed.

(** A genuinely finite positive integral, not an unspecified axiom. *)
Fixpoint finite_integral {X : Type}
    (samples : list (X * R)) (f : X -> R) : R :=
  match samples with
  | [] => 0
  | (x,w) :: rest => w * f x + finite_integral rest f
  end.

Lemma finite_integral_ext :
  forall (X : Type) (samples : list (X * R)) f g,
    (forall x, f x = g x) ->
    finite_integral samples f = finite_integral samples g.
Proof.
  intros X samples. induction samples as [|[x w] rest IH]; intros f g Heq;
    simpl; [reflexivity|].
  rewrite (Heq x). rewrite (IH f g Heq). reflexivity.
Qed.

Lemma finite_integral_add :
  forall (X : Type) (samples : list (X * R)) f g,
    finite_integral samples (fun x => f x + g x) =
      finite_integral samples f + finite_integral samples g.
Proof.
  intros X samples. induction samples as [|[x w] rest IH]; intros f g;
    simpl; [ring|].
  rewrite IH. ring.
Qed.

Lemma finite_integral_scale :
  forall (X : Type) (samples : list (X * R)) c f,
    finite_integral samples (fun x => c * f x) =
      c * finite_integral samples f.
Proof.
  intros X samples. induction samples as [|[x w] rest IH]; intros c f;
    simpl; [ring|].
  rewrite IH. ring.
Qed.

Lemma finite_integral_monotone :
  forall (X : Type) (samples : list (X * R)) f g,
    Forall (fun p => 0 <= snd p) samples ->
    (forall x, f x <= g x) ->
    finite_integral samples f <= finite_integral samples g.
Proof.
  intros X samples. induction samples as [|[x w] rest IH]; intros f g Hw Hfg;
    simpl; [lra|].
  inversion Hw as [|z zs Hhead Htail]; subst.
  apply Rplus_le_compat.
  - apply Rmult_le_compat_l.
    + exact Hhead.
    + apply Hfg.
  - apply IH; assumption.
Qed.

Definition finite_positive_integral
    {X : Type} (samples : list (X * R))
    (Hweights : Forall (fun p => 0 <= snd p) samples)
    : PositiveLinearIntegral X.
Proof.
  refine {| integral := finite_integral samples |}.
  - intros f g Hfg. apply finite_integral_ext. exact Hfg.
  - intros f g. apply finite_integral_add.
  - intros c f. apply finite_integral_scale.
  - intros f g Hfg. apply finite_integral_monotone; assumption.
Defined.

Section LocalizedIntegratedEstimate.
  Context {X : Type}.
  Variable I : PositiveLinearIntegral X.
  Variable Cinf : R.
  Variable kappa : nat.
  Variable incidence_at : X -> list (SupportIncidence Cinf).

  Hypothesis active_overlap_at :
    forall x, (length (filter si_active (incidence_at x)) <= kappa)%nat.

  Definition value_at (x : X) : R :=
    sumR (map (fun z => value_term (si_incidence z)) (incidence_at x)).

  Definition derivative_at (x : X) : R :=
    sumR (map (fun z => derivative_term (si_incidence z)) (incidence_at x)).

  Definition global_squared_integrand (x : X) : R :=
    value_at x ^ 2 + derivative_at x ^ 2.

  Definition local_squared_l2 (x : X) : R :=
    sumR (map (fun z => (pw_error (si_incidence z)) ^ 2)
              (incidence_at x)).

  Definition local_weighted_l2 (x : X) : R :=
    sumR (map (fun z =>
        pw_L (si_incidence z) ^ 2 * pw_error (si_incidence z) ^ 2)
              (incidence_at x)).

  Definition local_squared_derivative (x : X) : R :=
    sumR (map (fun z => (pw_error_prime (si_incidence z)) ^ 2)
              (incidence_at x)).

  Definition local_allowances (x : X) : R :=
    sumR (map (fun z => total_allowance (si_incidence z))
              (incidence_at x)).

  Lemma local_allowances_expanded : forall x,
    local_allowances x =
      Cinf ^ 2 * local_squared_l2 x
      + 2 * local_weighted_l2 x
      + 2 * Cinf ^ 2 * local_squared_derivative x.
  Proof.
    intros x.
    unfold local_allowances, local_squared_l2,
      local_weighted_l2, local_squared_derivative.
    induction (incidence_at x) as [|z zs IH]; simpl.
    - ring.
    - rewrite total_allowance_formula.
      rewrite IH. ring.
  Qed.

  Lemma pointwise_56_for_integral : forall x,
    global_squared_integrand x <= INR kappa * local_allowances x.
  Proof.
    intros x. unfold global_squared_integrand, value_at,
      derivative_at, local_allowances.
    apply localized_integrand_supported_56.
    apply active_overlap_at.
  Qed.

  Theorem integrated_localized_56 :
    integral I global_squared_integrand <=
      INR kappa * (Cinf ^ 2 * integral I local_squared_l2
        + 2 * integral I local_weighted_l2
        + 2 * Cinf ^ 2 * integral I local_squared_derivative).
  Proof.
    pose proof (integral_monotone I global_squared_integrand
      (fun x => INR kappa * local_allowances x)
      pointwise_56_for_integral) as H.
    rewrite (integral_scale I (INR kappa) local_allowances) in H.
    assert (Hbudget :
      integral I local_allowances =
        Cinf ^ 2 * integral I local_squared_l2
        + 2 * integral I local_weighted_l2
        + 2 * Cinf ^ 2 * integral I local_squared_derivative).
    {
      transitivity
        (integral I (fun x => Cinf ^ 2 * local_squared_l2 x
          + 2 * local_weighted_l2 x
          + (2 * Cinf ^ 2) * local_squared_derivative x)).
      - apply integral_ext. intro x.
        rewrite local_allowances_expanded. ring.
      - apply integral_three_terms.
    }
    rewrite Hbudget in H. exact H.
  Qed.

  Lemma integrated_zero : integral I (fun _ => 0) = 0.
  Proof.
    pose proof (integral_add I (fun _ => 0) (fun _ => 0)) as Hz.
    assert (Hzero :
      integral I (fun x => 0 + 0) = integral I (fun _ => 0)).
    { apply integral_ext. intro x. ring. }
    rewrite Hzero in Hz. lra.
  Qed.

  Corollary integrated_localized_56_nonnegative :
    0 <= integral I global_squared_integrand.
  Proof.
    pose proof (integral_monotone I (fun _ => 0)
      global_squared_integrand) as H.
    rewrite integrated_zero in H.
    apply H. intro x.
    unfold global_squared_integrand.
    pose proof (pow2_ge_0 (value_at x)).
    pose proof (pow2_ge_0 (derivative_at x)).
    lra.
  Qed.
End LocalizedIntegratedEstimate.

(** At least one non-axiomatic integral instantiation: finite weighted
    quadrature over an arbitrary domain X. This theorem is explicitly
    *not* presented as continuous W12. *)
Theorem finite_positive_integrated_56 :
  forall (X : Type) (samples : list (X * R))
    (Hweights : Forall (fun p => 0 <= snd p) samples)
    Cinf kappa (incidence_at : X -> list (SupportIncidence Cinf))
    (Hoverlap : forall x,
      (length (filter si_active (incidence_at x)) <= kappa)%nat),
    integral (finite_positive_integral samples Hweights)
      (global_squared_integrand Cinf incidence_at) <=
      INR kappa *
        (Cinf ^ 2 * integral (finite_positive_integral samples Hweights)
          (local_squared_l2 Cinf incidence_at)
        + 2 * integral (finite_positive_integral samples Hweights)
          (local_weighted_l2 Cinf incidence_at)
        + 2 * Cinf ^ 2 *
            integral (finite_positive_integral samples Hweights)
              (local_squared_derivative Cinf incidence_at)).
Proof.
  intros X samples Hweights Cinf kappa incidence_at Hoverlap.
  exact (integrated_localized_56
    (finite_positive_integral samples Hweights)
    Cinf kappa incidence_at Hoverlap).
Qed.

End UELAT_V3_PUFEMIntegralBridge.
