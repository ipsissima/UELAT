(**
  PUFEMScaleBridge.v -- scale-sensitive consequence of the genuinely
  pointwise-derived local-to-global energy estimate for 5.6/7.2.

  This is NOT a new proof of the local approximation inequalities:
  their squared L2 and derivative rates are explicit hypotheses.
  Unlike ScaleSensitivePUFEMAnalytic.v, the global overlap and
  product-rule error estimates are *derived* from finite active supports,
  multiplier bounds and a positive linear integral in the earlier files.

  The normalized squared scales are h_r, h_alpha and h_inv.
  For h in (0,1] and regularity r>1 the intended semantics is:
    h_r = h^(2r), h_alpha = h^(2(r-1)), h_inv = h^(-1).
  No exponential identity or continuous integral is assumed checked.
*)
From Coq Require Import Reals List Lra Ring.
Import ListNotations.
Local Open Scope R_scope.

From UELAT.V3 Require Import PUFEMPointwiseCore PUFEMIntegralBridge.

Module UELAT_V3_PUFEMScaleBridge.
Import UELAT_V3_PUFEMPointwiseCore.
Import UELAT_V3_PUFEMIntegralBridge.

Section Scale.
  Context {X : Type}.
  Variable I : PositiveLinearIntegral X.
  Variables Cinf Cchi C0 C1 h_r h_alpha h_inv Rbound : R.
  Variable kappa : nat.
  Variable incidence_at : X -> list (SupportIncidence Cinf).

  Hypothesis HC0 : 0 <= C0.
  Hypothesis HC1 : 0 <= C1.
  Hypothesis HCchi : 0 <= Cchi.
  Hypothesis Hinv : 0 <= h_inv.
  Hypothesis HR : 0 <= Rbound.
  Hypothesis Hoverlap : forall x,
    (length (filter si_active (incidence_at x)) <= kappa)%nat.

  Hypothesis Hmultiplier : forall x z,
    In z (incidence_at x) ->
    pw_L (si_incidence z) <= Cchi * h_inv.

  Hypothesis Hlocal_l2 :
    integral I (local_squared_l2 Cinf incidence_at)
      <= C0 * h_r * Rbound.
  Hypothesis Hlocal_deriv :
    integral I (local_squared_derivative Cinf incidence_at)
      <= C1 * h_alpha * Rbound.
  Hypothesis Hrate_loss : h_r <= h_alpha.
  Hypothesis Hinverse_loss : h_inv ^ 2 * h_r <= h_alpha.

  Definition scale_squared_constant : R :=
    INR kappa * ((Cinf ^ 2 + 2 * Cchi ^ 2) * C0
                 + 2 * Cinf ^ 2 * C1).

  Lemma weighted_list_bound :
    forall (xs : list (SupportIncidence Cinf)),
      (forall z, In z xs ->
         pw_L (si_incidence z) <= Cchi * h_inv) ->
      sumR (map (fun z =>
          pw_L (si_incidence z) ^ 2 *
          pw_error (si_incidence z) ^ 2) xs)
      <= Cchi ^ 2 * h_inv ^ 2 *
         sumR (map (fun z =>
          pw_error (si_incidence z) ^ 2) xs).
  Proof.
    intros xs. induction xs as [|z zs IH]; intro Hbound; simpl.
    - nra.
    - assert (HL : pw_L (si_incidence z) <= Cchi * h_inv).
      { apply Hbound. left. reflexivity. }
      assert (HL0 : 0 <= pw_L (si_incidence z)).
      { pose proof (pw_psi_prime_lower (si_incidence z)).
        pose proof (pw_psi_prime_upper (si_incidence z)).
        lra. }
      assert (Hupper : 0 <= Cchi * h_inv).
      { apply Rmult_le_pos; assumption. }
      assert (Hsquare :
        pw_L (si_incidence z) ^ 2 <= (Cchi * h_inv) ^ 2).
      { nra. }
      assert (Hterm :
        pw_L (si_incidence z) ^ 2 *
          pw_error (si_incidence z) ^ 2
        <= (Cchi ^ 2 * h_inv ^ 2) *
          pw_error (si_incidence z) ^ 2).
      {
        replace (Cchi ^ 2 * h_inv ^ 2)
          with ((Cchi * h_inv) ^ 2) by ring.
        apply Rmult_le_compat_r.
        - apply pow2_ge_0.
        - exact Hsquare.
      }
      assert (Htail :
        sumR (map (fun z0 =>
          pw_L (si_incidence z0) ^ 2 *
          pw_error (si_incidence z0) ^ 2) zs)
        <= Cchi ^ 2 * h_inv ^ 2 *
          sumR (map (fun z0 =>
          pw_error (si_incidence z0) ^ 2) zs)).
      {
        apply IH. intros z0 Hz0.
        apply Hbound. right. exact Hz0.
      }
      rewrite Rmult_plus_distr_l. lra.
  Qed.

  Lemma weighted_integrand_bound : forall x,
    local_weighted_l2 Cinf incidence_at x
      <= Cchi ^ 2 * h_inv ^ 2 *
          local_squared_l2 Cinf incidence_at x.
  Proof.
    intro x.
    unfold local_weighted_l2, local_squared_l2.
    apply weighted_list_bound.
    intros z Hz. apply Hmultiplier with (x := x).
    exact Hz.
  Qed.

  Lemma weighted_energy_bound :
    integral I (local_weighted_l2 Cinf incidence_at)
      <= (Cchi ^ 2 * h_inv ^ 2) *
          integral I (local_squared_l2 Cinf incidence_at).
  Proof.
    pose proof
      (integral_monotone I
        (local_weighted_l2 Cinf incidence_at)
        (fun x => (Cchi ^ 2 * h_inv ^ 2) *
                  local_squared_l2 Cinf incidence_at x)
        weighted_integrand_bound) as H.
    rewrite (integral_scale I
      (Cchi ^ 2 * h_inv ^ 2)
      (local_squared_l2 Cinf incidence_at)) in H.
    exact H.
  Qed.

  Lemma l2_rate_after_loss :
    integral I (local_squared_l2 Cinf incidence_at)
      <= C0 * h_alpha * Rbound.
  Proof.
    eapply Rle_trans; [exact Hlocal_l2|].
    replace (C0 * h_r * Rbound)
      with ((C0 * Rbound) * h_r) by ring.
    replace (C0 * h_alpha * Rbound)
      with ((C0 * Rbound) * h_alpha) by ring.
    apply Rmult_le_compat_l.
    - apply Rmult_le_pos; assumption.
    - exact Hrate_loss.
  Qed.

  Lemma weighted_rate_after_loss :
    integral I (local_weighted_l2 Cinf incidence_at)
      <= Cchi ^ 2 * C0 * h_alpha * Rbound.
  Proof.
    eapply Rle_trans; [apply weighted_energy_bound|].
    eapply Rle_trans
      with (r2 := (Cchi ^ 2 * h_inv ^ 2) *
                    (C0 * h_r * Rbound)).
    - apply Rmult_le_compat_l.
      + apply Rmult_le_pos; apply pow2_ge_0.
      + exact Hlocal_l2.
    - replace ((Cchi ^ 2 * h_inv ^ 2) *
                 (C0 * h_r * Rbound))
        with ((Cchi ^ 2 * C0 * Rbound) *
              (h_inv ^ 2 * h_r)) by ring.
      replace (Cchi ^ 2 * C0 * h_alpha * Rbound)
        with ((Cchi ^ 2 * C0 * Rbound) * h_alpha) by ring.
      apply Rmult_le_compat_l.
      + apply Rmult_le_pos.
        * apply Rmult_le_pos.
          -- apply pow2_ge_0.
          -- exact HC0.
        * exact HR.
      + exact Hinverse_loss.
  Qed.

  (** This is the genuinely *derived* global squared energy bound. *)
  Theorem scale_sensitive_squared_72 :
    integral I (global_squared_integrand Cinf incidence_at)
      <= scale_squared_constant * h_alpha * Rbound.
  Proof.
    pose proof (integrated_localized_56 I Cinf kappa
      incidence_at Hoverlap) as Hglobal.
    pose proof l2_rate_after_loss as H0.
    pose proof weighted_rate_after_loss as Hw.
    pose proof Hlocal_deriv as H1.
    assert (HCinf2 : 0 <= Cinf ^ 2) by apply pow2_ge_0.
    assert (Hfirst :
       Cinf ^ 2 * integral I (local_squared_l2 Cinf incidence_at)
       <= Cinf ^ 2 * (C0 * h_alpha * Rbound)).
    { apply Rmult_le_compat_l; assumption. }
    assert (Hsecond :
       2 * integral I (local_weighted_l2 Cinf incidence_at)
       <= 2 * (Cchi ^ 2 * C0 * h_alpha * Rbound)).
    { apply Rmult_le_compat_l; [lra|exact Hw]. }
    assert (Hthird :
       2 * Cinf ^ 2 *
        integral I (local_squared_derivative Cinf incidence_at)
       <= (2 * Cinf ^ 2) * (C1 * h_alpha * Rbound)).
    { apply Rmult_le_compat_l; [nra|exact H1]. }
    assert (Hinside :
      Cinf ^ 2 * integral I (local_squared_l2 Cinf incidence_at)
      + 2 * integral I (local_weighted_l2 Cinf incidence_at)
      + 2 * Cinf ^ 2 *
        integral I (local_squared_derivative Cinf incidence_at)
      <= (Cinf ^ 2 * (C0 * h_alpha * Rbound)
          + 2 * (Cchi ^ 2 * C0 * h_alpha * Rbound)
          + (2 * Cinf ^ 2) * (C1 * h_alpha * Rbound))).
    { lra. }
    eapply Rle_trans; [exact Hglobal|].
    unfold scale_squared_constant.
    replace
      (INR kappa * ((Cinf ^ 2 + 2 * Cchi ^ 2) * C0
        + 2 * Cinf ^ 2 * C1) * h_alpha * Rbound)
      with
      (INR kappa *
        (Cinf ^ 2 * (C0 * h_alpha * Rbound)
          + 2 * (Cchi ^ 2 * C0 * h_alpha * Rbound)
          + (2 * Cinf ^ 2) * (C1 * h_alpha * Rbound)))
      by ring.
    apply Rmult_le_compat_l.
    - apply pos_INR.
    - exact Hinside.
  Qed.

  (** Norm estimate with an explicit admissible constant. It does
      not construct a Sobolev norm or establish the local rates. *)
  Theorem norm_scale_sensitive_72 :
    forall error_norm h_rate source_norm Cstar,
      0 <= error_norm ->
      0 <= h_rate ->
      0 <= source_norm ->
      0 <= Cstar ->
      error_norm ^ 2 =
        integral I (global_squared_integrand Cinf incidence_at) ->
      h_alpha = h_rate ^ 2 ->
      Rbound = source_norm ^ 2 ->
      scale_squared_constant <= Cstar ^ 2 ->
      error_norm <= Cstar * h_rate * source_norm.
  Proof.
    intros error_norm h_rate source_norm Cstar
      Herr Hrate Hsource HCstar Hsq Halpha Hsource2 Hconst.
    pose proof scale_sensitive_squared_72 as Hglobal.
    rewrite <- Hsq in Hglobal.
    rewrite Halpha, Hsource2 in Hglobal.
    assert (Hproduct : 0 <= h_rate ^ 2 * source_norm ^ 2).
    { apply Rmult_le_pos; apply pow2_ge_0. }
    assert (Hconstmul :
      scale_squared_constant * (h_rate ^ 2 * source_norm ^ 2)
      <= Cstar ^ 2 * (h_rate ^ 2 * source_norm ^ 2)).
    { apply Rmult_le_compat_r; assumption. }
    assert (Hsquare :
      error_norm ^ 2 <= (Cstar * h_rate * source_norm) ^ 2).
    {
      eapply Rle_trans.
      - exact Hglobal.
      - replace
          (scale_squared_constant * h_rate ^ 2 * source_norm ^ 2)
          with (scale_squared_constant *
                (h_rate ^ 2 * source_norm ^ 2)) by ring.
        replace ((Cstar * h_rate * source_norm) ^ 2)
          with (Cstar ^ 2 * (h_rate ^ 2 * source_norm ^ 2)) by ring.
        exact Hconstmul.
    }
    assert (Htarget : 0 <= Cstar * h_rate * source_norm).
    { apply Rmult_le_pos.
      - apply Rmult_le_pos; assumption.
      - exact Hsource. }
    nra.
  Qed.
End Scale.

End UELAT_V3_PUFEMScaleBridge.
