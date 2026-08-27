(** ScaleSensitivePUFEMAnalytic.v -- standard analytic derivation for v3 Theorem 7.2. *)

From Coq Require Import Reals Lra Ring.
Local Open Scope R_scope.

Module UELAT_V3_ScaleSensitivePUFEMAnalytic.
Section ClassicalRate.
  Variables kappa Cchi C0 C1 : R.
  Variables h_r h_alpha h_inv Rbound : R.
  Hypothesis Hkappa : 0 <= kappa.
  Hypothesis HCchi : 0 <= Cchi.
  Hypothesis HC0 : 0 <= C0.
  Hypothesis HC1 : 0 <= C1.
  Hypothesis Hhr : 0 <= h_r.
  Hypothesis Hha : 0 <= h_alpha.
  Hypothesis Hhinv : 0 <= h_inv.
  Hypothesis HR : 0 <= Rbound.
  Hypothesis power_loss_one : h_r <= h_alpha.
  Hypothesis inverse_times_high_order : h_inv * h_r <= h_alpha.

  Record ScaleSensitiveAnalyticData := {
    local_l2_aggregate : R;
    local_deriv_aggregate : R;
    global_l2_error : R;
    global_deriv_error : R;
    global_w12_error : R;
    local_l2_nonnegative : 0 <= local_l2_aggregate;
    local_deriv_nonnegative : 0 <= local_deriv_aggregate;
    global_l2_nonnegative : 0 <= global_l2_error;
    global_deriv_nonnegative : 0 <= global_deriv_error;
    global_w12_nonnegative : 0 <= global_w12_error;
    local_l2_rate : local_l2_aggregate <= C0 * h_r * Rbound;
    local_deriv_rate : local_deriv_aggregate <= C1 * h_alpha * Rbound;
    global_l2_from_overlap : global_l2_error <= kappa * local_l2_aggregate;
    global_deriv_from_product_rule :
      global_deriv_error <=
        kappa * (Cchi * h_inv * local_l2_aggregate + local_deriv_aggregate);
    global_w12_from_components :
      global_w12_error <= global_l2_error + global_deriv_error
  }.

  Definition scale_Cstar : R := kappa * ((1 + Cchi) * C0 + C1).
  Lemma scale_Cstar_nonnegative : 0 <= scale_Cstar.
  Proof.
    unfold scale_Cstar.
    apply Rmult_le_pos; [exact Hkappa|].
    apply Rplus_le_le_0_compat.
    - apply Rmult_le_pos; [lra|exact HC0].
    - exact HC1.
  Qed.

  Variable D : ScaleSensitiveAnalyticData.

  Lemma global_l2_rate_derived :
    global_l2_error D <= kappa * C0 * h_alpha * Rbound.
  Proof.
    assert (HC0R : 0 <= C0 * Rbound) by nra.
    assert (Hlocal : local_l2_aggregate D <= C0 * h_alpha * Rbound).
    {
      eapply Rle_trans; [exact (local_l2_rate D)|].
      replace (C0 * h_r * Rbound) with ((C0 * Rbound) * h_r) by ring.
      replace (C0 * h_alpha * Rbound) with ((C0 * Rbound) * h_alpha) by ring.
      exact (Rmult_le_compat_l (C0 * Rbound) h_r h_alpha HC0R power_loss_one).
    }
    eapply Rle_trans; [exact (global_l2_from_overlap D)|].
    replace (kappa * C0 * h_alpha * Rbound)
      with (kappa * (C0 * h_alpha * Rbound)) by ring.
    exact (Rmult_le_compat_l kappa
      (local_l2_aggregate D) (C0 * h_alpha * Rbound) Hkappa Hlocal).
  Qed.

  Lemma global_deriv_rate_derived :
    global_deriv_error D <=
      kappa * (Cchi * C0 + C1) * h_alpha * Rbound.
  Proof.
    assert (Hchiinv : 0 <= Cchi * h_inv) by nra.
    assert (Hfactor : 0 <= Cchi * C0 * Rbound) by nra.
    assert (Hweighted :
      Cchi * h_inv * local_l2_aggregate D
        <= Cchi * C0 * h_alpha * Rbound).
    {
      eapply Rle_trans.
      - exact (Rmult_le_compat_l (Cchi * h_inv)
          (local_l2_aggregate D) (C0 * h_r * Rbound)
          Hchiinv (local_l2_rate D)).
      - replace ((Cchi * h_inv) * (C0 * h_r * Rbound))
          with ((Cchi * C0 * Rbound) * (h_inv * h_r)) by ring.
        replace (Cchi * C0 * h_alpha * Rbound)
          with ((Cchi * C0 * Rbound) * h_alpha) by ring.
        exact (Rmult_le_compat_l (Cchi * C0 * Rbound)
          (h_inv * h_r) h_alpha Hfactor inverse_times_high_order).
    }
    assert (Hinside :
      Cchi * h_inv * local_l2_aggregate D + local_deriv_aggregate D
        <= Cchi * C0 * h_alpha * Rbound + C1 * h_alpha * Rbound).
    {
      apply Rplus_le_compat.
      - exact Hweighted.
      - exact (local_deriv_rate D).
    }
    eapply Rle_trans; [exact (global_deriv_from_product_rule D)|].
    replace (kappa * (Cchi * C0 + C1) * h_alpha * Rbound)
      with (kappa *
        (Cchi * C0 * h_alpha * Rbound + C1 * h_alpha * Rbound)) by ring.
    exact (Rmult_le_compat_l kappa _ _ Hkappa Hinside).
  Qed.

  Theorem classical_scale_sensitive_pufem_estimate :
    global_w12_error D <= scale_Cstar * h_alpha * Rbound.
  Proof.
    eapply Rle_trans; [exact (global_w12_from_components D)|].
    eapply Rle_trans.
    - apply Rplus_le_compat.
      + exact global_l2_rate_derived.
      + exact global_deriv_rate_derived.
    - unfold scale_Cstar.
      replace (kappa * ((1 + Cchi) * C0 + C1) * h_alpha * Rbound)
        with (kappa * C0 * h_alpha * Rbound
              + kappa * (Cchi * C0 + C1) * h_alpha * Rbound) by ring.
      reflexivity.
  Qed.

  Theorem scale_sensitive_rate_loses_exactly_one_power :
    global_w12_error D <=
      kappa * ((1 + Cchi) * C0 + C1) * h_alpha * Rbound.
  Proof. exact classical_scale_sensitive_pufem_estimate. Qed.
End ClassicalRate.
End UELAT_V3_ScaleSensitivePUFEMAnalytic.
