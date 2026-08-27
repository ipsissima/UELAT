(** Refinement.v -- scale-sensitive analytic rate algebra for authoritative Theorem 7.2.

    Formalizes the quantitative combination step after the standard
    bounded-overlap and product-rule estimates supply the L2 and derivative
    bounds, including C_* = kappa*((1+C_chi)C0+C1) and loss of one h power.
*)

From Coq Require Import Reals Lra Nra.

Module UELAT_V3_Refinement.

Section ScaleSensitive.
  Variables kappa Cchi C0 C1 : R.
  Variables h_r h_alpha Rbound : R.
  Hypothesis Hkappa : 0 <= kappa.
  Hypothesis HCchi : 0 <= Cchi.
  Hypothesis HC0 : 0 <= C0.
  Hypothesis HC1 : 0 <= C1.
  Hypothesis Hhr : 0 <= h_r.
  Hypothesis Hha : 0 <= h_alpha.
  Hypothesis HR : 0 <= Rbound.
  Hypothesis power_loss_one : h_r <= h_alpha.

  Definition Cstar : R := kappa * ((1 + Cchi) * C0 + C1).

  Lemma Cstar_nonnegative : 0 <= Cstar.
  Proof. unfold Cstar. nra. Qed.

  Theorem scale_sensitive_pufem_from_components
      (l2_error deriv_error w12_error : R) :
    0 <= l2_error -> 0 <= deriv_error -> 0 <= w12_error ->
    l2_error <= kappa * C0 * h_r * Rbound ->
    deriv_error <= kappa * (Cchi * C0 + C1) * h_alpha * Rbound ->
    w12_error <= l2_error + deriv_error ->
    w12_error <= Cstar * h_alpha * Rbound.
  Proof.
    intros Hl2 Hd Hw Hl2b Hdb Hw12.
    unfold Cstar. nra.
  Qed.

  Theorem scale_rate_is_stable_under_weaker_bound
      (e e' : R) :
    0 <= e -> e <= e' -> e' <= Cstar * h_alpha * Rbound ->
    e <= Cstar * h_alpha * Rbound.
  Proof. intros. lra. Qed.
End ScaleSensitive.

End UELAT_V3_Refinement.
