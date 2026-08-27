(** ApproximateHahnBanachInterface.v -- semantic bounded-functional adapter.

    This older-style interface remains useful for coordinate lemmas that need
    only bounded linear semantics. It is NOT the authoritative machine contract
    for Lemma 3.1: that role belongs to ApproximateHahnBanachStrongInterface.v,
    whose outputs carry literal rational Type-2 realizers.
*)

From Coq Require Import Reals QArith Qreals.
From UELAT.V3 Require Import CertificateEnrichment ComputableBanach.

Module UELAT_V3_ApproximateHahnBanachInterface.
Import UELAT_V3_CertificateEnrichment.
Import UELAT_V3_ComputableBanach.

Section Functionals.
  Variable B : RealComputableBanachPresentation.
  Let X := carrier (cb_metric B).

  Record ComputableBoundedFunctional := {
    cbf_apply : X -> R;
    cbf_add : forall x y,
      cbf_apply (cb_add B x y) = cbf_apply x + cbf_apply y;
    cbf_scale : forall a x,
      cbf_apply (cb_scale B a x) = a * cbf_apply x;
    cbf_norm_bound : R;
    cbf_norm_bound_nonnegative : 0 <= cbf_norm_bound;
    cbf_bounded : forall x,
      Rabs (cbf_apply x) <= cbf_norm_bound * distance x (cb_zero B);
    cbf_realizer : Type
  }.

  Arguments cbf_apply _ _.
  Arguments cbf_norm_bound _.

  Record EffectiveApproxHahnBanach := {
    ahb_extend : forall (v : X) (eta : Q), ComputableBoundedFunctional;
    ahb_hits_norm : forall v eta,
      0 < distance v (cb_zero B) -> (0 < eta)%Q ->
      cbf_apply (ahb_extend v eta) v = distance v (cb_zero B);
    ahb_small_norm_loss : forall v eta,
      0 < distance v (cb_zero B) -> (0 < eta)%Q ->
      cbf_norm_bound (ahb_extend v eta) <= 1 + Q2R eta
  }.

  Variable AHB : EffectiveApproxHahnBanach.

  Theorem approximate_hahn_banach_contract : forall v eta,
    0 < distance v (cb_zero B) -> (0 < eta)%Q ->
    exists g : ComputableBoundedFunctional,
      cbf_apply g v = distance v (cb_zero B)
      /\ cbf_norm_bound g <= 1 + Q2R eta.
  Proof.
    intros v eta Hv Heta.
    exists (ahb_extend AHB v eta). split.
    - now apply ahb_hits_norm.
    - now apply ahb_small_norm_loss.
  Qed.
End Functionals.

End UELAT_V3_ApproximateHahnBanachInterface.
