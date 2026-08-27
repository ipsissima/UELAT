(** RealizedDualCoordinates.v -- realized contracting functionals satisfy the
    finite coordinate inequalities of Step 2. *)

From Coq Require Import Reals QArith Qreals List Lra.
From UELAT.V3 Require Import
  CertificateEnrichment ComputableBanach RealizedBoundedFunctional
  NormalizedCoreCoordinates.

Module UELAT_V3_RealizedDualCoordinates.
Import UELAT_V3_CertificateEnrichment.
Import UELAT_V3_ComputableBanach.
Import UELAT_V3_RealizedBoundedFunctional.
Import UELAT_V3_NormalizedCoreCoordinates.

Section FunctionalCoordinates.
  Variable B : RealComputableBanachPresentation.
  Variable g : RealizedBoundedFunctional B.

  Lemma realized_functional_zero : rbf_apply g (cb_zero B) = 0.
  Proof.
    pose proof (rbf_scale g 0 (cb_zero B)) as H.
    rewrite cb_scale_zero_scalar in H. lra.
  Qed.

  Definition functional_coordinates : CoordinatePoint :=
    fun i => rbf_apply g (normalized_core B i).

  Lemma functional_combination_value : forall terms,
    rbf_apply g (core_decode (combination_code B terms))
      = coordinate_sum functional_coordinates terms.
  Proof.
    induction terms as [|[q i] rest IH]; simpl.
    - rewrite core_zero_sound. apply realized_functional_zero.
    - rewrite core_add_sound, core_scale_sound.
      rewrite rbf_add, rbf_scale, IH. reflexivity.
  Qed.

  Hypothesis g_contracting : forall x,
    Rabs (rbf_apply g x) <= cb_norm B x.

  Theorem realized_functional_coordinates_admissible :
    CoordinateAdmissible B functional_coordinates.
  Proof.
    intro terms. rewrite <- functional_combination_value. apply g_contracting.
  Qed.

  Theorem realized_functional_coordinates_bounded : forall i,
    Rabs (functional_coordinates i) < 1.
  Proof.
    intro i. eapply Rle_lt_trans.
    - apply g_contracting.
    - apply normalized_enumerated_core_norm_lt_one.
  Qed.
End FunctionalCoordinates.

End UELAT_V3_RealizedDualCoordinates.
