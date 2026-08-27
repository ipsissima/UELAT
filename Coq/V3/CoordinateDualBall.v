(** CoordinateDualBall.v -- coordinate compactum underlying authoritative
    Theorem 3.2, Step 2. *)

From Coq Require Import Reals QArith Qreals List Lra.
Import ListNotations.
Local Open Scope Q_scope.
From UELAT.V3 Require Import
  CertificateEnrichment ComputableBanach RealizedBoundedFunctional
  NormalizedCoreCoordinates RealizedDualCoordinates.

Module UELAT_V3_CoordinateDualBall.
Import UELAT_V3_CertificateEnrichment.
Import UELAT_V3_ComputableBanach.
Import UELAT_V3_RealizedBoundedFunctional.
Import UELAT_V3_NormalizedCoreCoordinates.
Import UELAT_V3_RealizedDualCoordinates.

Section CoordinateBall.
  Variable B : RealComputableBanachPresentation.

  Record CoordinateDualBallPoint := {
    cdb_coordinates : CoordinatePoint;
    cdb_admissible : CoordinateAdmissible B cdb_coordinates
  }.
  Arguments cdb_coordinates _.

  Lemma combination_single_decode : forall i,
    core_decode (combination_code B [(1,i)]) = normalized_core B i.
  Proof.
    intro i. simpl.
    rewrite core_add_sound, core_scale_sound, core_zero_sound.
    change (Q2R (1 : Q)) with 1%R.
    rewrite cb_scale_one, cb_add_zero_r. reflexivity.
  Qed.

  Lemma coordinate_single_sum : forall a i,
    coordinate_sum a [(1,i)] = a i.
  Proof. intros. simpl. change (Q2R (1 : Q)) with 1%R. ring. Qed.

  Theorem admissible_coordinate_strictly_bounded :
    forall (a : CoordinateDualBallPoint) i,
      Rabs (cdb_coordinates a i) < 1.
  Proof.
    intros [a Hadm] i. simpl.
    specialize (Hadm [(1,i)]).
    rewrite coordinate_single_sum in Hadm.
    rewrite combination_single_decode in Hadm.
    eapply Rle_lt_trans; [exact Hadm|].
    apply normalized_enumerated_core_norm_lt_one.
  Qed.

  Definition coordinates_of_realized_functional
      (g : RealizedBoundedFunctional B)
      (Hg : forall x, Rabs (rbf_apply g x) <= cb_norm B x) :
      CoordinateDualBallPoint :=
    {| cdb_coordinates := functional_coordinates B g;
       cdb_admissible := realized_functional_coordinates_admissible B g Hg |}.

  Theorem realized_functional_coordinate_value : forall g Hg i,
    cdb_coordinates (coordinates_of_realized_functional g Hg) i
      = rbf_apply g (normalized_core B i).
  Proof. reflexivity. Qed.

  Theorem realized_contracting_functionals_land_in_coordinate_ball :
    forall g,
      (forall x, Rabs (rbf_apply g x) <= cb_norm B x) ->
      exists a : CoordinateDualBallPoint,
        forall i, cdb_coordinates a i = rbf_apply g (normalized_core B i).
  Proof.
    intros g Hg.
    exists (coordinates_of_realized_functional g Hg).
    intro i. reflexivity.
  Qed.
End CoordinateBall.

End UELAT_V3_CoordinateDualBall.
