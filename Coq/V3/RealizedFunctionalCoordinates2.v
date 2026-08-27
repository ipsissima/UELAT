(** RealizedFunctionalCoordinates2.v -- strong bridge from a realized
    contracting functional to an effective coordinate-dual-ball point. *)

From Coq Require Import Reals QArith Qreals.
From UELAT.V3 Require Import
  CertificateEnrichment RepresentedSpace ComputableBanach
  RealizedBoundedFunctional CoreConstantName NormalizedCoreCoordinates
  RealizedDualCoordinates CoordinateDualBall EffectiveCoordinateSequence.

Module UELAT_V3_RealizedFunctionalCoordinates2.
Import UELAT_V3_CertificateEnrichment.
Import UELAT_V3_RepresentedSpace.
Import UELAT_V3_ComputableBanach.
Import UELAT_V3_RealizedBoundedFunctional.
Import UELAT_V3_CoreConstantName.
Import UELAT_V3_NormalizedCoreCoordinates.
Import UELAT_V3_RealizedDualCoordinates.
Import UELAT_V3_CoordinateDualBall.
Import UELAT_V3_EffectiveCoordinateSequence.

Section Coordinates.
  Variable B : RealComputableBanachPresentation.
  Variable g : RealizedBoundedFunctional B.
  Hypothesis g_contracting : forall x,
    Rabs (rbf_apply g x) <= cb_norm B x.

  Definition realized_coordinate_values : CoordinatePoint :=
    functional_coordinates B g.

  Definition realized_coordinate_approx (i n : nat) : Q :=
    rbf_realize g
      (constant_core_fast_name B
        (normalized_core_code B (core_enum B i))) n.

  Theorem realized_coordinate_approx_sound : forall i n,
    Rabs
      (Q2R (realized_coordinate_approx i n)
       - realized_coordinate_values i)
      <= dyadic n.
  Proof.
    intros i n.
    unfold realized_coordinate_approx, realized_coordinate_values,
      functional_coordinates, normalized_core.
    pose proof
      (rbf_realize_correct g
        (constant_core_named_point B
          (normalized_core_code B (core_enum B i))) n) as H.
    simpl in H. exact H.
  Qed.

  Definition realized_effective_coordinates : EffectiveCoordinateSequence B :=
    {| ecs_values := realized_coordinate_values;
       ecs_approx := realized_coordinate_approx;
       ecs_approx_sound := realized_coordinate_approx_sound |}.

  Theorem realized_coordinate_admissible :
    CoordinateAdmissible B realized_coordinate_values.
  Proof.
    unfold realized_coordinate_values.
    apply realized_functional_coordinates_admissible.
    exact g_contracting.
  Qed.

  Definition realized_effective_ball_point : EffectiveCoordinateBallPoint B :=
    exist _ realized_effective_coordinates realized_coordinate_admissible.

  Theorem realized_functional_coordinates_are_effectively_in_ball :
    exists a : EffectiveCoordinateBallPoint B,
      forall i,
        ecs_values B (proj1_sig a) i = rbf_apply g (normalized_core B i).
  Proof.
    exists realized_effective_ball_point. intro i. reflexivity.
  Qed.

  Theorem realized_coordinate_stage_tracks_functional : forall i n,
    Rabs
      (Q2R (ecs_approx B (proj1_sig realized_effective_ball_point) i n)
       - rbf_apply g (normalized_core B i))
      <= dyadic n.
  Proof. intros i n. exact (realized_coordinate_approx_sound i n). Qed.
End Coordinates.

End UELAT_V3_RealizedFunctionalCoordinates2.
