(** EffectiveCoordinateSequence.v -- ambient effective Hilbert-cube coordinates versus admissible dual-ball points.

    Co-c.e.-closedness must talk about coordinate sequences both inside and
    outside the dual ball, so effectivity is attached first to arbitrary
    coordinate sequences and admissibility is a separate subtype.
*)

From Coq Require Import Reals QArith Qreals.
From UELAT.V3 Require Import
  RepresentedSpace ComputableBanach DualBallCoordinates CoordinateDualBall.

Module UELAT_V3_EffectiveCoordinateSequence.
Import UELAT_V3_RepresentedSpace.
Import UELAT_V3_ComputableBanach.
Import UELAT_V3_DualBallCoordinates.
Import UELAT_V3_CoordinateDualBall.

Section EffectiveSequences.
  Variable B : RealComputableBanachPresentation.

  Record EffectiveCoordinateSequence := {
    ecs_values : CoordinatePoint;
    ecs_approx : nat -> nat -> Q;
    ecs_approx_sound : forall i n,
      Rabs (Q2R (ecs_approx i n) - ecs_values i) <= dyadic n
  }.

  Definition EffectiveCoordinateBallPoint :=
    { a : EffectiveCoordinateSequence | CoordinateAdmissible B (ecs_values a) }.

  Definition effective_ball_coordinate_point
      (a : EffectiveCoordinateBallPoint) : CoordinateDualBallPoint B :=
    {| cdb_coordinates := ecs_values (proj1_sig a);
       cdb_admissible := proj2_sig a |}.

  Definition effective_ball_approx
      (a : EffectiveCoordinateBallPoint) : nat -> nat -> Q :=
    ecs_approx (proj1_sig a).

  Theorem effective_ball_approx_sound : forall a i n,
    Rabs
      (Q2R (effective_ball_approx a i n)
       - cdb_coordinates B (effective_ball_coordinate_point a) i)
      <= dyadic n.
  Proof.
    intros a i n. unfold effective_ball_approx, effective_ball_coordinate_point.
    simpl. apply ecs_approx_sound.
  Qed.
End EffectiveSequences.

End UELAT_V3_EffectiveCoordinateSequence.
