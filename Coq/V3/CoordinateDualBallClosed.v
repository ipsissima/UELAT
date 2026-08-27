(** CoordinateDualBallClosed.v -- finite-constraint complement of the
    coordinate dual ball. *)

From Coq Require Import Reals QArith List Classical Lra.
Import ListNotations.
From UELAT.V3 Require Import
  CertificateEnrichment ComputableBanach
  NormalizedCoreCoordinates CoordinateDualBall.

Module UELAT_V3_CoordinateDualBallClosed.
Import UELAT_V3_CertificateEnrichment.
Import UELAT_V3_ComputableBanach.
Import UELAT_V3_NormalizedCoreCoordinates.
Import UELAT_V3_CoordinateDualBall.

Section Violations.
  Variable B : RealComputableBanachPresentation.

  Definition CoordinateViolation
      (a : CoordinatePoint) (terms : list RationalCoordinateTerm) : Prop :=
    cb_norm B (core_decode (combination_code B terms))
      < Rabs (coordinate_sum a terms).

  Theorem violation_excludes_admissibility : forall a terms,
    CoordinateViolation a terms -> ~ CoordinateAdmissible B a.
  Proof.
    intros a terms Hviol Hadm.
    specialize (Hadm terms). unfold CoordinateViolation in Hviol. lra.
  Qed.

  Theorem nonadmissible_has_finite_violation : forall a,
    ~ CoordinateAdmissible B a ->
    exists terms, CoordinateViolation a terms.
  Proof.
    intros a Hnot. unfold CoordinateAdmissible in Hnot.
    apply not_all_ex_not in Hnot. destruct Hnot as [terms Hterms].
    exists terms. unfold CoordinateViolation. apply Rnot_le_lt. exact Hterms.
  Qed.

  Theorem admissible_iff_no_finite_violation : forall a,
    CoordinateAdmissible B a <-> forall terms, ~ CoordinateViolation a terms.
  Proof.
    intro a. split.
    - intros Hadm terms Hviol. exact (violation_excludes_admissibility a terms Hviol Hadm).
    - intros Hnone terms. apply Rnot_lt_le. intro Hviol. exact (Hnone terms Hviol).
  Qed.
End Violations.

Section EffectiveViolation.
  Variable B : RealComputableBanachPresentation.
  Context {CoordName : Type}.
  Variable decode_coord_name : CoordName -> CoordinatePoint.

  Record FiniteViolationSemidecider := {
    violation_stage : CoordName -> list RationalCoordinateTerm -> nat -> bool;
    violation_stage_sound : forall nu terms s,
      violation_stage nu terms s = true ->
      CoordinateViolation B (decode_coord_name nu) terms;
    violation_stage_complete : forall nu terms,
      CoordinateViolation B (decode_coord_name nu) terms ->
      exists s, violation_stage nu terms s = true
  }.

  Variable V : FiniteViolationSemidecider.

  Record EffectiveTermEnumeration := {
    term_enum : nat -> list RationalCoordinateTerm;
    term_enum_surjective : forall terms, exists n, term_enum n = terms
  }.

  Variable E : EffectiveTermEnumeration.

  Definition complement_stage_test
      (nu : CoordName) (term_index precision : nat) : bool :=
    violation_stage V nu (term_enum E term_index) precision.

  Theorem complement_stage_sound : forall nu i s,
    complement_stage_test nu i s = true ->
    ~ CoordinateAdmissible B (decode_coord_name nu).
  Proof.
    intros nu i s H.
    apply violation_excludes_admissibility with (terms := term_enum E i).
    now apply violation_stage_sound in H.
  Qed.

  Theorem nonadmissible_eventually_violates : forall nu,
    ~ CoordinateAdmissible B (decode_coord_name nu) ->
    exists i s, complement_stage_test nu i s = true.
  Proof.
    intros nu Hnot.
    destruct (nonadmissible_has_finite_violation B _ Hnot) as [terms Hviol].
    destruct (term_enum_surjective E terms) as [i Hi].
    destruct (violation_stage_complete V nu terms Hviol) as [s Hs].
    exists i, s. unfold complement_stage_test. now rewrite Hi.
  Qed.

  Theorem coordinate_ball_has_effective_violation_basis : forall nu,
    (~ CoordinateAdmissible B (decode_coord_name nu) ->
       exists i s, complement_stage_test nu i s = true)
    /\ (forall i s,
       complement_stage_test nu i s = true ->
       ~ CoordinateAdmissible B (decode_coord_name nu)).
  Proof.
    intro nu. split.
    - apply nonadmissible_eventually_violates.
    - apply complement_stage_sound.
  Qed.
End EffectiveViolation.

End UELAT_V3_CoordinateDualBallClosed.
