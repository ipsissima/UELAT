(** CoordinateViolationSemidecision3.v -- genuine ambient finite-violation
    semidecider for the coordinate dual ball. *)

From Coq Require Import Reals QArith Qreals List Bool Lra Nra Ring Field.
Import ListNotations.
Local Open Scope Q_scope.
From UELAT.V3 Require Import
  CertificateEnrichment RepresentedSpace ComputableBanach
  DyadicVanishing GenericSlackCertification
  NormalizedCoreCoordinates CoordinateDualBallClosed EffectiveCoordinateSequence.

Module UELAT_V3_CoordinateViolationSemidecision3.
Import UELAT_V3_CertificateEnrichment.
Import UELAT_V3_RepresentedSpace.
Import UELAT_V3_ComputableBanach.
Import UELAT_V3_DyadicVanishing.
Import UELAT_V3_GenericSlackCertification.
Import UELAT_V3_NormalizedCoreCoordinates.
Import UELAT_V3_CoordinateDualBallClosed.
Import UELAT_V3_EffectiveCoordinateSequence.

Definition qabs_exact (q : Q) : Q :=
  if Qlt_le_dec q 0 then -q else q.

Lemma qabs_exact_real : forall q,
  Q2R (qabs_exact q) = Rabs (Q2R q).
Proof.
  intro q. unfold qabs_exact.
  destruct (Qlt_le_dec q 0) as [Hneg|Hnonneg].
  - rewrite Q2R_opp, Rabs_left; [reflexivity|now apply Qlt_Rlt].
  - rewrite Rabs_right; [reflexivity|now apply Qle_Rle].
Qed.

Fixpoint coefficient_weight_Q
    (terms : list RationalCoordinateTerm) : Q :=
  match terms with
  | [] => 0
  | (q,_) :: rest => qabs_exact q + coefficient_weight_Q rest
  end.

Lemma coefficient_weight_Q_nonnegative : forall terms,
  (0 <= coefficient_weight_Q terms)%Q.
Proof.
  induction terms as [|[q i] rest IH]; simpl.
  - reflexivity.
  - apply Qplus_le_0_compat.
    + apply Rle_Qle. rewrite qabs_exact_real. apply Rabs_pos.
    + exact IH.
Qed.

Section Test.
  Variable B : RealComputableBanachPresentation.

  Fixpoint coordinate_sum_approx_Q
      (a : EffectiveCoordinateSequence B)
      (terms : list RationalCoordinateTerm) (s : nat) : Q :=
    match terms with
    | [] => 0
    | (q,i) :: rest =>
        q * ecs_approx B a i s + coordinate_sum_approx_Q a rest s
    end.

  Lemma coordinate_sum_approx_error : forall a terms s,
    Rabs
      (Q2R (coordinate_sum_approx_Q a terms s)
       - coordinate_sum (ecs_values B a) terms)
      <= Q2R (coefficient_weight_Q terms) * dyadic s.
  Proof.
    intros a terms.
    induction terms as [|[q i] rest IH]; intro s; simpl.
    - rewrite Rabs_R0. nra.
    - repeat rewrite Q2R_plus. rewrite Q2R_mult.
      replace
        (Q2R q * Q2R (ecs_approx B a i s)
         + Q2R (coordinate_sum_approx_Q a rest s)
         - (Q2R q * ecs_values B a i
            + coordinate_sum (ecs_values B a) rest))
        with
        (Q2R q * (Q2R (ecs_approx B a i s) - ecs_values B a i)
         + (Q2R (coordinate_sum_approx_Q a rest s)
            - coordinate_sum (ecs_values B a) rest)) by ring.
      eapply Rle_trans; [apply Rabs_triang|].
      rewrite Rabs_mult.
      pose proof (ecs_approx_sound B a i s) as Hi.
      pose proof (IH s) as Hr.
      rewrite Q2R_plus, qabs_exact_real.
      apply Rplus_le_compat.
      + apply Rmult_le_compat_l; [apply Rabs_pos|exact Hi].
      + exact Hr.
  Qed.

  Definition violation_stage_test
      (a : EffectiveCoordinateSequence B)
      (terms : list RationalCoordinateTerm) (s : nat) : bool :=
    let normq := core_norm_approx B (combination_code B terms) s in
    let sumq := coordinate_sum_approx_Q a terms s in
    let errq := coefficient_weight_Q terms * qdyadic s in
    qltb (normq + qdyadic s + errq) (qabs_exact sumq).

  Theorem violation_stage_test_sound : forall a terms s,
    violation_stage_test a terms s = true ->
    CoordinateViolation B (ecs_values B a) terms.
  Proof.
    intros a terms s Htest.
    unfold violation_stage_test in Htest.
    apply qltb_true_iff in Htest.
    pose proof (Qlt_Rlt _ _ Htest) as HtestR.
    repeat rewrite Q2R_plus in HtestR.
    rewrite Q2R_mult, qdyadic_real, qabs_exact_real in HtestR.
    pose proof (core_norm_approx_sound B (combination_code B terms) s) as Hnorm.
    pose proof (coordinate_sum_approx_error a terms s) as Hsum.
    set (N := cb_norm B (core_decode (combination_code B terms))).
    set (A := coordinate_sum (ecs_values B a) terms).
    set (Qn := Q2R (core_norm_approx B (combination_code B terms) s)).
    set (Qs := Q2R (coordinate_sum_approx_Q a terms s)).
    set (W := Q2R (coefficient_weight_Q terms)).
    change (Rabs (Qn-N) <= dyadic s) in Hnorm.
    change (Rabs (Qs-A) <= W*dyadic s) in Hsum.
    assert (HN : N <= Qn + dyadic s).
    { pose proof (Rle_abs (N-Qn)) as Habs.
      replace (N-Qn) with (-(Qn-N)) in Habs by ring.
      rewrite Rabs_Ropp in Habs. lra. }
    assert (HQA : Rabs Qs <= Rabs A + W*dyadic s).
    { replace Qs with ((Qs-A)+A) by ring.
      eapply Rle_trans; [apply Rabs_triang|]. lra. }
    unfold CoordinateViolation. fold N A. lra.
  Qed.

  Theorem violation_stage_test_eventually : forall a terms,
    CoordinateViolation B (ecs_values B a) terms ->
    exists s, violation_stage_test a terms s = true.
  Proof.
    intros a terms Hviol.
    unfold CoordinateViolation in Hviol.
    set (N := cb_norm B (core_decode (combination_code B terms))) in *.
    set (A := coordinate_sum (ecs_values B a) terms) in *.
    set (W := Q2R (coefficient_weight_Q terms)).
    assert (HW : 0 <= W).
    { unfold W. apply Qle_Rle. apply coefficient_weight_Q_nonnegative. }
    assert (Hgap : 0 < Rabs A - N) by lra.
    destruct (dyadic_eventually_below
      ((Rabs A-N)/(2*W+3))
      ltac:(apply Rdiv_lt_0_compat; [exact Hgap|nra])) as [s Hsmall].
    pose proof (core_norm_approx_sound B (combination_code B terms) s) as Hnorm.
    pose proof (coordinate_sum_approx_error a terms s) as Hsum.
    set (Qn := Q2R (core_norm_approx B (combination_code B terms) s)).
    set (Qs := Q2R (coordinate_sum_approx_Q a terms s)).
    change (Rabs (Qn-N) <= dyadic s) in Hnorm.
    change (Rabs (Qs-A) <= W*dyadic s) in Hsum.
    assert (HQn : Qn <= N + dyadic s).
    { pose proof (Rle_abs (Qn-N)) as Habs. lra. }
    assert (HQs : Rabs A - W*dyadic s <= Rabs Qs).
    { assert (Hsym : Rabs (A-Qs) <= W*dyadic s).
      { replace (A-Qs) with (-(Qs-A)) by ring.
        rewrite Rabs_Ropp. exact Hsum. }
      pose proof (Rabs_triang (A-Qs) Qs) as Htri.
      replace (A-Qs+Qs) with A in Htri by ring. lra. }
    assert (Herr : (2*W+3)*dyadic s < Rabs A-N).
    { apply (Rmult_lt_reg_r (/ (2*W+3))).
      - apply Rinv_0_lt_compat. nra.
      - replace (((2*W+3)*dyadic s) * / (2*W+3))
          with (dyadic s) by (field; nra).
        exact Hsmall. }
    exists s.
    unfold violation_stage_test.
    apply qltb_true_iff. apply Rlt_Qlt.
    repeat rewrite Q2R_plus.
    rewrite Q2R_mult, qdyadic_real, qabs_exact_real.
    fold Qn Qs W. nra.
  Qed.

  Definition effective_coordinate_decode
      (a : EffectiveCoordinateSequence B) : CoordinatePoint := ecs_values B a.

  Definition concrete_violation_semidecider :
    FiniteViolationSemidecider B effective_coordinate_decode.
  Proof.
    refine {| violation_stage := violation_stage_test |}.
    - apply violation_stage_test_sound.
    - apply violation_stage_test_eventually.
  Defined.

  Theorem ambient_coordinate_ball_complement_is_semidecidable : forall a,
    (~ CoordinateAdmissible B (ecs_values B a) ->
       exists terms s, violation_stage_test a terms s = true)
    /\ (forall terms s,
       violation_stage_test a terms s = true ->
       ~ CoordinateAdmissible B (ecs_values B a)).
  Proof.
    intro a. split.
    - intro Hnot.
      destruct (nonadmissible_has_finite_violation B _ Hnot) as [terms Hviol].
      destruct (violation_stage_test_eventually a terms Hviol) as [s Hs].
      exists terms, s. exact Hs.
    - intros terms s Hs.
      apply violation_excludes_admissibility with (terms := terms).
      now apply violation_stage_test_sound in Hs.
  Qed.
End Test.

End UELAT_V3_CoordinateViolationSemidecision3.
