(** RationalSobolevBooleanCheckers.v -- terminating finite checkers for
    manuscript Definition 5.1 / Proposition 5.3.

    Bounds and all stored arithmetic are rational. The checker recomputes the
    exact finite-stage squared W12 distance, checks the stored rational value,
    and checks the strict slack inequality using decidable Q arithmetic. Its
    soundness follows from the fast-Cauchy tails; strict semantic slack yields
    an accepted finite witness by dyadic vanishing.
*)

From Coq Require Import Reals QArith Qreals Bool Lra Lra.
From UELAT.V3 Require Import
  CertificateEnrichment RepresentedSpace
  GenericSlackCertification DyadicVanishing
  RationalSobolev RationalSobolevPresentation.

Module UELAT_V3_RationalSobolevBooleanCheckers.
Import UELAT_V3_CertificateEnrichment.
Import UELAT_V3_RepresentedSpace.
Import UELAT_V3_GenericSlackCertification.
Import UELAT_V3_DyadicVanishing.
Import UELAT_V3_RationalSobolev.
Import UELAT_V3_RationalSobolevPresentation.

Definition qeqb (a b : Q) : bool :=
  if Qeq_dec a b then true else false.

Lemma qeqb_true_iff : forall a b,
  qeqb a b = true <-> a == b.
Proof.
  intros a b. unfold qeqb.
  destruct (Qeq_dec a b) as [Heq|Hneq].
  - split; intro; assumption.
  - split; intro H.
    + discriminate.
    + contradiction.
Qed.

Record QApproxWitness := {
  qaw_stage : nat;
  qaw_sigma : Q
}.

Record QDistanceWitness := {
  qdw_stage : nat;
  qdw_sigma : Q
}.

Definition approx_check_Q
    (P : RationalW12Presentation)
    (nu : w12_name P) (p : RationalPiecewiseCode)
    (q : Q) (w : QApproxWitness) : bool :=
  let n := qaw_stage w in
  let sigma := qaw_sigma w in
  andb (qltb (qdyadic n) q)
    (andb
      (qeqb sigma (w12_sqdist (w12_stage nu n) p))
      (qltb sigma ((q - qdyadic n) * (q - qdyadic n)))).

Definition distance_check_Q
    (P : RationalW12Presentation)
    (nu mu : w12_name P) (q : Q)
    (w : QDistanceWitness) : bool :=
  let n := qdw_stage w in
  let sigma := qdw_sigma w in
  andb (qltb (2 * qdyadic n) q)
    (andb
      (qeqb sigma
        (w12_sqdist (w12_stage nu n) (w12_stage mu n)))
      (qltb sigma
        ((q - 2 * qdyadic n) * (q - 2 * qdyadic n)))).

Section Soundness.
  Variable P : RationalW12Presentation.

  Theorem approx_check_Q_sound : forall nu p q w,
    approx_check_Q P nu p q w = true ->
    distance (w12_name_value nu) (w12_decode p) < Q2R q.
  Proof.
    intros nu p q [n sigma] Hcheck.
    unfold approx_check_Q in Hcheck. simpl in Hcheck.
    apply andb_true_iff in Hcheck as [Htail Hrest].
    apply andb_true_iff in Hrest as [Hexact Hsq].
    apply qltb_true_iff in Htail.
    apply qeqb_true_iff in Hexact.
    apply qltb_true_iff in Hsq.
    pose proof (Qlt_Rlt _ _ Htail) as HtailR.
    pose proof (Qlt_Rlt _ _ Hsq) as HsqR.
    pose proof (Qeq_eqR _ _ Hexact) as HexactR.
    rewrite qdyadic_real in HtailR.
    rewrite Q2R_mult in HsqR.
    repeat rewrite Q2R_minus in HsqR.
    repeat rewrite qdyadic_real in HsqR.
    rewrite HexactR in HsqR.
    rewrite (w12_sqdist_sound (P:=P) (w12_stage nu n) p) in HsqR.
    pose proof (w12_stage_tail P nu n) as Hname.
    pose proof (distance_nonnegative (w12_metric P)
      (w12_decode (w12_stage nu n)) (w12_decode p)) as Hfin0.
    assert (Hfin :
      distance (w12_decode (w12_stage nu n)) (w12_decode p)
        < Q2R q - dyadic n) by nra.
    eapply Rle_lt_trans.
    - apply distance_triangle with (y := w12_decode (w12_stage nu n)).
    - lra.
  Qed.

  Theorem distance_check_Q_sound : forall nu mu q w,
    distance_check_Q P nu mu q w = true ->
    distance (w12_name_value nu) (w12_name_value mu) < Q2R q.
  Proof.
    intros nu mu q [n sigma] Hcheck.
    unfold distance_check_Q in Hcheck. simpl in Hcheck.
    apply andb_true_iff in Hcheck as [Htail Hrest].
    apply andb_true_iff in Hrest as [Hexact Hsq].
    apply qltb_true_iff in Htail.
    apply qeqb_true_iff in Hexact.
    apply qltb_true_iff in Hsq.
    pose proof (Qlt_Rlt _ _ Htail) as HtailR.
    pose proof (Qlt_Rlt _ _ Hsq) as HsqR.
    pose proof (Qeq_eqR _ _ Hexact) as HexactR.
    rewrite Q2R_mult, qdyadic_real in HtailR.
    change (Q2R (2 : Q)) with 2%R in HtailR.
    rewrite Q2R_mult in HsqR.
    repeat rewrite Q2R_minus in HsqR.
    repeat rewrite Q2R_mult in HsqR.
    repeat rewrite qdyadic_real in HsqR.
    change (Q2R (2 : Q)) with 2%R in HsqR.
    rewrite HexactR in HsqR.
    rewrite (w12_sqdist_sound (P:=P)
      (w12_stage nu n) (w12_stage mu n)) in HsqR.
    pose proof (w12_stage_tail P nu n) as Hnu.
    pose proof (w12_stage_tail P mu n) as Hmu.
    pose proof (distance_nonnegative (w12_metric P)
      (w12_decode (w12_stage nu n))
      (w12_decode (w12_stage mu n))) as Hfin0.
    assert (Hfin :
      distance (w12_decode (w12_stage nu n))
               (w12_decode (w12_stage mu n))
        < Q2R q - 2 * dyadic n) by nra.
    assert (Hwhole :
      distance (w12_name_value nu) (w12_name_value mu)
        <= 2 * dyadic n
           + distance (w12_decode (w12_stage nu n))
                      (w12_decode (w12_stage mu n))).
    { eapply Rle_trans.
      - apply distance_triangle with (y := w12_decode (w12_stage nu n)).
      - eapply Rle_trans.
        + apply Rplus_le_compat_l.
          apply distance_triangle with (y := w12_decode (w12_stage mu n)).
        + rewrite distance_symmetric with
            (x := w12_decode (w12_stage mu n))
            (y := w12_name_value mu).
          lra. }
    lra.
  Qed.

End Soundness.

Section Completeness.
  Variable P : RationalW12Presentation.

  Theorem approx_check_Q_complete_strict : forall nu p q,
    distance (w12_name_value nu) (w12_decode p) < Q2R q ->
    exists w, approx_check_Q P nu p q w = true.
  Proof.
    intros nu p q Htrue.
    set (dtrue := distance (w12_name_value nu) (w12_decode p)).
    assert (Hgap : 0 < Q2R q - dtrue) by (unfold dtrue; lra).
    destruct (two_dyadic_eventually_below (Q2R q - dtrue) Hgap) as [n Hsmall].
    set (sigma := w12_sqdist (w12_stage nu n) p).
    exists {| qaw_stage := n; qaw_sigma := sigma |}.
    unfold approx_check_Q. simpl.
    apply andb_true_iff. split.
    - apply qltb_true_iff. apply Rlt_Qlt.
      rewrite qdyadic_real. unfold dtrue in *. lra.
    - apply andb_true_iff. split.
      + apply qeqb_true_iff. reflexivity.
      + apply qltb_true_iff. apply Rlt_Qlt.
        rewrite Q2R_mult.
        repeat rewrite Q2R_minus.
        repeat rewrite qdyadic_real.
        rewrite (w12_sqdist_sound (P:=P) (w12_stage nu n) p).
        pose proof (w12_stage_tail P nu n) as Htail.
        pose proof (distance_nonnegative (w12_metric P)
          (w12_decode (w12_stage nu n)) (w12_decode p)) as Hfin0.
        assert (Hfin :
          distance (w12_decode (w12_stage nu n)) (w12_decode p)
            <= dyadic n + dtrue).
        { eapply Rle_trans.
          - apply distance_triangle with (y := w12_name_value nu).
          - rewrite distance_symmetric with
              (x := w12_decode (w12_stage nu n))
              (y := w12_name_value nu).
            unfold dtrue. lra. }
        unfold dtrue in *. nra.
  Qed.

  Theorem distance_check_Q_complete_strict : forall nu mu q,
    distance (w12_name_value nu) (w12_name_value mu) < Q2R q ->
    exists w, distance_check_Q P nu mu q w = true.
  Proof.
    intros nu mu q Htrue.
    set (dtrue := distance (w12_name_value nu) (w12_name_value mu)).
    assert (Hgap : 0 < Q2R q - dtrue) by (unfold dtrue; lra).
    destruct (four_dyadic_eventually_below (Q2R q - dtrue) Hgap) as [n Hsmall].
    set (sigma := w12_sqdist (w12_stage nu n) (w12_stage mu n)).
    exists {| qdw_stage := n; qdw_sigma := sigma |}.
    unfold distance_check_Q. simpl.
    apply andb_true_iff. split.
    - apply qltb_true_iff. apply Rlt_Qlt.
      rewrite Q2R_mult, qdyadic_real.
      change (Q2R (2 : Q)) with 2%R.
      unfold dtrue in *. lra.
    - apply andb_true_iff. split.
      + apply qeqb_true_iff. reflexivity.
      + apply qltb_true_iff. apply Rlt_Qlt.
        rewrite Q2R_mult.
        repeat rewrite Q2R_minus.
        repeat rewrite Q2R_mult.
        repeat rewrite qdyadic_real.
        change (Q2R (2 : Q)) with 2%R.
        rewrite (w12_sqdist_sound (P:=P)
          (w12_stage nu n) (w12_stage mu n)).
        pose proof (w12_stage_tail P nu n) as Hnu.
        pose proof (w12_stage_tail P mu n) as Hmu.
        pose proof (distance_nonnegative (w12_metric P)
          (w12_decode (w12_stage nu n))
          (w12_decode (w12_stage mu n))) as Hfin0.
        assert (Hfin :
          distance (w12_decode (w12_stage nu n))
                   (w12_decode (w12_stage mu n))
            <= 2 * dyadic n + dtrue).
        { eapply Rle_trans.
          - apply distance_triangle with (y := w12_name_value nu).
          - eapply Rle_trans.
            + apply Rplus_le_compat_l.
              apply distance_triangle with (y := w12_name_value mu).
            + rewrite distance_symmetric with
                (x := w12_decode (w12_stage nu n))
                (y := w12_name_value nu).
              unfold dtrue. lra. }
        unfold dtrue in *. nra.
  Qed.

End Completeness.

End UELAT_V3_RationalSobolevBooleanCheckers.
