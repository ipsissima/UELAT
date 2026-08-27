(** GenericSlackCertification.v -- manuscript Proposition 2.5. *)

From Coq Require Import Reals QArith Qreals Lra Lra.
From UELAT.V3 Require Import
  CertificateEnrichment RepresentedSpace DyadicVanishing StrictSlackSearch.

Module UELAT_V3_GenericSlackCertification.
Import UELAT_V3_CertificateEnrichment.
Import UELAT_V3_RepresentedSpace.
Import UELAT_V3_DyadicVanishing.
Import UELAT_V3_StrictSlackSearch.

Fixpoint qdyadic (n : nat) : Q :=
  match n with | O => 1 | S k => qdyadic k / 2 end.

Lemma Q_two_nonzero : ~ (2 : Q) == 0.
Proof. vm_compute. discriminate. Qed.

Lemma qdyadic_real : forall n, Q2R (qdyadic n) = dyadic n.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - simpl qdyadic. simpl dyadic.
    rewrite Q2R_div by apply Q_two_nonzero.
    rewrite IH. change (Q2R (2 : Q)) with 2%R. field.
Qed.

Definition qltb (a b : Q) : bool :=
  if Qlt_le_dec a b then true else false.

Lemma qltb_true_iff : forall a b, qltb a b = true <-> (a < b)%Q.
Proof.
  intros a b. unfold qltb. destruct (Qlt_le_dec a b) as [Hlt|Hle].
  - split; intros; assumption.
  - split; intro H.
    + discriminate.
    + exfalso. now apply (Qlt_not_le _ _ H).
Qed.

Record EffectiveMetricSlackInterface (X : MetricPresentation) := {
  ems_stage : name X -> nat -> carrier X;
  ems_stage_tail : forall nu n,
    distance (decode_name nu) (ems_stage nu n) <= dyadic n;
  ems_upper : carrier X -> carrier X -> nat -> Q;
  ems_upper_sound : forall x y k,
    distance x y <= Q2R (ems_upper x y k);
  ems_upper_precision : forall x y k,
    Q2R (ems_upper x y k) <= distance x y + dyadic k
}.

Arguments ems_stage {X} _ _ _.
Arguments ems_upper {X} _ _ _ _.

Section DistanceCertification.
  Context {X : MetricPresentation}.
  Variable E : EffectiveMetricSlackInterface X.

  Definition distance_stage_test
      (nu mu : name X) (q : Q) (n : nat) : bool :=
    qltb
      (ems_upper E (ems_stage E nu n) (ems_stage E mu n) n
       + 2 * qdyadic n) q.

  Lemma distance_stage_test_sound : forall nu mu q n,
    distance_stage_test nu mu q n = true ->
    distance (decode_name nu) (decode_name mu) < Q2R q.
  Proof.
    intros nu mu q n Htest.
    apply qltb_true_iff in Htest.
    pose proof (Qlt_Rlt _ _ Htest) as Hq.
    repeat rewrite Q2R_plus in Hq.
    rewrite Q2R_mult, qdyadic_real in Hq.
    change (Q2R (2 : Q)) with 2%R in Hq.
    pose proof (ems_stage_tail E nu n) as Hnu.
    pose proof (ems_stage_tail E mu n) as Hmu.
    pose proof (ems_upper_sound E (ems_stage E nu n) (ems_stage E mu n) n) as Hupper.
    rewrite distance_symmetric with (x := decode_name mu) (y := ems_stage E mu n) in Hmu.
    eapply Rle_lt_trans.
    - apply distance_triangle with (y := ems_stage E nu n).
    - eapply Rle_lt_trans.
      + apply Rplus_le_compat_l.
        apply distance_triangle with (y := ems_stage E mu n).
      + lra.
  Qed.

  Theorem distance_stage_eventually_accepts : forall nu mu q,
    distance (decode_name nu) (decode_name mu) < Q2R q ->
    exists n, distance_stage_test nu mu q n = true.
  Proof.
    intros nu mu q Htrue.
    set (dtrue := distance (decode_name nu) (decode_name mu)).
    assert (Hgap : 0 < Q2R q - dtrue) by (unfold dtrue; lra).
    destruct (dyadic_eventually_below ((Q2R q - dtrue) / 8) ltac:(lra)) as [n Hsmall].
    assert (Hfinite :
      distance (ems_stage E nu n) (ems_stage E mu n)
        <= dtrue + 2 * dyadic n).
    { pose proof (ems_stage_tail E nu n) as Hnu.
      pose proof (ems_stage_tail E mu n) as Hmu.
      eapply Rle_trans.
      - apply distance_triangle with (y := decode_name nu).
      - eapply Rle_trans.
        + apply Rplus_le_compat_l.
          apply distance_triangle with (y := decode_name mu).
        + rewrite distance_symmetric with (x := ems_stage E nu n) (y := decode_name nu).
          unfold dtrue. lra. }
    pose proof (ems_upper_precision E (ems_stage E nu n) (ems_stage E mu n) n) as Hprec.
    assert (Hreal :
      Q2R (ems_upper E (ems_stage E nu n) (ems_stage E mu n) n
            + 2 * qdyadic n) < Q2R q).
    { rewrite Q2R_plus, Q2R_mult, qdyadic_real.
      change (Q2R (2 : Q)) with 2%R. unfold dtrue in *. lra. }
    exists n. apply qltb_true_iff. now apply Rlt_Qlt.
  Qed.

  Definition distance_slack_search
      (nu mu : name X) (q : Q)
      (H : distance (decode_name nu) (decode_name mu) < Q2R q) :
      SemidecidableSlackSearch :=
    {| slack_test := distance_stage_test nu mu q;
       slack_eventually := distance_stage_eventually_accepts nu mu q H |}.

  Definition distance_slack_stage
      (nu mu : name X) (q : Q)
      (H : distance (decode_name nu) (decode_name mu) < Q2R q) : nat :=
    run_semidecidable_slack_search (distance_slack_search nu mu q H).

  Theorem distance_slack_stage_valid : forall nu mu q H,
    distance_stage_test nu mu q (distance_slack_stage nu mu q H) = true.
  Proof. intros. unfold distance_slack_stage. apply semidecidable_slack_search_valid. Qed.
End DistanceCertification.

Section ApproximationCertification.
  Context {X : MetricPresentation}.
  Variable E : EffectiveMetricSlackInterface X.
  Variable Code : Type.
  Variable decode : Code -> carrier X.

  Definition approximation_stage_test
      (nu : name X) (p : Code) (q : Q) (n : nat) : bool :=
    qltb (ems_upper E (ems_stage E nu n) (decode p) n + qdyadic n) q.

  Lemma approximation_stage_test_sound : forall nu p q n,
    approximation_stage_test nu p q n = true ->
    distance (decode_name nu) (decode p) < Q2R q.
  Proof.
    intros nu p q n Htest.
    apply qltb_true_iff in Htest.
    pose proof (Qlt_Rlt _ _ Htest) as Hq.
    rewrite Q2R_plus, qdyadic_real in Hq.
    pose proof (ems_stage_tail E nu n) as Htail.
    pose proof (ems_upper_sound E (ems_stage E nu n) (decode p) n) as Hupper.
    eapply Rle_lt_trans.
    - apply distance_triangle with (y := ems_stage E nu n).
    - lra.
  Qed.

  Theorem approximation_stage_eventually_accepts : forall nu p q,
    distance (decode_name nu) (decode p) < Q2R q ->
    exists n, approximation_stage_test nu p q n = true.
  Proof.
    intros nu p q Htrue.
    set (dtrue := distance (decode_name nu) (decode p)).
    assert (Hgap : 0 < Q2R q - dtrue) by (unfold dtrue; lra).
    destruct (dyadic_eventually_below ((Q2R q - dtrue) / 4) ltac:(lra)) as [n Hsmall].
    assert (Hfinite : distance (ems_stage E nu n) (decode p) <= dtrue + dyadic n).
    { pose proof (ems_stage_tail E nu n) as Htail.
      eapply Rle_trans.
      - apply distance_triangle with (y := decode_name nu).
      - rewrite distance_symmetric with (x := ems_stage E nu n) (y := decode_name nu).
        unfold dtrue. lra. }
    pose proof (ems_upper_precision E (ems_stage E nu n) (decode p) n) as Hprec.
    assert (Hreal :
      Q2R (ems_upper E (ems_stage E nu n) (decode p) n + qdyadic n) < Q2R q).
    { rewrite Q2R_plus, qdyadic_real. unfold dtrue in *. lra. }
    exists n. apply qltb_true_iff. now apply Rlt_Qlt.
  Qed.

  Definition approximation_slack_search
      (nu : name X) (p : Code) (q : Q)
      (H : distance (decode_name nu) (decode p) < Q2R q) :
      SemidecidableSlackSearch :=
    {| slack_test := approximation_stage_test nu p q;
       slack_eventually := approximation_stage_eventually_accepts nu p q H |}.

  Definition approximation_slack_stage
      (nu : name X) (p : Code) (q : Q)
      (H : distance (decode_name nu) (decode p) < Q2R q) : nat :=
    run_semidecidable_slack_search (approximation_slack_search nu p q H).

  Theorem approximation_slack_stage_valid : forall nu p q H,
    approximation_stage_test nu p q (approximation_slack_stage nu p q H) = true.
  Proof. intros. unfold approximation_slack_stage. apply semidecidable_slack_search_valid. Qed.
End ApproximationCertification.

End UELAT_V3_GenericSlackCertification.
