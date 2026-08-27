(** RationalSobolevCompleteness.v -- completion of the semantic existence part
    of manuscript Proposition 5.3.

    Given a true strict metric bound, dyadic tails eventually fit inside the
    slack.  Exact rational finite-stage squared distances then give the
    PositiveApprox / PositiveDistance witnesses of RationalSobolevPresentation.
    Combined with StrictSlackSearch.v, this supplies an axiom-free terminating
    search whenever the corresponding acceptance predicate is reflected to an
    executable boolean checker.
*)

From Coq Require Import Reals QArith Qreals Lra Lra.
From UELAT.V3 Require Import
  CertificateEnrichment RepresentedSpace DyadicVanishing
  RationalSobolev RationalSobolevPresentation.

Module UELAT_V3_RationalSobolevCompleteness.
Import UELAT_V3_CertificateEnrichment.
Import UELAT_V3_RepresentedSpace.
Import UELAT_V3_DyadicVanishing.
Import UELAT_V3_RationalSobolev.
Import UELAT_V3_RationalSobolevPresentation.

Section ApproximationCompleteness.

  Variable P : RationalW12Presentation.

  Theorem strict_approximation_has_finite_witness :
    forall (nu : w12_name P) (p : RationalPiecewiseCode) (q : R),
      distance (w12_name_value nu) (w12_decode p) < q ->
      exists w : ApproxWitness P, approx_accept P nu p q w.
  Proof.
    intros nu p q Htrue.
    set (dtrue := distance (w12_name_value nu) (w12_decode p)).
    assert (Hgap : 0 < q - dtrue) by (unfold dtrue; lra).
    destruct (two_dyadic_eventually_below (q - dtrue) Hgap) as [n Hsmall].
    set (sigma := w12_sqdist (w12_stage nu n) p).
    exists (PositiveApprox n sigma).
    simpl.
    repeat split.
    - unfold dtrue in Hsmall. lra.
    - reflexivity.
    - rewrite (w12_sqdist_sound (P:=P) (w12_stage nu n) p).
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
          unfold dtrue.
          lra. }
      assert (Hstrict :
        distance (w12_decode (w12_stage nu n)) (w12_decode p)
          < q - dyadic n).
      { unfold dtrue in *. lra. }
      assert (Hrhs : 0 < q - dyadic n) by (unfold dtrue in *; lra).
      nra.
  Qed.

End ApproximationCompleteness.

Section DistanceCompleteness.

  Variable P : RationalW12Presentation.

  Theorem strict_distance_has_finite_witness :
    forall (nu mu : w12_name P) (q : R),
      distance (w12_name_value nu) (w12_name_value mu) < q ->
      exists w : DistanceWitness P, distance_accept P nu mu q w.
  Proof.
    intros nu mu q Htrue.
    set (dtrue := distance (w12_name_value nu) (w12_name_value mu)).
    assert (Hgap : 0 < q - dtrue) by (unfold dtrue; lra).
    destruct (four_dyadic_eventually_below (q - dtrue) Hgap) as [n Hsmall].
    set (sigma := w12_sqdist (w12_stage nu n) (w12_stage mu n)).
    exists (PositiveDistance n sigma).
    simpl.
    repeat split.
    - unfold dtrue in Hsmall. lra.
    - reflexivity.
    - rewrite (w12_sqdist_sound (P:=P)
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
            unfold dtrue.
            lra. }
      assert (Hstrict :
        distance (w12_decode (w12_stage nu n))
                 (w12_decode (w12_stage mu n))
          < q - 2 * dyadic n).
      { unfold dtrue in *. lra. }
      assert (Hrhs : 0 < q - 2 * dyadic n) by (unfold dtrue in *; lra).
      nra.
  Qed.

End DistanceCompleteness.

Theorem rational_w12_strict_slack_complete :
  forall (P : RationalW12Presentation),
    (forall nu p q,
      distance (w12_name_value nu) (w12_decode p) < q ->
      exists w, approx_accept P nu p q w)
    /\
    (forall nu mu q,
      distance (w12_name_value nu) (w12_name_value mu) < q ->
      exists w, distance_accept P nu mu q w).
Proof.
  intro P. split.
  - apply strict_approximation_has_finite_witness.
  - apply strict_distance_has_finite_witness.
Qed.

End UELAT_V3_RationalSobolevCompleteness.
