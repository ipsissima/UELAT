(** EffectiveNormingCandidatesStrong.v -- strong Step 1 of authoritative Theorem 3.2.

    Conditional only on the genuine Type-2 epsilon-Hahn--Banach realizer,
    every candidate is a RealizedBoundedFunctional: semantic action, norm bound
    and rational Type-2 name transformer travel together. The resulting family
    is proved 1-norming.
*)

From Coq Require Import Reals QArith Qreals Bool Lra Nra Ring Field.
From UELAT.V3 Require Import
  CertificateEnrichment RepresentedSpace ComputableBanach BanachNormLemmas
  DyadicVanishing GenericSlackCertification
  RealizedBoundedFunctional ApproximateHahnBanachStrongInterface
  NormalizedApproxHBStrong.

Module UELAT_V3_EffectiveNormingCandidatesStrong.
Import UELAT_V3_CertificateEnrichment.
Import UELAT_V3_RepresentedSpace.
Import UELAT_V3_ComputableBanach.
Import UELAT_V3_BanachNormLemmas.
Import UELAT_V3_DyadicVanishing.
Import UELAT_V3_GenericSlackCertification.
Import UELAT_V3_RealizedBoundedFunctional.
Import UELAT_V3_ApproximateHahnBanachStrongInterface.
Import UELAT_V3_NormalizedApproxHBStrong.

Section Candidates.
  Variable B : RealComputableBanachPresentation.
  Let X := carrier (cb_metric B).
  Variable A : EffectiveApproxHahnBanachStrong B.

  Lemma qdyadic_positive_strong : forall n, (0 < qdyadic n)%Q.
  Proof.
    intro n. apply Rlt_Qlt. rewrite qdyadic_real.
    change (Q2R (0 : Q)) with 0%R. apply dyadic_pos.
  Qed.

  Definition core_nonzero_test_strong
      (p : core_code B) (n : nat) : bool :=
    qltb (qdyadic n) (core_norm_approx B p n).

  Theorem core_nonzero_test_strong_sound : forall p n,
    core_nonzero_test_strong p n = true -> 0 < cb_norm B (core_decode p).
  Proof.
    intros p n Htest.
    unfold core_nonzero_test_strong in Htest.
    apply qltb_true_iff in Htest.
    pose proof (Qlt_Rlt _ _ Htest) as Hlt.
    rewrite qdyadic_real in Hlt.
    pose proof (core_norm_approx_sound B p n) as Happ.
    change
      (Rabs (Q2R (core_norm_approx B p n)
             - cb_norm B (core_decode p)) <= dyadic n) in Happ.
    pose proof
      (Rle_abs (Q2R (core_norm_approx B p n)
                - cb_norm B (core_decode p))) as Hdiff.
    nra.
  Qed.

  Theorem core_nonzero_test_strong_eventually : forall p,
    0 < cb_norm B (core_decode p) ->
    exists n, core_nonzero_test_strong p n = true.
  Proof.
    intros p Hnorm.
    destruct (dyadic_eventually_below (cb_norm B (core_decode p) / 3)
                ltac:(lra)) as [n Hsmall].
    pose proof (core_norm_approx_sound B p n) as Happ.
    change
      (Rabs (Q2R (core_norm_approx B p n)
             - cb_norm B (core_decode p)) <= dyadic n) in Happ.
    assert (Hlower :
      cb_norm B (core_decode p) - Q2R (core_norm_approx B p n)
        <= dyadic n).
    { replace
        (cb_norm B (core_decode p) - Q2R (core_norm_approx B p n))
        with
        (-(Q2R (core_norm_approx B p n)
           - cb_norm B (core_decode p))) by ring.
      rewrite <- Rabs_Ropp.
      eapply Rle_trans; [apply Rle_abs|exact Happ]. }
    exists n.
    unfold core_nonzero_test_strong.
    apply qltb_true_iff. apply Rlt_Qlt.
    rewrite qdyadic_real. nra.
  Qed.

  Definition zero_realized_functional : RealizedBoundedFunctional B.
  Proof.
    refine {| rbf_apply := fun _ => 0;
              rbf_norm_bound := 0;
              rbf_realize := fun _ _ => 0%Q |}.
    - intros. ring.
    - intros. ring.
    - lra.
    - intro x. rewrite Rabs_R0. nra.
    - intros x n. change (Rabs (0-0) <= dyadic n).
      rewrite Rabs_R0. apply dyadic_nonnegative.
  Defined.

  Definition strong_core_candidate
      (p : core_code B) (cert_stage eta_stage : nat) :
      RealizedBoundedFunctional B :=
    match Bool.eq_dec (core_nonzero_test_strong p cert_stage) true with
    | left Hcert =>
        normalized_realized_hb B A (core_decode p) (qdyadic eta_stage)
          (core_nonzero_test_strong_sound p cert_stage Hcert)
          (qdyadic_positive_strong eta_stage)
    | right _ => zero_realized_functional
    end.

  Definition strong_indexed_candidate (i cert_stage eta_stage : nat) :
      RealizedBoundedFunctional B :=
    strong_core_candidate (core_enum B i) cert_stage eta_stage.

  Theorem strong_core_candidate_contracting : forall p n k x,
    Rabs (rbf_apply (strong_core_candidate p n k) x) <= cb_norm B x.
  Proof.
    intros p n k x.
    unfold strong_core_candidate.
    destruct (Bool.eq_dec (core_nonzero_test_strong p n) true) as [Hcert|Hnot].
    - apply normalized_strong_contracting.
    - simpl. rewrite Rabs_R0. apply cb_norm_nonnegative.
  Qed.

  Theorem strong_indexed_candidate_contracting : forall i n k x,
    Rabs (rbf_apply (strong_indexed_candidate i n k) x) <= cb_norm B x.
  Proof. intros. apply strong_core_candidate_contracting. Qed.

  Theorem strong_core_candidate_hits : forall p n k,
    core_nonzero_test_strong p n = true ->
    rbf_apply (strong_core_candidate p n k) (core_decode p)
      = cb_norm B (core_decode p) / (1 + Q2R (qdyadic k)).
  Proof.
    intros p n k Hcert.
    unfold strong_core_candidate.
    destruct (Bool.eq_dec (core_nonzero_test_strong p n) true) as [Hyes|Hno].
    - apply normalized_strong_hits_fractional_norm.
    - contradiction.
  Qed.

  Lemma strong_functional_on_subtraction :
    forall (g : RealizedBoundedFunctional B) x y,
      rbf_apply g (cb_sub B x y) = rbf_apply g x - rbf_apply g y.
  Proof.
    intros g x y.
    unfold cb_sub, cb_neg.
    rewrite rbf_add, rbf_scale. ring.
  Qed.

  Theorem strong_core_candidate_transfer_lower : forall p n k x,
    core_nonzero_test_strong p n = true ->
    cb_norm B (core_decode p) / (1 + Q2R (qdyadic k))
      - distance x (core_decode p)
      <= rbf_apply (strong_core_candidate p n k) x.
  Proof.
    intros p n k x Hcert.
    set (g := strong_core_candidate p n k).
    pose proof (strong_core_candidate_contracting p n k
      (cb_sub B x (core_decode p))) as Hcontract.
    rewrite cb_norm_sub_is_distance in Hcontract.
    pose proof (Rle_abs (-(rbf_apply g (cb_sub B x (core_decode p))))) as Hminus.
    rewrite Rabs_Ropp in Hminus.
    assert (Hlower :
      - distance x (core_decode p)
        <= rbf_apply g (cb_sub B x (core_decode p))) by lra.
    rewrite strong_functional_on_subtraction in Hlower.
    unfold g in Hlower |- *.
    rewrite strong_core_candidate_hits by exact Hcert.
    lra.
  Qed.

  Theorem strong_normalization_loss_eventually_small : forall p gamma,
    0 < gamma ->
    exists k,
      cb_norm B (core_decode p)
        - cb_norm B (core_decode p) / (1 + Q2R (qdyadic k)) < gamma.
  Proof.
    intros p gamma Hgamma.
    set (N := cb_norm B (core_decode p)).
    pose proof (cb_norm_nonnegative B (core_decode p)) as HN.
    assert (HN1 : 0 < N+1) by (unfold N; lra).
    destruct (dyadic_eventually_below (gamma/(N+1)) ltac:(lra)) as [k Hsmall].
    exists k. rewrite qdyadic_real.
    set (e := dyadic k).
    assert (He : 0 < e) by (unfold e; apply dyadic_pos).
    assert (Hmul : e*(N+1) < gamma).
    { pose proof (Rmult_lt_compat_r (N+1) e (gamma/(N+1))
                    HN1 Hsmall) as H.
      replace ((gamma/(N+1))*(N+1)) with gamma in H by (field; lra).
      exact H. }
    assert (Hratio : e/(1+e) <= e).
    { apply (Rmult_le_reg_r (1+e)); [lra|].
      replace ((e/(1+e))*(1+e)) with e by (field; lra). nra. }
    replace (N - N/(1+e)) with (N*(e/(1+e))) by (field; lra).
    eapply Rle_lt_trans.
    - apply Rmult_le_compat_l; [exact HN|exact Hratio].
    - nra.
  Qed.

  Theorem strong_candidates_are_one_norming : forall x eps,
    0 < eps ->
    exists i n k,
      cb_norm B x - eps
        < Rabs (rbf_apply (strong_indexed_candidate i n k) x).
  Proof.
    intros x eps Heps.
    pose proof (cb_norm_nonnegative B x) as Hxnonneg.
    destruct (Req_dec (cb_norm B x) 0) as [Hxzero|Hxnonzero].
    - exists 0%nat, 0%nat, 0%nat.
      pose proof (Rabs_pos (rbf_apply (strong_indexed_candidate 0 0 0) x)). lra.
    - assert (Hxpos : 0 < cb_norm B x) by lra.
      set (delta := Rmin (eps/4) (cb_norm B x/4)).
      assert (Hdelta : 0 < delta).
      { unfold delta. apply Rmin_pos; lra. }
      destruct (core_dense B x delta Hdelta) as [p Hclose].
      pose proof (cb_norm_reverse_triangle_left B x (core_decode p)) as Hrev.
      pose proof (Rmin_r (eps/4) (cb_norm B x/4)) as Hdeltanorm.
      pose proof (Rmin_l (eps/4) (cb_norm B x/4)) as Hdeltaeps.
      assert (Hpnorm : 0 < cb_norm B (core_decode p)).
      { unfold delta in Hclose. nra. }
      destruct (core_nonzero_test_strong_eventually p Hpnorm) as [n Hcert].
      destruct (strong_normalization_loss_eventually_small p (eps/4) ltac:(lra))
        as [k Hloss].
      destruct (core_enum_surjective B p) as [i Hi].
      exists i, n, k.
      unfold strong_indexed_candidate. rewrite Hi.
      pose proof (strong_core_candidate_transfer_lower p n k x Hcert) as Htransfer.
      pose proof (Rle_abs (rbf_apply (strong_core_candidate p n k) x)) as Habs.
      assert (Hclose_eps : distance x (core_decode p) < eps/4).
      { eapply Rlt_le_trans; [exact Hclose|exact Hdeltaeps]. }
      nra.
  Qed.

  Theorem strong_candidate_has_realizer : forall i n k x s,
    Rabs
      (Q2R (rbf_realize (strong_indexed_candidate i n k)
                (core_named_name x) s)
       - rbf_apply (strong_indexed_candidate i n k)
                (core_named_value x)) <= dyadic s.
  Proof. intros. apply rbf_realize_correct. Qed.
End Candidates.

End UELAT_V3_EffectiveNormingCandidatesStrong.
