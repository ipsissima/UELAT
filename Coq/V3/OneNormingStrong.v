(** OneNormingStrong.v -- finish Step 1 of authoritative Theorem 3.2 under
    the strong effective epsilon-Hahn--Banach contract. *)

From Coq Require Import Reals QArith Qreals Lra Lra Ring Field.
From UELAT.V3 Require Import
  CertificateEnrichment RepresentedSpace ComputableBanach BanachNormLemmas
  DyadicVanishing GenericSlackCertification CoreNonzeroSearchStrong
  RealizedBoundedFunctional EffectiveNormingFamilyStrong.

Module UELAT_V3_OneNormingStrong.
Import UELAT_V3_CertificateEnrichment.
Import UELAT_V3_RepresentedSpace.
Import UELAT_V3_ComputableBanach.
Import UELAT_V3_BanachNormLemmas.
Import UELAT_V3_DyadicVanishing.
Import UELAT_V3_GenericSlackCertification.
Import UELAT_V3_CoreNonzeroSearchStrong.
Import UELAT_V3_RealizedBoundedFunctional.
Import UELAT_V3_EffectiveNormingFamilyStrong.

Section Norming.
  Variable B : RealComputableBanachPresentation.
  Variable A : EffectiveApproxHahnBanachStrong B.

  Theorem strong_core_candidate_transfer_lower : forall p n k x,
    core_nonzero_test_strong B p n = true ->
    cb_norm B (core_decode p) / (1 + Q2R (qdyadic k))
      - distance x (core_decode p)
      <= rbf_apply (strong_core_candidate B A p n k) x.
  Proof.
    intros p n k x Hcert.
    set (g := strong_core_candidate B A p n k).
    pose proof (strong_core_candidate_contracting B A p n k
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
    assert (HN1 : 0 < N + 1) by (unfold N; lra).
    destruct (dyadic_eventually_below (gamma / (N + 1)) ltac:(lra))
      as [k Hsmall].
    exists k.
    rewrite qdyadic_real.
    set (e := dyadic k).
    assert (He : 0 < e) by (unfold e; apply dyadic_pos).
    assert (Hmul : e * (N + 1) < gamma).
    { pose proof (Rmult_lt_compat_r (N + 1) e (gamma / (N + 1))
                    HN1 Hsmall) as H.
      replace ((gamma / (N + 1)) * (N + 1)) with gamma in H by (field; lra).
      exact H. }
    assert (Hratio : e / (1 + e) <= e).
    { apply (Rmult_le_reg_r (1 + e)); [lra|].
      replace ((e / (1 + e)) * (1 + e)) with e by (field; lra).
      nra. }
    replace (N - N / (1 + e)) with (N * (e / (1 + e))) by (field; lra).
    eapply Rle_lt_trans.
    - apply Rmult_le_compat_l; [exact HN|exact Hratio].
    - nra.
  Qed.

  Theorem strong_candidates_are_one_norming : forall x eps,
    0 < eps ->
    exists i n k,
      cb_norm B x - eps
        < Rabs (rbf_apply (strong_indexed_candidate B A i n k) x).
  Proof.
    intros x eps Heps.
    pose proof (cb_norm_nonnegative B x) as Hxnonneg.
    destruct (Req_dec (cb_norm B x) 0) as [Hxzero|Hxnonzero].
    - exists 0%nat, 0%nat, 0%nat.
      pose proof (Rabs_pos (rbf_apply (strong_indexed_candidate B A 0 0 0) x)).
      lra.
    - assert (Hxpos : 0 < cb_norm B x) by lra.
      set (delta := Rmin (eps / 4) (cb_norm B x / 4)).
      assert (Hdelta : 0 < delta).
      { unfold delta. apply Rmin_pos; lra. }
      destruct (core_dense B x delta Hdelta) as [p Hclose].
      pose proof (cb_norm_reverse_triangle_left B x (core_decode p)) as Hrev.
      pose proof (Rmin_r (eps / 4) (cb_norm B x / 4)) as Hdeltanorm.
      pose proof (Rmin_l (eps / 4) (cb_norm B x / 4)) as Hdeltaeps.
      assert (Hpnorm : 0 < cb_norm B (core_decode p)).
      { unfold delta in Hclose. nra. }
      destruct (core_nonzero_test_strong_eventually B p Hpnorm) as [n Hcert].
      destruct (strong_normalization_loss_eventually_small p (eps / 4) ltac:(lra))
        as [k Hloss].
      destruct (core_enum_surjective B p) as [i Hi].
      exists i, n, k.
      unfold strong_indexed_candidate.
      rewrite Hi.
      pose proof (strong_core_candidate_transfer_lower p n k x Hcert) as Htransfer.
      pose proof (Rle_abs (rbf_apply (strong_core_candidate B A p n k) x)) as Habs.
      assert (Hclose_eps : distance x (core_decode p) < eps / 4).
      { eapply Rlt_le_trans; [exact Hclose|exact Hdeltaeps]. }
      nra.
  Qed.

  Theorem strong_candidates_norming_upper : forall i n k x,
    Rabs (rbf_apply (strong_indexed_candidate B A i n k) x) <= cb_norm B x.
  Proof. intros. apply strong_indexed_candidate_contracting. Qed.
End Norming.

End UELAT_V3_OneNormingStrong.
