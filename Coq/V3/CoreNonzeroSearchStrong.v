(** CoreNonzeroSearchStrong.v -- effective discovery of nonzero rational-core
    vectors for Step 1 of Theorem 3.2. *)

From Coq Require Import Reals QArith Qreals Lra Nra Ring.
From UELAT.V3 Require Import
  CertificateEnrichment RepresentedSpace ComputableBanach
  DyadicVanishing GenericSlackCertification.

Module UELAT_V3_CoreNonzeroSearchStrong.
Import UELAT_V3_CertificateEnrichment.
Import UELAT_V3_RepresentedSpace.
Import UELAT_V3_ComputableBanach.
Import UELAT_V3_DyadicVanishing.
Import UELAT_V3_GenericSlackCertification.

Section Search.
  Variable B : RealComputableBanachPresentation.

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
    apply qltb_true_iff. apply Rlt_Qlt. rewrite qdyadic_real. nra.
  Qed.
End Search.

End UELAT_V3_CoreNonzeroSearchStrong.
