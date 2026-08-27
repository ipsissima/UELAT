(** EffectiveNormingFamilyStrong.v -- Type-2 norming candidates for Step 1 of
    authoritative Theorem 3.2. *)

From Coq Require Import Reals QArith Qreals Bool Lra Nra Ring.
From UELAT.V3 Require Import
  CertificateEnrichment RepresentedSpace ComputableBanach BanachNormLemmas
  GenericSlackCertification RealizedBoundedFunctional
  ApproximateHahnBanachStrongInterface NormalizedApproxHBStrong
  CoreNonzeroSearchStrong.

Module UELAT_V3_EffectiveNormingFamilyStrong.
Import UELAT_V3_CertificateEnrichment.
Import UELAT_V3_RepresentedSpace.
Import UELAT_V3_ComputableBanach.
Import UELAT_V3_BanachNormLemmas.
Import UELAT_V3_GenericSlackCertification.
Import UELAT_V3_RealizedBoundedFunctional.
Import UELAT_V3_ApproximateHahnBanachStrongInterface.
Import UELAT_V3_NormalizedApproxHBStrong.
Import UELAT_V3_CoreNonzeroSearchStrong.

Section Candidates.
  Variable B : RealComputableBanachPresentation.
  Variable A : EffectiveApproxHahnBanachStrong B.

  Definition zero_realized_functional : RealizedBoundedFunctional B.
  Proof.
    refine {| rbf_apply := fun _ => 0;
              rbf_norm_bound := 0;
              rbf_realize := fun _ _ => 0%Q |}.
    - intros. ring.
    - intros. ring.
    - lra.
    - intro x. rewrite Rabs_R0. nra.
    - intros x n. change (Rabs (0 - 0) <= dyadic n).
      rewrite Rabs_R0. apply dyadic_nonnegative.
  Defined.

  Definition strong_core_candidate
      (p : core_code B) (cert_stage eta_stage : nat) :
      RealizedBoundedFunctional B :=
    match Bool.eq_dec (core_nonzero_test_strong B p cert_stage) true with
    | left Hcert =>
        normalized_realized_hb B A (core_decode p) (qdyadic eta_stage)
          (core_nonzero_test_strong_sound B p cert_stage Hcert)
          (qdyadic_positive_strong B eta_stage)
    | right _ => zero_realized_functional
    end.

  Definition strong_indexed_candidate (i cert_stage eta_stage : nat) :
      RealizedBoundedFunctional B :=
    strong_core_candidate (core_enum B i) cert_stage eta_stage.

  Theorem strong_core_candidate_contracting : forall p n k x,
    Rabs (rbf_apply (strong_core_candidate p n k) x) <= cb_norm B x.
  Proof.
    intros p n k x. unfold strong_core_candidate.
    destruct (Bool.eq_dec (core_nonzero_test_strong B p n) true)
      as [Hcert|Hnot].
    - apply normalized_strong_contracting.
    - simpl. rewrite Rabs_R0. apply cb_norm_nonnegative.
  Qed.

  Theorem strong_indexed_candidate_contracting : forall i n k x,
    Rabs (rbf_apply (strong_indexed_candidate i n k) x) <= cb_norm B x.
  Proof. intros. apply strong_core_candidate_contracting. Qed.

  Theorem strong_core_candidate_hits : forall p n k,
    core_nonzero_test_strong B p n = true ->
    rbf_apply (strong_core_candidate p n k) (core_decode p)
      = cb_norm B (core_decode p) / (1 + Q2R (qdyadic k)).
  Proof.
    intros p n k Hcert. unfold strong_core_candidate.
    destruct (Bool.eq_dec (core_nonzero_test_strong B p n) true)
      as [Hyes|Hno].
    - apply normalized_strong_hits_fractional_norm.
    - contradiction.
  Qed.

  Lemma strong_functional_on_subtraction :
    forall (g : RealizedBoundedFunctional B) x y,
      rbf_apply g (cb_sub B x y) = rbf_apply g x - rbf_apply g y.
  Proof.
    intros g x y. unfold cb_sub, cb_neg.
    rewrite rbf_add, rbf_scale. ring.
  Qed.

  Theorem strong_candidate_has_realizer : forall i n k x s,
    Rabs
      (Q2R (rbf_realize (strong_indexed_candidate i n k)
                (core_named_name x) s)
       - rbf_apply (strong_indexed_candidate i n k)
                (core_named_value x))
      <= dyadic s.
  Proof. intros. apply rbf_realize_correct. Qed.
End Candidates.

End UELAT_V3_EffectiveNormingFamilyStrong.
