(** NormalizedApproxHBStrong.v -- normalization of the strong Type-2
    epsilon-Hahn--Banach output. *)

From Coq Require Import Reals QArith Qreals Lra Lra Ring Field.
From UELAT.V3 Require Import
  CertificateEnrichment RepresentedSpace ComputableBanach
  RealizedBoundedFunctional ApproximateHahnBanachStrongInterface.

Module UELAT_V3_NormalizedApproxHBStrong.
Import UELAT_V3_CertificateEnrichment.
Import UELAT_V3_RepresentedSpace.
Import UELAT_V3_ComputableBanach.
Import UELAT_V3_RealizedBoundedFunctional.
Import UELAT_V3_ApproximateHahnBanachStrongInterface.

Section Normalize.
  Variable B : RealComputableBanachPresentation.
  Variable A : EffectiveApproxHahnBanachStrong B.
  Variable v : carrier (cb_metric B).
  Variable eta : Q.
  Hypothesis Hv : 0 < cb_norm B v.
  Hypothesis Heta : (0 < eta)%Q.

  Let g := ahbs_extend A v eta Hv Heta.
  Definition denomQ : Q := 1 + eta.
  Definition denomR : R := 1 + Q2R eta.

  Lemma denomR_positive : 0 < denomR.
  Proof.
    unfold denomR.
    pose proof (Qlt_Rlt _ _ Heta).
    change (Q2R (0 : Q)) with 0%R in H.
    lra.
  Qed.

  Lemma denomQ_nonzero : ~ denomQ == 0.
  Proof.
    intro Hzero.
    apply Qeq_eqR in Hzero.
    unfold denomQ in Hzero.
    rewrite Q2R_plus in Hzero.
    change (Q2R (1 : Q)) with 1%R in Hzero.
    change (Q2R (0 : Q)) with 0%R in Hzero.
    pose proof denomR_positive.
    unfold denomR in H.
    lra.
  Qed.

  Definition normalized_realized_hb : RealizedBoundedFunctional B.
  Proof.
    refine {| rbf_apply := fun x => rbf_apply g x / denomR;
              rbf_norm_bound := 1;
              rbf_realize := fun nu n => rbf_realize g nu n / denomQ |}.
    - intros x y. rewrite rbf_add. ring.
    - intros a x. rewrite rbf_scale. ring.
    - lra.
    - intro x.
      rewrite Rabs_div.
      rewrite Rabs_pos_eq by lra.
      pose proof (rbf_bounded g x) as Hg.
      pose proof (ahbs_norm_bound A v eta Hv Heta) as Hgbound.
      pose proof (rbf_norm_bound_nonnegative g) as Hgnonneg.
      pose proof (cb_norm_nonnegative B x) as Hx.
      unfold denomR.
      apply (Rmult_le_reg_r (1 + Q2R eta)); [exact denomR_positive|].
      field_simplify; try lra.
      nra.
    - intros x n.
      rewrite Q2R_div by exact denomQ_nonzero.
      unfold denomQ.
      rewrite Q2R_plus.
      change (Q2R (1 : Q)) with 1%R.
      unfold denomR.
      replace
        (Q2R (rbf_realize g (core_named_name x) n) / (1 + Q2R eta)
         - rbf_apply g (core_named_value x) / (1 + Q2R eta))
        with
        ((Q2R (rbf_realize g (core_named_name x) n)
          - rbf_apply g (core_named_value x)) / (1 + Q2R eta)) by field.
      rewrite Rabs_div, Rabs_pos_eq by lra.
      pose proof (rbf_realize_correct g x n) as Hreal.
      pose proof denomR_positive as Hd.
      unfold denomR in Hd.
      apply (Rmult_le_reg_r (1 + Q2R eta)); [exact Hd|].
      replace
        ((Rabs
           (Q2R (rbf_realize g (core_named_name x) n)
            - rbf_apply g (core_named_value x)) /
          (1 + Q2R eta)) * (1 + Q2R eta))
        with
        (Rabs
          (Q2R (rbf_realize g (core_named_name x) n)
           - rbf_apply g (core_named_value x))) by (field; lra).
      pose proof (Qlt_Rlt _ _ Heta) as HetaR.
      change (Q2R (0 : Q)) with 0%R in HetaR.
      nra.
  Defined.

  Theorem normalized_strong_contracting : forall x,
    Rabs (rbf_apply normalized_realized_hb x) <= cb_norm B x.
  Proof.
    intro x.
    pose proof (rbf_bounded normalized_realized_hb x).
    simpl in H. nra.
  Qed.

  Theorem normalized_strong_hits_fractional_norm :
    rbf_apply normalized_realized_hb v = cb_norm B v / denomR.
  Proof.
    unfold normalized_realized_hb. simpl.
    rewrite ahbs_hits_vector. reflexivity.
  Qed.

  Theorem normalized_strong_has_realizer : forall x n,
    Rabs
      (Q2R (rbf_realize normalized_realized_hb (core_named_name x) n)
       - rbf_apply normalized_realized_hb (core_named_value x))
      <= dyadic n.
  Proof.
    intros. apply rbf_realize_correct.
  Qed.
End Normalize.

End UELAT_V3_NormalizedApproxHBStrong.
