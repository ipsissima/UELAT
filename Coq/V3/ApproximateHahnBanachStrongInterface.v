(** ApproximateHahnBanachStrongInterface.v -- manuscript Lemma 3.1 with the
    computability requirement made literal.

    The output is not merely a semantic bounded linear functional. It carries
    a rational Type-2 realizer on fast source names. Any future claim that
    Lemma 3.1 is machine-checked must construct this record uniformly from the
    computable Banach presentation, nonzero computable vector and rational eta.

    No exact norm-preserving Hahn--Banach selector is postulated.
*)

From Coq Require Import Reals QArith Qreals.
From UELAT.V3 Require Import
  CertificateEnrichment ComputableBanach RealizedBoundedFunctional.

Module UELAT_V3_ApproximateHahnBanachStrongInterface.
Import UELAT_V3_CertificateEnrichment.
Import UELAT_V3_ComputableBanach.
Import UELAT_V3_RealizedBoundedFunctional.

Record EffectiveApproxHahnBanachStrong
    (B : RealComputableBanachPresentation) := {
  ahbs_extend :
    forall (v : carrier (cb_metric B)) (eta : Q),
      0 < cb_norm B v ->
      (0 < eta)%Q ->
      RealizedBoundedFunctional B;

  ahbs_hits_vector : forall v eta Hv Heta,
    rbf_apply (ahbs_extend v eta Hv Heta) v = cb_norm B v;

  ahbs_norm_bound : forall v eta Hv Heta,
    rbf_norm_bound (ahbs_extend v eta Hv Heta) <= 1 + Q2R eta
}.

Arguments ahbs_extend {B} _ _ _ _ _.

Theorem strong_ahb_is_genuinely_type2 :
  forall B (A : EffectiveApproxHahnBanachStrong B)
         v eta Hv Heta (x : CoreNamedPoint B) n,
    Rabs
      (Q2R (rbf_realize (ahbs_extend A v eta Hv Heta)
                (core_named_name x) n)
       - rbf_apply (ahbs_extend A v eta Hv Heta)
                (core_named_value x))
      <= dyadic n.
Proof.
  intros.
  apply rbf_realize_correct.
Qed.

End UELAT_V3_ApproximateHahnBanachStrongInterface.
