(** RealizedBoundedFunctional.v -- strong computability interface for bounded
    real-valued functionals on a computable Banach presentation.

    A realized functional carries an executable rational approximation program
    on source fast names and a correctness theorem against the semantic value.
*)

From Coq Require Import Reals QArith Qreals Lra.
From UELAT.V3 Require Import
  CertificateEnrichment RepresentedSpace ComputableBanach.

Module UELAT_V3_RealizedBoundedFunctional.
Import UELAT_V3_CertificateEnrichment.
Import UELAT_V3_RepresentedSpace.
Import UELAT_V3_ComputableBanach.

Record RealizedBoundedFunctional
    (B : RealComputableBanachPresentation) := {
  rbf_apply : carrier (cb_metric B) -> R;
  rbf_add : forall x y,
    rbf_apply (cb_add B x y) = rbf_apply x + rbf_apply y;
  rbf_scale : forall a x,
    rbf_apply (cb_scale B a x) = a * rbf_apply x;

  rbf_norm_bound : R;
  rbf_norm_bound_nonnegative : 0 <= rbf_norm_bound;
  rbf_bounded : forall x,
    Rabs (rbf_apply x) <= rbf_norm_bound * cb_norm B x;

  rbf_realize : CoreFastName B -> nat -> Q;
  rbf_realize_correct : forall (x : CoreNamedPoint B) n,
    Rabs
      (Q2R (rbf_realize (core_named_name x) n)
       - rbf_apply (core_named_value x))
      <= dyadic n
}.

Arguments rbf_apply {B} _ _.
Arguments rbf_realize {B} _ _ _.

Definition realized_functional_extensional
    {B : RealComputableBanachPresentation}
    (g : RealizedBoundedFunctional B) : Prop :=
  forall (x y : CoreNamedPoint B),
    core_named_value x = core_named_value y ->
    forall n,
      Rabs
        (Q2R (rbf_realize g (core_named_name x) n)
         - Q2R (rbf_realize g (core_named_name y) n))
      <= 2 * dyadic n.

Theorem realized_functional_names_extensional :
  forall B (g : RealizedBoundedFunctional B),
    realized_functional_extensional g.
Proof.
  intros B g x y Hxy n.
  pose proof (rbf_realize_correct g x n) as Hx.
  pose proof (rbf_realize_correct g y n) as Hy.
  rewrite <- Hxy in Hy.
  replace
    (Q2R (rbf_realize g (core_named_name x) n)
     - Q2R (rbf_realize g (core_named_name y) n))
    with
    ((Q2R (rbf_realize g (core_named_name x) n)
      - rbf_apply g (core_named_value x))
     + (rbf_apply g (core_named_value x)
      - Q2R (rbf_realize g (core_named_name y) n))) by ring.
  eapply Rle_trans; [apply Rabs_triang|].
  replace
    (rbf_apply g (core_named_value x)
     - Q2R (rbf_realize g (core_named_name y) n))
    with
    (-(Q2R (rbf_realize g (core_named_name y) n)
       - rbf_apply g (core_named_value x))) by ring.
  rewrite Rabs_Ropp.
  lra.
Qed.

End UELAT_V3_RealizedBoundedFunctional.
