(** LinearUniversalityPipeline.v -- auditable factorization of v3 Theorem 3.2.

    The manuscript proof of effective linear universality has several logically
    independent computable-analysis steps.  This file prevents any one of them
    from being hidden behind a monolithic theorem name: each step is an explicit
    record interface, and the final theorem composes only data that have actually
    been supplied.

    This is not yet a proof that every computable Banach presentation supplies
    the records below.  The hard remaining work is precisely to instantiate
    them from effective approximate Hahn--Banach and computable compactness.
*)

From Coq Require Import Reals List.
From UELAT.V3 Require Import ComputableBanach LinearUniversality.

Module UELAT_V3_LinearUniversalityPipeline.
Import UELAT_V3_ComputableBanach.

Section Pipeline.

  Variable B : RealComputableBanachPresentation.
  Let X := carrier (cb_metric B).

  Record EffectiveNormingFamily := {
    enf_coord : nat -> X -> R;
    enf_add : forall j x y,
      enf_coord j (cb_add B x y) = enf_coord j x + enf_coord j y;
    enf_scale : forall j a x,
      enf_coord j (cb_scale B a x) = a * enf_coord j x;
    enf_contracting : forall j x,
      Rabs (enf_coord j x) <= distance x (cb_zero B);
    enf_one_norming : forall x eta,
      0 < eta -> exists j,
        distance x (cb_zero B) - eta < Rabs (enf_coord j x)
  }.

  Record EffectiveDualBall := {
    KPoint : Type;
    KName : Type;
    Kdecode : KName -> KPoint;
    Kcompact_net : nat -> list KName;
    Kcompact_net_spec : Prop;
    evaluate : KPoint -> X -> R;
    evaluate_linear : forall k x y,
      evaluate k (cb_add B x y) = evaluate k x + evaluate k y;
    evaluate_scale : forall k a x,
      evaluate k (cb_scale B a x) = a * evaluate k x;
    evaluate_contracting : forall k x,
      Rabs (evaluate k x) <= distance x (cb_zero B);
    evaluate_norming : forall x eta,
      0 < eta -> exists k,
        distance x (cb_zero B) - eta < Rabs (evaluate k x)
  }.

  Record EffectiveCantorSurjection (K : EffectiveDualBall) := {
    CantorName : Type;
    cantor_decode : CantorName -> KPoint K;
    cantor_surjective : forall k : KPoint K,
      exists c : CantorName, cantor_decode c = k
  }.

  Record CantorFunctionRepresentation
      (K : EffectiveDualBall) (Q : EffectiveCantorSurjection K) := {
    CFun : Type;
    cfun_zero : CFun;
    cfun_add : CFun -> CFun -> CFun;
    cfun_smul : R -> CFun -> CFun;
    cfun_eval : CFun -> CantorName K Q -> R;
    cfun_eval_zero : forall c, cfun_eval cfun_zero c = 0;
    cfun_eval_add : forall g h c,
      cfun_eval (cfun_add g h) c = cfun_eval g c + cfun_eval h c;
    cfun_eval_smul : forall a g c,
      cfun_eval (cfun_smul a g) c = a * cfun_eval g c;
    embed_cantor : X -> CFun;
    embed_cantor_eval : forall x c,
      cfun_eval (embed_cantor x) c =
        evaluate K (cantor_decode K Q c) x;
    embed_cantor_add : forall x y,
      embed_cantor (cb_add B x y) = cfun_add (embed_cantor x) (embed_cantor y);
    embed_cantor_smul : forall a x,
      embed_cantor (cb_scale B a x) = cfun_smul a (embed_cantor x);
    cfun_norm : CFun -> R;
    embed_cantor_isometry : forall x,
      cfun_norm (embed_cantor x) = distance x (cb_zero B)
  }.

  Record IntervalExtension
      {K : EffectiveDualBall} {Q : EffectiveCantorSurjection K}
      (F : CantorFunctionRepresentation K Q) := {
    C01 : Type;
    c01_zero : C01;
    c01_add : C01 -> C01 -> C01;
    c01_smul : R -> C01 -> C01;
    c01_norm : C01 -> R;
    extend_to_interval : CFun K Q F -> C01;
    extension_zero : extend_to_interval (cfun_zero K Q F) = c01_zero;
    extension_add : forall g h,
      extend_to_interval (cfun_add K Q F g h)
        = c01_add (extend_to_interval g) (extend_to_interval h);
    extension_smul : forall a g,
      extend_to_interval (cfun_smul K Q F a g)
        = c01_smul a (extend_to_interval g);
    extension_isometric : forall g,
      c01_norm (extend_to_interval g) = cfun_norm K Q F g
  }.

  Record RangeInverse
      {K : EffectiveDualBall} {Q : EffectiveCantorSurjection K}
      {F : CantorFunctionRepresentation K Q}
      (E : IntervalExtension F) := {
    invert_range : C01 E -> option X;
    invert_on_embedding : forall x,
      invert_range (extend_to_interval F E (embed_cantor K Q F x)) = Some x
  }.

  Record EffectiveLinearUniversalityPackage := {
    elu_dual : EffectiveDualBall;
    elu_cantor : EffectiveCantorSurjection elu_dual;
    elu_cfun : CantorFunctionRepresentation elu_dual elu_cantor;
    elu_interval : IntervalExtension elu_cfun;
    elu_inverse : RangeInverse elu_interval
  }.

  Definition universal_embedding
      (P : EffectiveLinearUniversalityPackage) : X -> C01 (elu_interval P) :=
    fun x =>
      extend_to_interval (elu_cfun P) (elu_interval P)
        (embed_cantor (elu_dual P) (elu_cantor P) (elu_cfun P) x).

  Theorem universal_embedding_linear_add
      (P : EffectiveLinearUniversalityPackage) : forall x y,
    universal_embedding P (cb_add B x y)
      = c01_add (elu_interval P) (universal_embedding P x) (universal_embedding P y).
  Proof.
    intros x y. unfold universal_embedding.
    rewrite embed_cantor_add.
    apply extension_add.
  Qed.

  Theorem universal_embedding_linear_smul
      (P : EffectiveLinearUniversalityPackage) : forall a x,
    universal_embedding P (cb_scale B a x)
      = c01_smul (elu_interval P) a (universal_embedding P x).
  Proof.
    intros a x. unfold universal_embedding.
    rewrite embed_cantor_smul.
    apply extension_smul.
  Qed.

  Theorem universal_embedding_isometric
      (P : EffectiveLinearUniversalityPackage) : forall x,
    c01_norm (elu_interval P) (universal_embedding P x)
      = distance x (cb_zero B).
  Proof.
    intro x.
    unfold universal_embedding.
    rewrite extension_isometric.
    apply embed_cantor_isometry.
  Qed.

  Theorem universal_embedding_has_inverse_on_range
      (P : EffectiveLinearUniversalityPackage) : forall x,
    invert_range (elu_inverse P) (universal_embedding P x) = Some x.
  Proof.
    intro x.
    unfold universal_embedding.
    apply invert_on_embedding.
  Qed.

End Pipeline.

End UELAT_V3_LinearUniversalityPipeline.
