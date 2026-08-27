(** FiniteMeasureBoundary.v -- v3 Corollary 8.6.

    The result is deliberately internal.  Starting from finite-measure
    primitives and constructors that preserve the finite-measure regularity
    class, the CCP-generated universe remains inside that class.  A finite
    equidecomposition by admitted measure-preserving motions therefore cannot
    duplicate a positive finite-measure object.  This leaves the classical
    Banach--Tarski theorem, which uses nonmeasurable pieces outside the declared
    generated universe, untouched.
*)

From Coq Require Import Reals List Lra.
Import ListNotations.
From UELAT.V3 Require Import ContextualChoice.

Module UELAT_V3_FiniteMeasureBoundary.
Import UELAT_V3_ContextualChoice.

Fixpoint rsum (xs : list R) : R :=
  match xs with
  | [] => 0
  | x :: xs' => x + rsum xs'
  end.

Section AlgebraicDuplication.

  Variable muA : R.
  Hypothesis muA_positive : 0 < muA.

  Variable piece_measures image_measures : list R.

  Hypothesis finite_partition_additivity :
    rsum piece_measures = muA.

  Hypothesis admitted_isometries_preserve_measure :
    rsum image_measures = rsum piece_measures.

  Hypothesis duplication_additivity :
    rsum image_measures = 2 * muA.

  Theorem no_finite_measure_preserving_duplication : False.
  Proof.
    rewrite admitted_isometries_preserve_measure in duplication_additivity.
    rewrite finite_partition_additivity in duplication_additivity.
    lra.
  Qed.

End AlgebraicDuplication.

Section GeneratedFiniteMeasureBoundary.

  Context {Obj : Type}.

  Variable RationalBoxPrimitive : Obj -> Prop.
  Variable Step0 : Obj -> Prop.
  Variable Step1 : Obj -> Obj -> Prop.
  Variable Step2 : Obj -> Obj -> Obj -> Prop.
  Variable mu : Obj -> R.

  Definition FiniteMeasureObject (x : Obj) : Prop :=
    0 <= mu x /\ exists B : R, mu x <= B.

  Hypothesis rational_boxes_finite : forall x,
    RationalBoxPrimitive x -> FiniteMeasureObject x.
  Hypothesis nullary_preserves_finite : forall out,
    Step0 out -> FiniteMeasureObject out.
  Hypothesis unary_preserves_finite : forall x out,
    FiniteMeasureObject x -> Step1 x out -> FiniteMeasureObject out.
  Hypothesis binary_preserves_finite : forall x y out,
    FiniteMeasureObject x -> FiniteMeasureObject y ->
    Step2 x y out -> FiniteMeasureObject out.

  Definition GeneratedFinite :=
    @Generated Obj RationalBoxPrimitive Step0 Step1 Step2.

  Theorem generated_objects_remain_finite_measure : forall x,
    GeneratedFinite x -> FiniteMeasureObject x.
  Proof.
    intros x Hx.
    eapply (@invariant_preservation Obj
              RationalBoxPrimitive Step0 Step1 Step2
              FiniteMeasureObject);
      eauto.
  Qed.

  (** Internal Banach--Tarski boundary in the generated class. *)
  Theorem no_internal_finite_equidecomposition_duplication :
    forall A,
      GeneratedFinite A ->
      0 < mu A ->
      forall piece_measures image_measures,
        rsum piece_measures = mu A ->
        rsum image_measures = rsum piece_measures ->
        rsum image_measures = 2 * mu A ->
        False.
  Proof.
    intros A Hgen Hpos pieces images Hpart Hiso Hdup.
    pose proof (generated_objects_remain_finite_measure A Hgen) as Hfinite.
    destruct Hfinite as [Hnonneg [B HB]].
    rewrite Hiso in Hdup.
    rewrite Hpart in Hdup.
    lra.
  Qed.

  Corollary no_internal_duplication_statement :
    forall A,
      GeneratedFinite A ->
      0 < mu A ->
      ~ (exists piece_measures image_measures,
          rsum piece_measures = mu A /\
          rsum image_measures = rsum piece_measures /\
          rsum image_measures = 2 * mu A).
  Proof.
    intros A Hgen Hpos [pieces [images [Hp [Hi Hd]]]].
    eapply no_internal_finite_equidecomposition_duplication; eauto.
  Qed.

End GeneratedFiniteMeasureBoundary.

End UELAT_V3_FiniteMeasureBoundary.
