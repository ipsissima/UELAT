(** CoordinateFunctionalGraph.v -- converse coordinate-ball direction on the
    dense rational span. *)

From Coq Require Import Reals QArith Qreals List Lra Ring.
Import ListNotations.
Local Open Scope Q_scope.
From UELAT.V3 Require Import
  CertificateEnrichment ComputableBanach BanachNormLemmas
  NormalizedCoreCoordinates CoordinateDualBall.

Module UELAT_V3_CoordinateFunctionalGraph.
Import UELAT_V3_CertificateEnrichment.
Import UELAT_V3_ComputableBanach.
Import UELAT_V3_BanachNormLemmas.
Import UELAT_V3_NormalizedCoreCoordinates.
Import UELAT_V3_CoordinateDualBall.

Section SpanFunctional.
  Variable B : RealComputableBanachPresentation.
  Let X := carrier (cb_metric B).
  Variable a : CoordinateDualBallPoint B.

  Definition span_vector (ts : list RationalCoordinateTerm) : X :=
    core_decode (combination_code B ts).
  Definition span_value (ts : list RationalCoordinateTerm) : R :=
    coordinate_sum (cdb_coordinates a) ts.

  Lemma span_vector_nil : span_vector [] = cb_zero B.
  Proof. unfold span_vector. simpl. apply core_zero_sound. Qed.
  Lemma span_value_nil : span_value [] = 0.
  Proof. reflexivity. Qed.

  Lemma span_vector_append : forall xs ys,
    span_vector (xs ++ ys) = cb_add B (span_vector xs) (span_vector ys).
  Proof.
    intros xs ys. induction xs as [|[q i] rest IH].
    - simpl. unfold span_vector at 1 2. simpl.
      rewrite core_zero_sound, cb_add_zero_l. reflexivity.
    - simpl app. unfold span_vector in *; simpl in *.
      repeat rewrite core_add_sound. rewrite IH. apply cb_add_assoc.
  Qed.

  Lemma span_value_append : forall xs ys,
    span_value (xs ++ ys) = span_value xs + span_value ys.
  Proof.
    intros xs ys. induction xs as [|[q i] rest IH]; simpl.
    - ring.
    - unfold span_value in *; simpl in *. rewrite IH. ring.
  Qed.

  Fixpoint negate_terms (ts : list RationalCoordinateTerm) :
      list RationalCoordinateTerm :=
    match ts with
    | [] => []
    | (q,i) :: rest => (-q,i) :: negate_terms rest
    end.

  Lemma scale_neg_core_term : forall q i,
    core_decode
      (core_scale B (-q) (normalized_core_code B (core_enum B i)))
      = cb_neg B
          (core_decode
            (core_scale B q (normalized_core_code B (core_enum B i)))).
  Proof.
    intros q i. repeat rewrite core_scale_sound.
    unfold cb_neg. rewrite Q2R_opp, cb_scale_assoc.
    replace ((-1) * Q2R q)%R with (- Q2R q)%R by ring.
    reflexivity.
  Qed.

  Lemma span_vector_negate : forall ts,
    span_vector (negate_terms ts) = cb_neg B (span_vector ts).
  Proof.
    intro ts. induction ts as [|[q i] rest IH].
    - simpl. rewrite span_vector_nil. symmetry. apply cb_scale_zero_vector.
    - unfold span_vector in *; simpl in *.
      repeat rewrite core_add_sound.
      rewrite scale_neg_core_term, IH.
      unfold cb_neg at 2. rewrite cb_scale_add_vectors. reflexivity.
  Qed.

  Lemma span_value_negate : forall ts,
    span_value (negate_terms ts) = - span_value ts.
  Proof.
    intro ts. induction ts as [|[q i] rest IH].
    - reflexivity.
    - unfold span_value in *; simpl in *. rewrite Q2R_opp, IH. ring.
  Qed.

  Definition subtract_terms xs ys := xs ++ negate_terms ys.

  Lemma span_vector_subtract : forall xs ys,
    span_vector (subtract_terms xs ys)
      = cb_sub B (span_vector xs) (span_vector ys).
  Proof.
    intros xs ys. unfold subtract_terms, cb_sub.
    rewrite span_vector_append, span_vector_negate. reflexivity.
  Qed.

  Lemma span_value_subtract : forall xs ys,
    span_value (subtract_terms xs ys) = span_value xs - span_value ys.
  Proof.
    intros xs ys. unfold subtract_terms.
    rewrite span_value_append, span_value_negate. ring.
  Qed.

  Lemma admissible_span_bound : forall ts,
    Rabs (span_value ts) <= cb_norm B (span_vector ts).
  Proof.
    intro ts. unfold span_value, span_vector.
    exact (cdb_admissible a ts).
  Qed.

  Theorem coordinate_value_well_defined : forall xs ys,
    span_vector xs = span_vector ys -> span_value xs = span_value ys.
  Proof.
    intros xs ys Hxy.
    pose proof (admissible_span_bound (subtract_terms xs ys)) as Hbound.
    rewrite span_vector_subtract, span_value_subtract in Hbound.
    rewrite Hxy, cb_sub_self, cb_norm_zero in Hbound.
    pose proof (Rabs_pos (span_value xs - span_value ys)) as Habs0.
    lra.
  Qed.

  Definition CoordinateSpanGraph (x : X) (r : R) : Prop :=
    exists ts, x = span_vector ts /\ r = span_value ts.

  Theorem coordinate_span_graph_functional : forall x r s,
    CoordinateSpanGraph x r -> CoordinateSpanGraph x s -> r = s.
  Proof.
    intros x r s [ts [Hx Hr]] [us [Hx' Hs]].
    subst r s. apply coordinate_value_well_defined.
    now rewrite <- Hx, <- Hx'.
  Qed.

  Theorem coordinate_span_graph_bounded : forall x r,
    CoordinateSpanGraph x r -> Rabs r <= cb_norm B x.
  Proof.
    intros x r [ts [Hx Hr]]. subst x r. apply admissible_span_bound.
  Qed.
End SpanFunctional.

End UELAT_V3_CoordinateFunctionalGraph.
