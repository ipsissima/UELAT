(** SearchableCoordinateCoreFunctional2.v -- executable dense-core functional
    from an admissible dual coordinate point. *)

From Coq Require Import Reals QArith Qreals Lra Ring Field.
From UELAT.V3 Require Import
  CertificateEnrichment ComputableBanach SearchableCore
  NormalizedCoreCoordinates CoordinateDualBall CoordinateFunctionalGraph.

Module UELAT_V3_SearchableCoordinateCoreFunctional2.
Import UELAT_V3_CertificateEnrichment.
Import UELAT_V3_ComputableBanach.
Import UELAT_V3_SearchableCore.
Import UELAT_V3_NormalizedCoreCoordinates.
Import UELAT_V3_CoordinateDualBall.
Import UELAT_V3_CoordinateFunctionalGraph.

Section DirectCoreFunctional.
  Variable S : SearchableCorePresentation.
  Let B := sc_banach S.
  Variable a : CoordinateDualBallPoint B.

  Definition direct_core_value (p : core_code B) : R :=
    Q2R (core_scale_factor B p) * cdb_coordinates a (core_index S p).

  Lemma normalized_index_for_code : forall p,
    normalized_core B (core_index S p)
      = core_decode (normalized_core_code B p).
  Proof.
    intro p. unfold normalized_core. rewrite core_index_correct. reflexivity.
  Qed.

  Lemma rescale_normalized_code : forall p,
    cb_scale B (Q2R (core_scale_factor B p))
      (core_decode (normalized_core_code B p)) = core_decode p.
  Proof.
    intro p. unfold normalized_core_code.
    rewrite core_scale_sound, cb_scale_assoc.
    rewrite Q2R_inv by apply core_scale_factor_nonzero_Q.
    pose proof (core_scale_factor_real_positive B p) as Hpos.
    replace
      (Q2R (core_scale_factor B p) * / Q2R (core_scale_factor B p))
      with 1 by (field; lra).
    apply cb_scale_one.
  Qed.

  Theorem direct_core_value_in_span_graph : forall p,
    CoordinateSpanGraph B a (core_decode p) (direct_core_value p).
  Proof.
    intro p.
    unfold CoordinateSpanGraph.
    exists [(core_scale_factor B p, core_index S p)].
    split.
    - unfold span_vector. simpl.
      rewrite core_add_sound, core_scale_sound, core_zero_sound, cb_add_zero_r.
      rewrite normalized_index_for_code.
      apply rescale_normalized_code.
    - unfold span_value, direct_core_value. simpl.
      ring.
  Qed.

  Theorem direct_core_value_bounded : forall p,
    Rabs (direct_core_value p) <= cb_norm B (core_decode p).
  Proof.
    intro p. eapply coordinate_span_graph_bounded.
    apply direct_core_value_in_span_graph.
  Qed.

  Theorem direct_core_value_zero : direct_core_value (core_zero B) = 0.
  Proof.
    eapply coordinate_span_graph_functional.
    - apply direct_core_value_in_span_graph.
    - unfold CoordinateSpanGraph. exists []. split.
      + rewrite span_vector_nil, core_zero_sound. reflexivity.
      + rewrite span_value_nil. reflexivity.
  Qed.

  Theorem direct_core_value_add : forall p q,
    direct_core_value (core_add B p q) = direct_core_value p + direct_core_value q.
  Proof.
    intros p q.
    eapply coordinate_span_graph_functional.
    - apply direct_core_value_in_span_graph.
    - rewrite core_add_sound.
      apply coordinate_span_graph_add.
      + apply direct_core_value_in_span_graph.
      + apply direct_core_value_in_span_graph.
  Qed.

  Theorem direct_core_value_scale : forall c p,
    direct_core_value (core_scale B c p) = Q2R c * direct_core_value p.
  Proof.
    intros c p.
    eapply coordinate_span_graph_functional.
    - apply direct_core_value_in_span_graph.
    - rewrite core_scale_sound.
      apply coordinate_span_graph_scale_Q.
      apply direct_core_value_in_span_graph.
  Qed.

  Theorem admissible_coordinate_gives_bounded_rational_core_functional :
    (forall p, Rabs (direct_core_value p) <= cb_norm B (core_decode p))
    /\ direct_core_value (core_zero B) = 0
    /\ (forall p q,
      direct_core_value (core_add B p q) = direct_core_value p + direct_core_value q)
    /\ (forall c p,
      direct_core_value (core_scale B c p) = Q2R c * direct_core_value p).
  Proof.
    repeat split.
    - apply direct_core_value_bounded.
    - apply direct_core_value_zero.
    - apply direct_core_value_add.
    - apply direct_core_value_scale.
  Qed.
End DirectCoreFunctional.

End UELAT_V3_SearchableCoordinateCoreFunctional2.
