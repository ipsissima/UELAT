(**
  OneDimensionalHBSeed.v -- exact one-dimensional SOURCE functional
  for manuscript Lemma 3.1, given a named nonzero vector.

  We construct the real line of scalar multiples inside the actual
  computable Banach carrier, prove injection of scalar coordinates,
  and a linear initial functional with exact norm 1 which hits v at
  norm(v). No Hahn--Banach EXTENSION is constructed here.

  Missing: a computable inverse from arbitrary promised names of
  points in span(v) to scalar coordinates; and the uniform
  epsilon-HB extension program into the full dual. This is not the
  complete manuscript Lemma 3.1.
*)
From Coq Require Import Reals Lra Ring.
From UELAT.V3 Require Import CertificateEnrichment ComputableBanach.

Module UELAT_V3_OneDimensionalHBSeed.
Import UELAT_V3_CertificateEnrichment.
Import UELAT_V3_ComputableBanach.
Local Open Scope R_scope.

Section OneDimensionalSource.
  Variable B : RealComputableBanachPresentation.
  Variable x : CoreNamedPoint B.
  Let v := core_named_value B x.
  Hypothesis Hv : 0 < cb_norm B v.

  Definition line_embed (a : R) : carrier (cb_metric B) :=
    cb_scale B a v.

  Definition source_norm (a : R) : R :=
    Rabs a * cb_norm B v.

  Definition source_functional (a : R) : R :=
    a * cb_norm B v.

  Lemma source_norm_realized : forall a,
    cb_norm B (line_embed a) = source_norm a.
  Proof.
    intro a. unfold line_embed, source_norm.
    apply cb_norm_scale.
  Qed.

  Lemma line_embed_add : forall a b,
    line_embed (a + b) = cb_add B (line_embed a) (line_embed b).
  Proof.
    intros a b. unfold line_embed.
    apply cb_scale_add_scalars.
  Qed.

  Lemma line_embed_scale : forall c a,
    line_embed (c * a) = cb_scale B c (line_embed a).
  Proof.
    intros c a. unfold line_embed.
    symmetry. apply cb_scale_assoc.
  Qed.

  Lemma line_embed_one : line_embed 1 = v.
  Proof.
    unfold line_embed.
    apply cb_scale_one.
  Qed.

  Lemma line_embed_zero : line_embed 0 = cb_zero B.
  Proof.
    unfold line_embed.
    apply cb_scale_zero_scalar.
  Qed.

  Lemma line_embed_injective : forall a b,
    line_embed a = line_embed b -> a = b.
  Proof.
    intros a b Hsame.
    assert (Hzero : line_embed (a - b) = cb_zero B).
    {
      unfold line_embed in *.
      replace (a - b) with (a + - b) by ring.
      rewrite cb_scale_add_scalars.
      rewrite Hsame.
      rewrite <- cb_scale_add_scalars.
      replace (b + - b) with 0 by ring.
      apply cb_scale_zero_scalar.
    }
    assert (Hnorm :
      Rabs (a - b) * cb_norm B v = 0).
    {
      pose proof (source_norm_realized (a - b)) as H.
      unfold source_norm in H.
      rewrite Hzero, cb_norm_zero in H.
      lra.
    }
    assert (Hab : Rabs (a - b) = 0).
    { pose proof (Rabs_pos (a - b)). nra. }
    apply Rabs_eq_0 in Hab.
    lra.
  Qed.

  (** Explicit coefficient recovery from three NORM evaluations.
      This avoids using the functional we are trying to construct.
      For y=a*v, the parallelogram-looking identity is special to
      this ONE-dimensional line; no inner-product law is assumed. *)
  Definition recovered_line_coordinate
      (y : carrier (cb_metric B)) : R :=
    (cb_norm B (cb_add B y v) ^ 2
     - cb_norm B (cb_sub B y v) ^ 2)
      / (4 * cb_norm B v ^ 2).

  Lemma absolute_square_identity : forall t : R,
    (Rabs t) ^ 2 = t ^ 2.
  Proof.
    intro t.
    destruct (Rle_dec 0 t) as [Ht|Ht].
    - rewrite Rabs_pos_eq by lra. reflexivity.
    - rewrite Rabs_left by lra. ring.
  Qed.

  Theorem recovered_coordinate_is_exact_on_span : forall a,
    recovered_line_coordinate (line_embed a) = a.
  Proof.
    intro a.
    assert (Hplus : cb_add B (line_embed a) v
        = cb_scale B (a + 1) v).
    {
      unfold line_embed.
      transitivity
        (cb_add B (cb_scale B a v) (cb_scale B 1 v)).
      - rewrite cb_scale_one. reflexivity.
      - rewrite <- cb_scale_add_scalars. reflexivity.
    }
    assert (Hminus : cb_sub B (line_embed a) v
        = cb_scale B (a - 1) v).
    {
      unfold cb_sub, cb_neg, line_embed.
      rewrite <- cb_scale_add_scalars.
      replace (a + -1) with (a - 1) by ring.
      reflexivity.
    }
    unfold recovered_line_coordinate.
    rewrite Hplus, Hminus.
    repeat rewrite cb_norm_scale.
    assert (Habsplus :
      (Rabs (a + 1) * cb_norm B v) ^ 2 =
      (a + 1) ^ 2 * cb_norm B v ^ 2).
    { rewrite <- (absolute_square_identity (a + 1)).
      ring. }
    assert (Habsminus :
      (Rabs (a - 1) * cb_norm B v) ^ 2 =
      (a - 1) ^ 2 * cb_norm B v ^ 2).
    { rewrite <- (absolute_square_identity (a - 1)).
      ring. }
    rewrite Habsplus, Habsminus.
    unfold Rdiv. field. nra.
  Qed.

  (** The actual Type-2 algorithm still needs certified error bounds
      for the numerator and reciprocal: the denominator is bounded
      away from zero using NamedNonzeroWitness. *)

  Lemma source_functional_add : forall a b,
    source_functional (a + b) =
      source_functional a + source_functional b.
  Proof.
    intros a b. unfold source_functional. ring.
  Qed.

  Lemma source_functional_scale : forall a b,
    source_functional (a * b) = a * source_functional b.
  Proof.
    intros a b. unfold source_functional. ring.
  Qed.

  Lemma source_functional_absolute_value : forall a,
    Rabs (source_functional a) = cb_norm B (line_embed a).
  Proof.
    intro a.
    unfold source_functional.
    rewrite Rabs_mult.
    rewrite (Rabs_pos_eq (cb_norm B v)) by lra.
    symmetry. apply source_norm_realized.
  Qed.

  Lemma source_functional_norm_one :
    (forall a, Rabs (source_functional a)
       <= cb_norm B (line_embed a))
    /\ (exists a, cb_norm B (line_embed a) > 0
      /\ Rabs (source_functional a)
            = cb_norm B (line_embed a)).
  Proof.
    split.
    - intro a. rewrite source_functional_absolute_value.
      apply Rle_refl.
    - exists 1.
      rewrite line_embed_one.
      split.
      + exact Hv.
      + rewrite <- line_embed_one.
        apply source_functional_absolute_value.
  Qed.

  Theorem source_functional_hits_input_vector :
    line_embed 1 = v
    /\ source_functional 1 = cb_norm B v.
  Proof.
    split.
    - apply line_embed_one.
    - unfold source_functional. ring.
  Qed.
End OneDimensionalSource.

End UELAT_V3_OneDimensionalHBSeed.
