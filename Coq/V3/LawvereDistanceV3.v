(** * LawvereDistanceV3.v — exact term-level Definition 3.2

    The manuscript defines

      d_Cert(c,d) = inf { q in Q_{>=0} | exists W, (q,W):c -> d }

    with the convention inf(empty)=+infinity. The older formalization
    stopped at the GLB predicate [is_lawvere_dist] over ordinary reals.

    Here we construct the term itself. For a nonempty achievable set,
    the infimum is obtained from Rocq's real completeness theorem by
    taking the negative of the least upper bound of the negated set.
    For the empty set we return an explicit infinity constructor. No
    infimum axiom is introduced.

    The empty/nonempty branch is classical and therefore intentionally
    visible in the assumption audit. *)

From Stdlib Require Import Reals Qcanon ClassicalDescription Classical Lra.
From UELAT.V3 Require Import Presentation Evidence MetricReflection.
Local Open Scope R_scope.

Module V3_LawvereDistanceV3.

Import V3_Presentation.
Import V3_Evidence.
Import V3_MetricReflection.

Record NNReal : Type := {
  nnr_val : R;
  nnr_nonneg : 0 <= nnr_val
}.

Inductive ENNReal : Type :=
| enn_finite : NNReal -> ENNReal
| enn_infty : ENNReal.

Section WithPresentation.
Variable P : Presentation.

Definition neg_achievable
    (c d : EvidenceObject P) (x : R) : Prop :=
  exists q : Qc, achievable_bound P c d q /\ x = - Qc2R q.

Lemma neg_achievable_upper_analytic :
  forall c d,
    is_upper_bound (neg_achievable c d)
      (- distF P (deltaF P (eo_name c)) (deltaF P (eo_name d))).
Proof.
  intros c d x [q [Hq Hx]]. subst x.
  pose proof (prop_3_3_lower_bound P c d q Hq) as Hsound.
  lra.
Qed.

Lemma neg_achievable_bound :
  forall c d, bound (neg_achievable c d).
Proof.
  intros c d.
  exists (- distF P (deltaF P (eo_name c)) (deltaF P (eo_name d))).
  apply neg_achievable_upper_analytic.
Qed.

Lemma neg_achievable_nonempty :
  forall c d,
    (exists q : Qc, achievable_bound P c d q) ->
    exists x : R, neg_achievable c d x.
Proof.
  intros c d [q Hq].
  exists (- Qc2R q). exists q. split; [exact Hq | reflexivity].
Qed.

Definition neg_lub_pack
    (c d : EvidenceObject P)
    (Hex : exists q : Qc, achievable_bound P c d q)
  : { m : R | is_lub (neg_achievable c d) m } :=
  completeness (neg_achievable c d)
    (neg_achievable_bound c d)
    (neg_achievable_nonempty c d Hex).

Definition neg_lub
    (c d : EvidenceObject P)
    (Hex : exists q : Qc, achievable_bound P c d q) : R :=
  proj1_sig (neg_lub_pack c d Hex).

Lemma neg_lub_spec :
  forall c d Hex,
    is_lub (neg_achievable c d) (neg_lub c d Hex).
Proof.
  intros c d Hex. unfold neg_lub.
  exact (proj2_sig (neg_lub_pack c d Hex)).
Qed.

Definition inf_achievable_real
    (c d : EvidenceObject P)
    (Hex : exists q : Qc, achievable_bound P c d q) : R :=
  - neg_lub c d Hex.

Lemma inf_achievable_real_nonneg :
  forall c d Hex, 0 <= inf_achievable_real c d Hex.
Proof.
  intros c d Hex.
  destruct (neg_lub_spec c d Hex) as [_ Hleast].
  pose proof (Hleast
    (- distF P (deltaF P (eo_name c)) (deltaF P (eo_name d)))
    (neg_achievable_upper_analytic c d)) as Hlub.
  unfold inf_achievable_real.
  pose proof (distF_nonneg P (deltaF P (eo_name c)) (deltaF P (eo_name d))) as Han.
  lra.
Qed.

Definition inf_achievable_nnreal
    (c d : EvidenceObject P)
    (Hex : exists q : Qc, achievable_bound P c d q) : NNReal :=
  {| nnr_val := inf_achievable_real c d Hex;
     nnr_nonneg := inf_achievable_real_nonneg c d Hex |}.

Theorem inf_achievable_is_lawvere :
  forall c d Hex,
    is_lawvere_dist P c d (inf_achievable_real c d Hex).
Proof.
  intros c d Hex.
  destruct (neg_lub_spec c d Hex) as [Hub Hleast].
  split.
  - intros q Hq.
    specialize (Hub (- Qc2R q)).
    assert (HE : neg_achievable c d (- Qc2R q)).
    { exists q. split; [exact Hq | reflexivity]. }
    specialize (Hub HE).
    unfold inf_achievable_real. lra.
  - intros eps Heps.
    apply NNPP. intro Hnone.
    assert (Htight : is_upper_bound (neg_achievable c d)
                      (neg_lub c d Hex - eps)).
    {
      intros x [q [Hq Hx]]. subst x.
      apply Rnot_lt_le. intro Hgt.
      apply Hnone. exists q. split; [exact Hq |].
      unfold inf_achievable_real. lra.
    }
    specialize (Hleast (neg_lub c d Hex - eps) Htight).
    lra.
Qed.

Definition d_Cert (c d : EvidenceObject P) : ENNReal :=
  match excluded_middle_informative
          (exists q : Qc, achievable_bound P c d q) with
  | left Hex => enn_finite (inf_achievable_nnreal c d Hex)
  | right _ => enn_infty
  end.

Theorem d_Cert_nonempty_spec :
  forall c d (Hex : exists q : Qc, achievable_bound P c d q),
    exists r : NNReal,
      d_Cert c d = enn_finite r /\
      is_lawvere_dist P c d (nnr_val r).
Proof.
  intros c d Hex.
  unfold d_Cert.
  destruct (excluded_middle_informative
    (exists q : Qc, achievable_bound P c d q)) as [Hex'|Hempty].
  - exists (inf_achievable_nnreal c d Hex'). split; [reflexivity |].
    apply inf_achievable_is_lawvere.
  - contradiction.
Qed.

Theorem d_Cert_empty_spec :
  forall c d,
    ~ (exists q : Qc, achievable_bound P c d q) ->
    d_Cert c d = enn_infty.
Proof.
  intros c d Hempty. unfold d_Cert.
  destruct (excluded_middle_informative
    (exists q : Qc, achievable_bound P c d q)) as [Hex|Hnone].
  - contradiction.
  - reflexivity.
Qed.

Theorem d_Cert_of_morphism_finite :
  forall c d (f : EvidenceMorphism c d),
    exists r : NNReal, d_Cert c d = enn_finite r.
Proof.
  intros c d f.
  assert (Hex : exists q : Qc, achievable_bound P c d q).
  { exists (em_bound f). apply achievable_of_morphism. }
  destruct (d_Cert_nonempty_spec c d Hex) as [r [Hr _]].
  exists r. exact Hr.
Qed.

End WithPresentation.

End V3_LawvereDistanceV3.
