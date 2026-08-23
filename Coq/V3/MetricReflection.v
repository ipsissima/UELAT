(** * MetricReflection.v — v3 Lawvere metric, distance adequacy,
       extensional collapse (§3, §4)

    Paper reference: Ballús Santacana, "Universal Gluing and Contextual
    Choice: Certificate-Carrying Approximation, Functorial Evidence, and
    Effective Descent", arXiv:2506.22693 v3, Definitions 3.2, 4.1, and
    Theorem 4.4.

    STATUS: IN-PROGRESS (see docs/FORMALIZATION_STATUS.md).

    Rebased onto normalized evidence: the achievable-bound relation is
    now [V3_Presentation.certified_dist], i.e. "some normalized spine
    runs between these names at announced bound at most q", and bounds
    are canonical rationals [Qc]. The lower-bound half of Prop 3.3 is
    consequently a corollary of the checker-realization bridge
    [certified_dist_sound] rather than of an assumed whole-claim
    soundness field. *)

From Stdlib Require Import Reals QArith Qreals Qcanon Lra Lia.
From UELAT.V3 Require Import EvidenceSyntax Presentation Evidence.
Local Open Scope R_scope.

Module V3_MetricReflection.

Import V3_EvidenceSyntax.
Import V3_Presentation.
Import V3_Evidence.

Section WithPresentation.
Variable P : Presentation.

(** ** Achievable bounds between evidence objects. *)

Definition achievable_bound (c d : EvidenceObject P) (q : Qc) : Prop :=
  certified_dist P (eo_name c) (eo_name d) q.

(** Every morphism realizes its own bound as achievable. *)

Lemma achievable_of_morphism :
  forall (c d : EvidenceObject P) (f : EvidenceMorphism c d),
    achievable_bound c d (em_bound f).
Proof. intros c d f. apply em_certifies. Qed.

(** ** Def 3.2 — the Lawvere distance, as a greatest-lower-bound
    predicate.

    [r] is the Lawvere distance from [c] to [d] when it is a lower
    bound of the achievable rational bounds and the greatest such. We
    specify the property rather than constructing an infimum term, so
    that no completeness machinery is smuggled in. *)

Definition is_lawvere_dist (c d : EvidenceObject P) (r : R) : Prop :=
  (forall q, achievable_bound c d q -> r <= Qc2R q)
  /\ (forall eps : R, 0 < eps ->
        exists q, achievable_bound c d q /\ Qc2R q < r + eps).

Lemma is_lawvere_dist_unique :
  forall c d r1 r2,
    is_lawvere_dist c d r1 -> is_lawvere_dist c d r2 -> r1 = r2.
Proof.
  intros c d r1 r2 [Hlb1 Hglb1] [Hlb2 Hglb2].
  destruct (Rle_lt_dec r1 r2) as [Hle12 | Hlt21].
  - destruct (Rle_lt_dec r2 r1) as [Hle21 | Hlt12].
    + lra.
    + set (eps := r2 - r1).
      assert (Heps : 0 < eps) by (unfold eps; lra).
      destruct (Hglb1 eps Heps) as [q [Hq_acc Hq_bound]].
      specialize (Hlb2 q Hq_acc). unfold eps in Hq_bound. lra.
  - set (eps := r1 - r2).
    assert (Heps : 0 < eps) by (unfold eps; lra).
    destruct (Hglb2 eps Heps) as [q [Hq_acc Hq_bound]].
    specialize (Hlb1 q Hq_acc). unfold eps in Hq_bound. lra.
Qed.

(** ** Prop 3.3, lower-bound half.

    The analytic distance is a lower bound of every achievable rational
    bound. Unconditional — a direct corollary of the bridge. *)

Theorem prop_3_3_lower_bound :
  forall c d,
    forall q, achievable_bound c d q ->
      distF P (deltaF P (eo_name c)) (deltaF P (eo_name d)) <= Qc2R q.
Proof.
  intros c d q Hq. apply certified_dist_sound. exact Hq.
Qed.

Corollary lawvere_bounds_analytic :
  forall c d r,
    is_lawvere_dist c d r ->
    distF P (deltaF P (eo_name c)) (deltaF P (eo_name d)) <= r.
Proof.
  intros c d r [_ Hglb].
  set (an := distF P (deltaF P (eo_name c)) (deltaF P (eo_name d))).
  destruct (Rle_lt_dec an r) as [Hle | Hlt]; [exact Hle | exfalso].
  set (eps := an - r).
  assert (Heps : 0 < eps) by (unfold eps; lra).
  destruct (Hglb eps Heps) as [q [Hq_acc Hq_bound]].
  pose proof (prop_3_3_lower_bound c d q Hq_acc) as Hlb_q.
  unfold eps, an in *. lra.
Qed.

(** ** Def 4.1 — distance adequacy.

    For every pair of names and every rational strictly above the
    analytic distance, a normalized spine certifies that bound. This is
    a COMPLETENESS assumption on the evidence language; §12 exhibits
    interfaces that fail it. *)

Definition distance_adequate : Prop :=
  forall (nu mu : NameF P) (q : Qc),
    distF P (deltaF P nu) (deltaF P mu) < Qc2R q ->
    certified_dist P nu mu q.

(** ** Theorem 4.4 (extensional collapse), first equation.

    Under distance adequacy and rational density in R, the analytic
    distance IS the Lawvere distance. Density is threaded as an
    explicit Section hypothesis rather than pulled from a particular
    stdlib helper; it is a true fact of R, and discharging it inline is
    tracked as follow-up. *)

Hypothesis Qc_dense_R :
  forall a b : R, a < b -> exists q : Qc, a < Qc2R q < b.

Theorem extensional_collapse :
  distance_adequate ->
  forall c d,
    is_lawvere_dist c d
      (distF P (deltaF P (eo_name c)) (deltaF P (eo_name d))).
Proof.
  intros Hadeq c d.
  set (an := distF P (deltaF P (eo_name c)) (deltaF P (eo_name d))).
  split.
  - intros q Hacc. apply prop_3_3_lower_bound with (c := c) (d := d). exact Hacc.
  - intros eps Heps.
    assert (Hlt : an < an + eps) by lra.
    destruct (Qc_dense_R an (an + eps) Hlt) as [q [Hq_gt Hq_lt]].
    exists q. split; [| exact Hq_lt].
    unfold achievable_bound. apply Hadeq. unfold an in Hq_gt. exact Hq_gt.
Qed.

Definition ext_equiv (c d : EvidenceObject P) : Prop :=
  is_lawvere_dist c d 0.

Corollary ext_equiv_iff_analytic_zero :
  distance_adequate ->
  forall c d,
    ext_equiv c d <->
    distF P (deltaF P (eo_name c)) (deltaF P (eo_name d)) = 0.
Proof.
  intros Hadeq c d. split.
  - intro Hext.
    pose proof (lawvere_bounds_analytic c d 0 Hext) as Hle.
    pose proof (distF_nonneg P (deltaF P (eo_name c)) (deltaF P (eo_name d))) as Hge.
    lra.
  - intro Han0. unfold ext_equiv.
    pose proof (extensional_collapse Hadeq c d) as Hcoll.
    rewrite Han0 in Hcoll. exact Hcoll.
Qed.

End WithPresentation.

(** ** Correspondence with v3

      Def 3.2  → is_lawvere_dist          (IN-PROGRESS; GLB predicate,
                                           no infimum term)
      Prop 3.3 → prop_3_3_lower_bound     (CHECKED-RESTRICTED; the
                                           lower-bound half only)
      Def 4.1  → distance_adequate        (DEFINITION-EXACT)
      Thm 4.4  → extensional_collapse     (CHECKED-RESTRICTED, under
                                           the Qc_dense_R hypothesis)

    Change of basis relative to the previous revision: the achievable
    bound relation is now [certified_dist], so Prop 3.3's lower-bound
    half rests on the DERIVED bridge [certified_dist_sound] rather than
    on an assumed whole-claim [DistCheck_sound] field. The theorem
    statements are otherwise unchanged. *)

End V3_MetricReflection.
