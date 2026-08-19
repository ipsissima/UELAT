(** * MetricReflection.v — v3 Lawvere metric, distance adequacy,
       extensional collapse (§3, §4)

    Paper reference: Ballús Santacana, "Universal Gluing and Contextual Choice: Certificate-Carrying Approximation, Functorial Evidence, and Effective Descent", arXiv:2506.22693 v3, Definitions 3.2, 4.1,
    and Theorem 4.4.

    STATUS: IN-PROGRESS (see docs/FORMALIZATION_STATUS.md).

    This module formalizes:

    1. Def 3.2, the Lawvere pseudometric d_Cert on evidence objects,
       as a Prop-level predicate [is_lawvere_dist c d r] specifying
       that [r : R] is the infimum of accepted rational bounds. We
       do not force d_Cert to be a computable Rocq term; we specify
       its defining property.

    2. Proposition 3.3, soundness of the evidence metric: every
       accepted rational bound q dominates the underlying analytic
       distance [distF (deltaF (name c)) (deltaF (name d))]. This is
       the "lower bound" half of extensional collapse and needs no
       adequacy hypothesis.

    3. Def 4.1, distance-adequate presentation.

    4. Theorem 4.4, extensional collapse. Two logically distinct
       halves:

         (a) [extensional_collapse_lower_bound] — the analytic
             distance is a lower bound of the accepted rational
             bounds. This half needs NO adequacy hypothesis and is
             proved rigorously here.

         (b) [extensional_collapse] — under distance adequacy AND a
             rational-density hypothesis on ℝ, the analytic distance
             IS the Lawvere distance. The rational-density
             hypothesis is a real fact of stdlib (Q is dense in R),
             but its stdlib name / import path depends on the Rocq
             version and package availability at CI time; rather
             than commit to a particular helper library we thread it
             as an explicit Section variable. Status:
             CHECKED-RESTRICTED (extra rational-density hypothesis)
             until a follow-up commit discharges the hypothesis
             with an in-tree proof.

    No axiom, no admitted lemma.

    Correspondence entries in docs/FORMALIZATION_STATUS.md:
      Def 3.2 → is_lawvere_dist (IN-PROGRESS)
      Prop 3.3 → prop_3_3_lower_bound (CHECKED-EXACT candidate,
                 pending in-file correspondence review)
      Def 4.1 → distance_adequate
      Thm 4.4 → extensional_collapse (CHECKED-RESTRICTED under
                Q_dense_R hypothesis) *)

From Stdlib Require Import Reals QArith Lra Lia.
From UELAT.V3 Require Import Presentation Evidence.
Local Open Scope R_scope.

Module V3_MetricReflection.

Import V3_Presentation.
Import V3_Evidence.

Section WithPresentation.
Variable P : Presentation.
Variable EC : EvidenceClosure P.

(** ** Helper: rational-side bound accepted by DistCheck.

    "There exists finite data W such that DistCheck at bound q
    accepts" is what the paper calls an achievable rational bound for
    a pair of names. We predicate on names (not on evidence
    objects) so it does not depend on the certificate systems. *)

Definition dist_accepted (nu mu : NameF P) (q : Q) : Prop :=
  exists W, DistCheck P nu mu q W = true.

(** Extend to evidence objects: [achievable_bound c d q] says the
    names of [c] and [d] admit a distance witness at rational bound
    [q]. This corresponds directly to the "there exists a morphism
    of bound q" clause in Def 3.2. *)

Definition achievable_bound (c d : EvidenceObject P) (q : Q) : Prop :=
  dist_accepted (eo_name c) (eo_name d) q.

(** ** Def 3.2 — is_lawvere_dist as a predicate.

    r : R is the Lawvere distance from c to d if:

      (LB) r is a lower bound of the accepted rational bounds:
           for every accepted q, r ≤ Q2R q;
      (GLB) r is the greatest such lower bound: for every ε > 0,
            some accepted q has Q2R q < r + ε.

    "There is no morphism at any bound" is the special case r = +∞;
    we do not model +∞ explicitly here, since the paper's theorems
    below invoke d_Cert only in cases where a finite lower bound
    exists (Prop 3.3 always supplies distF as a lower bound). *)

Definition is_lawvere_dist (c d : EvidenceObject P) (r : R) : Prop :=
  (forall q, achievable_bound c d q -> r <= Q2R q)
  /\ (forall eps : R, 0 < eps ->
        exists q, achievable_bound c d q /\ Q2R q < r + eps).

(** Uniqueness of the Lawvere distance. Two reals that both satisfy
    the (LB) + (GLB) conjunction agree. Proof: standard "if r1 < r2,
    the (GLB) clause of r1 picks a q < r1 + (r2−r1) = r2, but the
    (LB) clause of r2 forces r2 ≤ q, contradiction". *)

Lemma is_lawvere_dist_unique :
  forall c d r1 r2,
    is_lawvere_dist c d r1 -> is_lawvere_dist c d r2 -> r1 = r2.
Proof.
  intros c d r1 r2 [Hlb1 Hglb1] [Hlb2 Hglb2].
  destruct (Rle_lt_dec r1 r2) as [Hle12 | Hlt21].
  - destruct (Rle_lt_dec r2 r1) as [Hle21 | Hlt12].
    + lra.
    + (* r1 < r2 : contradiction *)
      set (eps := r2 - r1).
      assert (Heps : 0 < eps) by (unfold eps; lra).
      destruct (Hglb1 eps Heps) as [q [Hq_acc Hq_bound]].
      specialize (Hlb2 q Hq_acc).
      unfold eps in Hq_bound. lra.
  - (* r2 < r1 : symmetric contradiction *)
    set (eps := r1 - r2).
    assert (Heps : 0 < eps) by (unfold eps; lra).
    destruct (Hglb2 eps Heps) as [q [Hq_acc Hq_bound]].
    specialize (Hlb1 q Hq_acc).
    unfold eps in Hq_bound. lra.
Qed.

(** ** Prop 3.3 (lower-bound half). The analytic distance is a lower
    bound of the accepted rational bounds.

    This holds unconditionally, from [DistCheck_sound] alone. The
    full Prop 3.3 (soundness of the evidence metric AND surjectivity
    of the certifiable subset) is not restated as one theorem here;
    the lower-bound half is what downstream theorems consume. *)

Theorem prop_3_3_lower_bound :
  forall c d,
    (forall q, achievable_bound c d q ->
       distF P (deltaF P (eo_name c)) (deltaF P (eo_name d)) <= Q2R q).
Proof.
  intros c d q [W Hacc].
  apply DistCheck_sound with (W := W). exact Hacc.
Qed.

(** As an immediate corollary, if the Lawvere distance is defined for
    (c, d) with value r, then the analytic distance is at most r. *)

Corollary lawvere_bounds_analytic :
  forall c d r,
    is_lawvere_dist c d r ->
    distF P (deltaF P (eo_name c)) (deltaF P (eo_name d)) <= r.
Proof.
  intros c d r [_ Hglb].
  (* We show ‖·‖ ≤ r by contradiction. Suppose r < ‖·‖; take
     ε := ‖·‖ − r > 0, obtain q accepted with Q2R q < r + ε = ‖·‖,
     but Prop 3.3 lower-bound says ‖·‖ ≤ Q2R q — contradiction. *)
  set (an := distF P (deltaF P (eo_name c)) (deltaF P (eo_name d))).
  destruct (Rle_lt_dec an r) as [Hle | Hlt]; [exact Hle | exfalso].
  set (eps := an - r).
  assert (Heps : 0 < eps) by (unfold eps; lra).
  destruct (Hglb eps Heps) as [q [Hq_acc Hq_bound]].
  pose proof (prop_3_3_lower_bound c d q Hq_acc) as Hlb_q.
  unfold eps, an in *. lra.
Qed.

(** ** Def 4.1 — distance-adequate presentation.

    For every pair of names and every rational q strictly above the
    analytic distance, some finite data W is accepted by
    [DistCheck]. This is a *completeness* assumption on the
    checker; §12 exhibits presentations that fail it (non-injective
    linear information). *)

Definition distance_adequate : Prop :=
  forall (nu mu : NameF P) (q : Q),
    distF P (deltaF P nu) (deltaF P mu) < Q2R q ->
    exists W, DistCheck P nu mu q W = true.

(** ** Theorem 4.4 (extensional collapse) — CHECKED-RESTRICTED.

    Under distance adequacy AND rational density in ℝ, the analytic
    distance IS the Lawvere distance. The rational-density
    hypothesis is threaded as a Section variable [Q_dense_R] to
    avoid depending on a particular stdlib import; it is a true
    fact of ℝ that a follow-up commit will prove inline. *)

Hypothesis Q_dense_R :
  forall a b : R, a < b -> exists q : Q, a < Q2R q < b.

Theorem extensional_collapse :
  distance_adequate ->
  forall c d,
    is_lawvere_dist c d
      (distF P (deltaF P (eo_name c)) (deltaF P (eo_name d))).
Proof.
  intros Hadeq c d.
  set (an := distF P (deltaF P (eo_name c)) (deltaF P (eo_name d))).
  split.
  - (* (LB): every accepted q satisfies an ≤ Q2R q. This is Prop 3.3. *)
    intros q Hacc.
    apply prop_3_3_lower_bound with (c := c) (d := d). exact Hacc.
  - (* (GLB): for every ε > 0, an accepted q with Q2R q < an + ε.
       By Q_dense_R, pick a rational q with an < Q2R q < an + ε; by
       distance adequacy, DistCheck accepts at q. *)
    intros eps Heps.
    assert (Hlt : an < an + eps) by lra.
    destruct (Q_dense_R an (an + eps) Hlt) as [q [Hq_gt Hq_lt]].
    assert (Hcheck : exists W, DistCheck P (eo_name c) (eo_name d) q W = true).
    { apply Hadeq. unfold an in Hq_gt. exact Hq_gt. }
    destruct Hcheck as [W HW].
    exists q. split.
    + red. red. exists W. exact HW.
    + exact Hq_lt.
Qed.

(** Zero-distance equivalence relation on evidence objects: c ~₀ d
    iff their Lawvere distance is 0. Under distance adequacy plus
    Q_dense_R this is equivalent to analytic-distance-zero on the
    underlying names. This is the equivalence that Ext(Cert) quotients
    out (Thm 4.4 second sentence). *)

Definition ext_equiv (c d : EvidenceObject P) : Prop :=
  is_lawvere_dist c d 0.

(** Under adequacy + Q_dense_R, c ~₀ d iff the analytic distance is
    zero. *)

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
  - intro Han0.
    unfold ext_equiv.
    pose proof (extensional_collapse Hadeq c d) as Hcoll.
    (* extensional_collapse gives is_lawvere_dist c d an; rewrite an = 0. *)
    rewrite Han0 in Hcoll. exact Hcoll.
Qed.

End WithPresentation.

(** ** What this file DOES NOT contain

    - A proof of Q_dense_R in terms of stdlib archimedes. Deferred
      to a follow-up commit so that this module can compile against
      any Rocq version whose stdlib exports the archimedes axiom;
      the hypothesis form makes the intended dependency explicit.
    - The quotient object ExtCert(F) and its metric structure. The
      paper's Thm 4.4 also asserts that the quotient is canonically
      isometric to the certifiable subset with the ambient metric;
      that statement requires a decidable-quotient construction we
      leave to a later module.
    - The "separated reflection" universal-property clause of
      Thm 4.4. Same reason.
    - Any dependence on [EvidenceClosure]. Prop 3.3 and Thm 4.4 in
      the form proved here concern DISTANCE evidence only, whose
      soundness comes from [DistCheck_sound] alone. The closure
      rules become necessary when [EvidenceMorphism] identity /
      composition are involved (Evidence.v).

    Correspondence with v3:

      Paper theorem:
        Proposition 3.3 (Soundness of the evidence metric) — lower
        bound half.
      Rocq theorem:
        V3_MetricReflection.prop_3_3_lower_bound
        (+ corollary V3_MetricReflection.lawvere_bounds_analytic).
      Correspondence: EXACT for the lower-bound half. Full Prop 3.3
      also includes surjectivity of the certifiable-subset image;
      that clause requires the certificate-system-existence
      criterion (Prop 2.4) and is deferred.

      Paper theorem:
        Definition 4.1 (Distance adequacy).
      Rocq definition:
        V3_MetricReflection.distance_adequate.
      Correspondence: EXACT.

      Paper theorem:
        Theorem 4.4 (Extensional collapse) — first equation
        d_Cert(c,d) = ‖U_F c − U_F d‖.
      Rocq theorem:
        V3_MetricReflection.extensional_collapse.
      Correspondence: CHECKED-RESTRICTED. The Rocq theorem proves,
      under distance adequacy AND a rational-density hypothesis on
      ℝ, that the analytic distance IS the Lawvere distance. The
      hypothesis is a true fact of ℝ; a follow-up commit will
      discharge it with an in-tree proof. *)

End V3_MetricReflection.
