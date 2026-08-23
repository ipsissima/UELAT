(** * Evidence.v — v3 proof-relevant evidence category (§2–§3)

    Paper reference: Ballús Santacana, "Universal Gluing and Contextual
    Choice: Certificate-Carrying Approximation, Functorial Evidence, and
    Effective Descent", arXiv:2506.22693 v3, Definitions 2.3 and 3.1.

    STATUS: IN-PROGRESS (see docs/FORMALIZATION_STATUS.md).

    ** Normalized witnesses, but genuine (q,W) morphism data

    The normalized witness itself is an endpoint-indexed flattened spine
    ([V3_EvidenceSyntax.Spine]).  Its endpoints live in the type and its
    intrinsic bound is [sp_bound].  Definition 3.1, however, makes an
    evidence morphism the accepted PAIR [(q,W)]: the announced rational
    bound [q] is proof-relevant data and may contain slack above the
    intrinsic spine bound.  We therefore retain [q] explicitly rather
    than silently canonicalizing every morphism to [sp_bound W].

    The slack condition is stored as a BOOLEAN check

      qcleb (sp_bound W) q = true

    rather than as an arbitrary Prop proof.  This matters for strict
    category laws: after the [Qc] bound and normalized spine components
    are identified, the remaining checker-equality proofs are equal by
    decidable UIP ([checker_proof_irrelevant]), with no proof-irrelevance
    axiom.

    Identity is [(0, empty spine)] and composition is

      (q1,W1) ; (q2,W2) = (q1+q2, W1++W2).

    Because bounds are canonical rationals [Qc] and witness composition
    is normalized concatenation, the category laws below are genuine
    Leibniz equalities.

    ** What the EvidenceClosure record is still for

    Reflexivity and the triangle rule are now theorems (empty spine,
    concatenation), so they are gone from the closure record.
    SYMMETRY and WEAKENING remain abstract witness constructors: they
    are genuine rules of the paper's evidence language that the current
    normal form does not yet realize. Keeping them as an explicit,
    named record makes the residual assumption visible instead of
    burying it. *)

From Stdlib Require Import List QArith Qcanon Bool Eqdep_dec Lra Lia.
From UELAT.V3 Require Import EvidenceSyntax Presentation.
Import ListNotations.
Local Open Scope Qc_scope.

Module V3_Evidence.

Import V3_EvidenceSyntax.
Import V3_Presentation.

Section WithPresentation.
Variable P : Presentation.

(** ** Residual closure rules. *)

Record EvidenceClosure : Type := {
  ec_sym :
    forall (nu mu : NameF P) (q : Qc),
      certified_dist P nu mu q -> certified_dist P mu nu q;
  ec_weaken :
    forall (nu mu : NameF P) (q q' : Qc),
      (q <= q')%Qc ->
      certified_dist P nu mu q -> certified_dist P nu mu q';
  ec_mixed :
    forall (nu mu : NameF P) (p : CodeF P) (q r : Qc) (V : list bool),
      certified_dist P nu mu q ->
      AppCheck P mu p r V = true ->
      exists V', AppCheck P nu p (q + r) V' = true
}.

(** ** Def 2.3 — Certificate system over a named point. *)

Record CertSystem (nu : NameF P) : Type := {
  cs_run     : Qc -> CodeF P * Qc * list bool;
  cs_bound_lt :
    forall eps : Qc, 0 < eps ->
      let '(_p, ebar, _V) := cs_run eps in 0 <= ebar /\ ebar < eps;
  cs_accept :
    forall eps : Qc, 0 < eps ->
      let '(p, ebar, V) := cs_run eps in
      AppCheck P nu p ebar V = true
}.

(** ** Def 3.1 — Objects of Cert_ev(F). *)

Record EvidenceObject : Type := {
  eo_name   : NameF P;
  eo_system : CertSystem eo_name
}.

(** Boolean comparison for canonical rationals.  [Qcle] is just [Qle]
    on the underlying rational, so the stdlib's [Qle_bool_iff] is the
    exact specification lemma we need. *)

Definition qcleb (a b : Qc) : bool := Qle_bool a b.

Lemma qcleb_iff :
  forall a b : Qc, qcleb a b = true <-> (a <= b)%Qc.
Proof.
  intros a b. unfold qcleb, Qcle. apply Qle_bool_iff.
Qed.

Lemma qcleb_proof_irrelevant :
  forall a b : Qc (p q : qcleb a b = true), p = q.
Proof.
  intros a b p q. apply checker_proof_irrelevant.
Qed.

(** ** Def 3.1 — proof-relevant morphisms are the actual pair (q,W).

    [em_q] is the announced bound.  [em_spine] is the normalized witness.
    [em_slack] is a decidable finite check that the witness's intrinsic
    bound is no larger than the announced bound. *)

Record EvidenceMorphism (c d : EvidenceObject) : Type := {
  em_q     : Qc;
  em_spine : PSpine P (eo_name c) (eo_name d);
  em_slack : qcleb (sp_bound em_spine) em_q = true
}.

Definition em_bound {c d : EvidenceObject} (f : EvidenceMorphism c d) : Qc :=
  em_q f.

Lemma em_spine_le_bound :
  forall (c d : EvidenceObject) (f : EvidenceMorphism c d),
    (sp_bound (em_spine f) <= em_bound f)%Qc.
Proof.
  intros c d f. apply (proj1 (qcleb_iff _ _)). exact (em_slack f).
Qed.

(** Record extensionality without a proof-irrelevance axiom. *)

Lemma EvidenceMorphism_eq :
  forall (c d : EvidenceObject) (f g : EvidenceMorphism c d),
    em_q f = em_q g -> em_spine f = em_spine g -> f = g.
Proof.
  intros c d [qf Wf pf] [qg Wg pg] Hq HW. simpl in Hq, HW.
  subst qg. subst Wg. f_equal. apply qcleb_proof_irrelevant.
Qed.

(** Identity is the accepted pair (0, empty spine). *)

Definition id_evidence (c : EvidenceObject) : EvidenceMorphism c c.
Proof.
  refine {| em_q := 0; em_spine := sp_nil (eo_name c); em_slack := _ |}.
  apply (proj2 (qcleb_iff _ _)). simpl. apply Qcle_refl.
Defined.

(** Composition adds announced bounds and concatenates normalized spines. *)

Definition comp_evidence {c d e : EvidenceObject}
    (f : EvidenceMorphism c d) (g : EvidenceMorphism d e)
  : EvidenceMorphism c e.
Proof.
  refine {| em_q := em_q f + em_q g;
            em_spine := sp_app (em_spine f) (em_spine g);
            em_slack := _ |}.
  apply (proj2 (qcleb_iff _ _)).
  rewrite sp_bound_app.
  apply Qcplus_le_compat.
  - apply em_spine_le_bound.
  - apply em_spine_le_bound.
Defined.

(** ** Def 3.1 category laws — STRICT, as Leibniz equalities. *)

Theorem comp_evidence_id_l :
  forall (c d : EvidenceObject) (f : EvidenceMorphism c d),
    comp_evidence (id_evidence c) f = f.
Proof.
  intros c d f. apply EvidenceMorphism_eq.
  - simpl. apply qc_add_0_l.
  - simpl. apply sp_app_nil_l.
Qed.

Theorem comp_evidence_id_r :
  forall (c d : EvidenceObject) (f : EvidenceMorphism c d),
    comp_evidence f (id_evidence d) = f.
Proof.
  intros c d f. apply EvidenceMorphism_eq.
  - simpl. apply qc_add_0_r.
  - simpl. apply sp_app_nil_r.
Qed.

Theorem comp_evidence_assoc :
  forall (c d e h : EvidenceObject)
         (f : EvidenceMorphism c d) (g : EvidenceMorphism d e)
         (k : EvidenceMorphism e h),
    comp_evidence (comp_evidence f g) k
    = comp_evidence f (comp_evidence g k).
Proof.
  intros c d e h f g k. apply EvidenceMorphism_eq.
  - simpl. symmetry. apply qc_add_assoc.
  - simpl. apply sp_app_assoc.
Qed.

(** ** Announced-bound behaviour, also strict. *)

Lemma id_evidence_bound : forall c, em_bound (id_evidence c) = 0.
Proof. intro c. reflexivity. Qed.

Lemma comp_evidence_bound :
  forall (c d e : EvidenceObject)
         (f : EvidenceMorphism c d) (g : EvidenceMorphism d e),
    em_bound (comp_evidence f g) = em_bound f + em_bound g.
Proof. intros. reflexivity. Qed.

(** ** Soundness of a morphism at its announced q. *)

Theorem em_sound :
  forall (c d : EvidenceObject) (f : EvidenceMorphism c d),
    distF P (deltaF P (eo_name c)) (deltaF P (eo_name d))
    <= Qc2R (em_bound f).
Proof.
  intros c d f.
  eapply Rle_trans.
  - apply spine_sound.
  - apply Qc2R_le. apply em_spine_le_bound.
Qed.

(** Every morphism certifies its endpoints at its announced bound. *)

Theorem em_certifies :
  forall (c d : EvidenceObject) (f : EvidenceMorphism c d),
    certified_dist P (eo_name c) (eo_name d) (em_bound f).
Proof.
  intros c d f. exists (em_spine f). apply em_spine_le_bound.
Qed.

End WithPresentation.

Arguments EvidenceClosure {_}.
Arguments ec_sym {_} _ {_ _ _} _.
Arguments ec_weaken {_} _ {_ _ _ _} _ _.
Arguments ec_mixed {_} _ {_ _ _ _ _ _} _ _.
Arguments CertSystem {_} _.
Arguments cs_run {_ _} _ _.
Arguments cs_bound_lt {_ _} _ _ _.
Arguments cs_accept {_ _} _ _ _.
Arguments EvidenceObject _.
Arguments eo_name {_} _.
Arguments eo_system {_} _.
Arguments EvidenceMorphism {_} _ _.
Arguments em_q {_ _ _} _.
Arguments em_spine {_ _ _} _.
Arguments em_slack {_ _ _} _.
Arguments em_bound {_ _ _} _.
Arguments id_evidence {_} _.
Arguments comp_evidence {_ _ _ _} _ _.

(** ** Correspondence with v3

      Paper definition:
        Definition 2.3 (Certificate and certificate system).
      Rocq definition:
        V3_Evidence.CertSystem.
      Correspondence: EXACT. [cs_run] is the uniform procedure,
      [cs_bound_lt] enforces ε̄ < ε, [cs_accept] is AppCheck
      acceptance.

      Paper definition:
        Definition 3.1 (Proof-relevant evidence category Cert_ev(F)).
      Rocq definitions:
        V3_Evidence.EvidenceObject, EvidenceMorphism,
        id_evidence, comp_evidence.
      Rocq theorems:
        comp_evidence_id_l, comp_evidence_id_r, comp_evidence_assoc.
      Correspondence: DEFINITION-EXACT candidate pending CI/audit.
      A morphism now literally retains the paper's accepted pair
      [(q,W)]: [em_q] is first-class proof-relevant data and
      [em_spine] is the normalized witness, with [em_slack] certifying
      that its intrinsic bound is at most q.  Thus slackened witnesses
      are not silently identified with their principal bound.  The
      category laws are literal Leibniz equalities and use no
      proof-irrelevance axiom.

      Residual assumptions, deliberately visible: [EvidenceClosure]
      still posits SYMMETRY and WEAKENING of certified distance. Both
      are rules of the paper's evidence language; neither is realized
      by the current normal form. Reflexivity and the triangle rule are
      NOT assumed — they are theorems
      ([certified_dist_refl], [certified_dist_trans]). *)

End V3_Evidence.
