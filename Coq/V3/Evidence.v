(** * Evidence.v — v3 proof-relevant evidence category (§2–§3)

    Paper reference: Ballús Santacana, "Universal Gluing and Contextual
    Choice: Certificate-Carrying Approximation, Functorial Evidence, and
    Effective Descent", arXiv:2506.22693 v3, Definitions 2.3 and 3.1.

    STATUS: IN-PROGRESS (see docs/FORMALIZATION_STATUS.md).

    A morphism of the paper is an accepted pair [(q,W)] with
    [q in Q_{>=0}]. The Rocq representation keeps both pieces as
    proof-relevant data: [em_q] is the announced canonical-rational bound,
    [em_spine] is a normalized endpoint-indexed witness, [em_nonneg]
    checks the manuscript's side condition [0 <= q], and [em_slack]
    checks that the intrinsic spine bound is at most the announced one.

    Both side conditions are Boolean equalities. Consequently equality
    of their proof components follows from decidable UIP for booleans;
    strict category laws remain genuine Leibniz equalities without a
    proof-irrelevance axiom.

    Evidence-language closure is computational. Symmetry returns an
    actual normalized spine; the mixed rule returns an actual AppCheck
    witness; and AppCheck weakening explicitly recompiles evidence from
    a certified bound [q] to any larger announced bound [q']. Distance
    weakening itself remains derivable by retaining the same normalized
    spine and increasing the announced morphism bound. *)

From Stdlib Require Import List Reals QArith Qcanon Bool Eqdep_dec Lra Lia.
From UELAT.V3 Require Import EvidenceSyntax Presentation.
Import ListNotations.
Local Open Scope Qc_scope.

Module V3_Evidence.

Import V3_EvidenceSyntax.
Import V3_Presentation.

Section WithPresentation.
Variable P : Presentation.

(** ** Computational closure operations from Def. 2.1's evidence language. *)
Record EvidenceClosure : Type := {
  ec_sym_spine :
    forall (nu mu : NameF P),
      PSpine P nu mu -> PSpine P mu nu;
  ec_sym_bound :
    forall (nu mu : NameF P) (W : PSpine P nu mu),
      sp_bound (ec_sym_spine nu mu W) = sp_bound W;

  ec_mixed_witness :
    forall (nu mu : NameF P) (p : CodeF P) (q r : Qc),
      PSpine P nu mu -> list bool -> list bool;
  ec_mixed_ok :
    forall (nu mu : NameF P) (p : CodeF P) (q r : Qc)
           (W : PSpine P nu mu) (V : list bool),
      (sp_bound W <= q)%Qc ->
      AppCheck P mu p r V = true ->
      AppCheck P nu p (q + r)
        (ec_mixed_witness nu mu p q r W V) = true;

  ec_app_weaken_witness :
    forall (nu : NameF P) (p : CodeF P) (q q' : Qc),
      list bool -> list bool;
  ec_app_weaken_ok :
    forall (nu : NameF P) (p : CodeF P) (q q' : Qc) (V : list bool),
      (q <= q')%Qc ->
      AppCheck P nu p q V = true ->
      AppCheck P nu p q'
        (ec_app_weaken_witness nu p q q' V) = true
}.

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

Record EvidenceObject : Type := {
  eo_name   : NameF P;
  eo_system : CertSystem eo_name
}.

Definition qcleb (a b : Qc) : bool := Qle_bool a b.

Lemma qcleb_iff :
  forall a b : Qc, qcleb a b = true <-> (a <= b)%Qc.
Proof.
  intros a b. unfold qcleb, Qcle. apply Qle_bool_iff.
Qed.

Lemma qcleb_proof_irrelevant :
  forall (a b : Qc) (p q : qcleb a b = true), p = q.
Proof.
  intros a b p q. apply checker_proof_irrelevant.
Qed.

(** ** Def. 3.1 — genuine accepted [(q,W)] with q nonnegative. *)
Record EvidenceMorphism (c d : EvidenceObject) : Type := {
  em_q       : Qc;
  em_spine   : PSpine P (eo_name c) (eo_name d);
  em_nonneg  : qcleb 0 em_q = true;
  em_slack   : qcleb (sp_bound em_spine) em_q = true
}.

Arguments em_q {_ _} _.
Arguments em_spine {_ _} _.
Arguments em_nonneg {_ _} _.
Arguments em_slack {_ _} _.

Definition em_bound {c d : EvidenceObject} (f : EvidenceMorphism c d) : Qc :=
  em_q f.

Lemma em_bound_nonneg :
  forall (c d : EvidenceObject) (f : EvidenceMorphism c d),
    (0 <= em_bound f)%Qc.
Proof.
  intros c d f. apply (proj1 (qcleb_iff _ _)). exact (em_nonneg f).
Qed.

Lemma em_spine_le_bound :
  forall (c d : EvidenceObject) (f : EvidenceMorphism c d),
    (sp_bound (em_spine f) <= em_bound f)%Qc.
Proof.
  intros c d f. apply (proj1 (qcleb_iff _ _)). exact (em_slack f).
Qed.

Lemma EvidenceMorphism_eq :
  forall (c d : EvidenceObject) (f g : EvidenceMorphism c d),
    em_q f = em_q g -> em_spine f = em_spine g -> f = g.
Proof.
  intros c d [qf Wf nnf sf] [qg Wg nng sg] Hq HW. simpl in Hq, HW.
  subst qg. subst Wg.
  assert (Hnn : nnf = nng) by apply qcleb_proof_irrelevant.
  subst nng. f_equal. apply qcleb_proof_irrelevant.
Qed.

Definition id_evidence (c : EvidenceObject) : EvidenceMorphism c c.
Proof.
  refine {| em_q := 0;
            em_spine := sp_nil (eo_name c);
            em_nonneg := _;
            em_slack := _ |}.
  - apply (proj2 (qcleb_iff _ _)). apply Qcle_refl.
  - apply (proj2 (qcleb_iff _ _)). simpl. apply Qcle_refl.
Defined.

Definition comp_evidence {c d e : EvidenceObject}
    (f : EvidenceMorphism c d) (g : EvidenceMorphism d e)
  : EvidenceMorphism c e.
Proof.
  refine {| em_q := em_q f + em_q g;
            em_spine := sp_app (em_spine f) (em_spine g);
            em_nonneg := _;
            em_slack := _ |}.
  - apply (proj2 (qcleb_iff _ _)).
    rewrite <- (qc_add_0_l 0).
    apply Qcplus_le_compat; apply em_bound_nonneg.
  - apply (proj2 (qcleb_iff _ _)).
    rewrite sp_bound_app.
    apply Qcplus_le_compat.
    + apply em_spine_le_bound.
    + apply em_spine_le_bound.
Defined.

Definition weaken_evidence {c d : EvidenceObject}
    (f : EvidenceMorphism c d) (q' : Qc)
    (Hle : (em_bound f <= q')%Qc) : EvidenceMorphism c d.
Proof.
  refine {| em_q := q'; em_spine := em_spine f;
            em_nonneg := _; em_slack := _ |}.
  - apply (proj2 (qcleb_iff _ _)).
    eapply Qcle_trans; [apply em_bound_nonneg | exact Hle].
  - apply (proj2 (qcleb_iff _ _)).
    eapply Qcle_trans; [apply em_spine_le_bound | exact Hle].
Defined.

Definition sym_evidence (EC : EvidenceClosure)
    {c d : EvidenceObject} (f : EvidenceMorphism c d)
  : EvidenceMorphism d c.
Proof.
  refine {| em_q := em_bound f;
            em_spine := ec_sym_spine EC (eo_name c) (eo_name d) (em_spine f);
            em_nonneg := _;
            em_slack := _ |}.
  - exact (em_nonneg f).
  - apply (proj2 (qcleb_iff _ _)).
    rewrite ec_sym_bound. apply em_spine_le_bound.
Defined.

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

Lemma id_evidence_bound : forall c, em_bound (id_evidence c) = 0.
Proof. intro c. reflexivity. Qed.

Lemma comp_evidence_bound :
  forall (c d e : EvidenceObject)
         (f : EvidenceMorphism c d) (g : EvidenceMorphism d e),
    em_bound (comp_evidence f g) = em_bound f + em_bound g.
Proof. intros. reflexivity. Qed.

Theorem em_sound :
  forall (c d : EvidenceObject) (f : EvidenceMorphism c d),
    (distF P (deltaF P (eo_name c)) (deltaF P (eo_name d))
     <= Qc2R (em_bound f))%R.
Proof.
  intros c d f.
  eapply Rle_trans.
  - apply spine_sound.
  - apply Qc2R_le. apply em_spine_le_bound.
Qed.

Theorem em_certifies :
  forall (c d : EvidenceObject) (f : EvidenceMorphism c d),
    certified_dist P (eo_name c) (eo_name d) (em_bound f).
Proof.
  intros c d f. exists (em_spine f). apply em_spine_le_bound.
Qed.

Theorem ec_sym_certified (EC : EvidenceClosure) :
  forall (nu mu : NameF P) (q : Qc),
    certified_dist P nu mu q -> certified_dist P mu nu q.
Proof.
  intros nu mu q [W Hle].
  exists (ec_sym_spine EC nu mu W).
  rewrite ec_sym_bound. exact Hle.
Qed.

Theorem certified_dist_weaken :
  forall (nu mu : NameF P) (q q' : Qc),
    (q <= q')%Qc -> certified_dist P nu mu q -> certified_dist P nu mu q'.
Proof.
  intros nu mu q q' Hqq' [W HW]. exists W.
  eapply Qcle_trans; eauto.
Qed.

End WithPresentation.

Arguments EvidenceClosure {_}.
Arguments ec_sym_spine {_} _ _ _ _.
Arguments ec_sym_bound {_} _ {_ _} _.
Arguments ec_mixed_witness {_} _ _ _ _ _ _ _ _.
Arguments ec_mixed_ok {_} _ {_ _ _ _ _ _} _ _ _.
Arguments ec_app_weaken_witness {_} _ _ _ _ _ _.
Arguments ec_app_weaken_ok {_} _ {_ _ _ _ _} _ _.
Arguments CertSystem {_} _.
Arguments cs_run {_ _} _ _.
Arguments cs_bound_lt {_ _} _ _ _.
Arguments cs_accept {_ _} _ _ _.
Arguments EvidenceObject _.
Arguments eo_name {_} _.
Arguments eo_system {_} _.
Arguments EvidenceMorphism {_} _ _.
Arguments em_bound {_ _ _} _.
Arguments id_evidence {_} _.
Arguments comp_evidence {_ _ _ _} _ _.

(** ** Correspondence with v3

      Definition 2.3 (Certificate system) is represented by
      [CertSystem]: [cs_run] is the uniform procedure,
      [cs_bound_lt] enforces a nonnegative announced error strictly below
      the requested tolerance, and [cs_accept] is AppCheck acceptance.

      Definition 2.1's evidence-language closure is represented here by
      computational constructors for symmetry, mixed/triangle use, and
      AppCheck weakening. Distance weakening is derivable because a
      distance morphism stores its announced bound separately from its
      normalized proof spine.

      Definition 3.1 (proof-relevant evidence category) is represented by
      [EvidenceObject] and [EvidenceMorphism]. A morphism literally
      retains the paper's pair [(q,W)] with the manuscript's
      [q in Q_{>=0}] side condition ([em_nonneg]) and an accepted
      normalized witness whose intrinsic bound is at most q ([em_slack]).
      Identity and composition retain their announced bounds exactly;
      the three category laws above are Leibniz equalities and use no
      proof-irrelevance axiom.

      Status remains a candidate for DEFINITION-EXACT until the exact
      branch compiles, coqchk passes, and the assumptions audit is
      committed. *)

End V3_Evidence.
