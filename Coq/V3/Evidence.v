(** * Evidence.v — v3 proof-relevant evidence category (§2–§3)

    Paper reference: Ballús Santacana, "Universal Gluing and Contextual
    Choice: Certificate-Carrying Approximation, Functorial Evidence, and
    Effective Descent", arXiv:2506.22693 v3, Definitions 2.3 and 3.1.

    STATUS: IN-PROGRESS (see docs/FORMALIZATION_STATUS.md).

    ** What changed, and why

    A morphism used to bundle a rational bound, an opaque [list bool]
    witness, and a checker-acceptance proof. The category laws could
    then only be stated up to an unspecified equivalence, because
    nothing related two opaque witnesses. The module said so and
    deferred them.

    A morphism is now literally a NORMALIZED SPINE
    ([V3_EvidenceSyntax.Spine]) between the two objects' names. Its
    endpoints live in the type, so no endpoint proof is stored; its
    bound is derived by [sp_bound]; and identity and composition are
    the empty spine and concatenation. The Def 3.1 category laws are
    therefore the strict spine laws, and are proved here as LEIBNIZ
    equalities — no setoid, no quotient, no axiom.

    ** What the EvidenceClosure record is still for

    Reflexivity and the triangle rule are now theorems (empty spine,
    concatenation), so they are gone from the closure record.
    SYMMETRY and WEAKENING remain abstract witness constructors: they
    are genuine rules of the paper's evidence language that the current
    normal form does not yet realize. Keeping them as an explicit,
    named record makes the residual assumption visible instead of
    burying it. *)

From Stdlib Require Import List QArith Qcanon Bool Lra Lia.
From UELAT.V3 Require Import EvidenceSyntax Presentation.
Import ListNotations.
Local Open Scope Qc_scope.

Module V3_Evidence.

Import V3_EvidenceSyntax.
Import V3_Presentation.

Section WithPresentation.
Variable P : Presentation.

(** ** Residual closure rules.

    Only the rules the normalized spine does not yet realize. A
    concrete presentation must exhibit these; reflexivity and triangle
    are NOT here because they are proved (see [Presentation.v]). *)

Record EvidenceClosure : Type := {
  (* Symmetry: reverse a certified distance at the same bound. *)
  ec_sym :
    forall (nu mu : NameF P) (q : Qc),
      certified_dist P nu mu q -> certified_dist P mu nu q;
  (* Weakening: raise an announced bound. *)
  ec_weaken :
    forall (nu mu : NameF P) (q q' : Qc),
      (q <= q')%Qc ->
      certified_dist P nu mu q -> certified_dist P nu mu q';
  (* The MIXED rule of §2: "a certified distance from one name to
     another may be composed with an approximation certificate for the
     second name to obtain an approximation certificate for the first
     name, with the two rational bounds added." This is a stated
     closure requirement of Def 2.1's evidence language, not an extra
     hypothesis — and it is precisely what lets approximation-evidence
     transport be DERIVED in Thm 5.2 instead of assumed as a fifth
     clause of Def 5.1. *)
  ec_mixed :
    forall (nu mu : NameF P) (p : CodeF P) (q r : Qc) (V : list bool),
      certified_dist P nu mu q ->
      AppCheck P mu p r V = true ->
      exists V', AppCheck P nu p (q + r) V' = true
}.

(** ** Def 2.3 — Certificate system over a named point.

    A uniform terminating procedure returning, for each positive
    rational tolerance, a certificate [(p, ε̄, V)] with [ε̄ < ε] that
    [AppCheck] accepts. *)

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

(** ** Def 3.1 — Objects and morphisms of Cert_ev(F).

    An object is a named point together with a certificate system over
    it. A morphism is a normalized spine between the objects' names;
    its rational bound is [sp_bound]. *)

Record EvidenceObject : Type := {
  eo_name   : NameF P;
  eo_system : CertSystem eo_name
}.

Definition EvidenceMorphism (c d : EvidenceObject) : Type :=
  PSpine P (eo_name c) (eo_name d).

Definition em_bound {c d : EvidenceObject} (f : EvidenceMorphism c d) : Qc :=
  sp_bound f.

(** Identity is the empty spine; composition is concatenation. *)

Definition id_evidence (c : EvidenceObject) : EvidenceMorphism c c :=
  sp_nil (eo_name c).

Definition comp_evidence {c d e : EvidenceObject}
    (f : EvidenceMorphism c d) (g : EvidenceMorphism d e)
  : EvidenceMorphism c e :=
  sp_app f g.

(** ** Def 3.1 category laws — STRICT, as Leibniz equalities.

    These are exactly the paper's "strictly unital and associative"
    claim for the normalized witness composition, now stated at the
    level of evidence morphisms rather than only of raw spines. *)

Theorem comp_evidence_id_l :
  forall (c d : EvidenceObject) (f : EvidenceMorphism c d),
    comp_evidence (id_evidence c) f = f.
Proof. intros c d f. apply sp_app_nil_l. Qed.

Theorem comp_evidence_id_r :
  forall (c d : EvidenceObject) (f : EvidenceMorphism c d),
    comp_evidence f (id_evidence d) = f.
Proof. intros c d f. apply sp_app_nil_r. Qed.

Theorem comp_evidence_assoc :
  forall (c d e h : EvidenceObject)
         (f : EvidenceMorphism c d) (g : EvidenceMorphism d e)
         (k : EvidenceMorphism e h),
    comp_evidence (comp_evidence f g) k
    = comp_evidence f (comp_evidence g k).
Proof. intros. apply sp_app_assoc. Qed.

(** ** Bound behaviour, also strict. *)

Lemma id_evidence_bound : forall c, em_bound (id_evidence c) = 0.
Proof. intro c. reflexivity. Qed.

Lemma comp_evidence_bound :
  forall (c d e : EvidenceObject)
         (f : EvidenceMorphism c d) (g : EvidenceMorphism d e),
    em_bound (comp_evidence f g) = em_bound f + em_bound g.
Proof. intros. apply sp_bound_app. Qed.

(** ** Soundness of a morphism: the bridge, at the level of Def 3.1. *)

Theorem em_sound :
  forall (c d : EvidenceObject) (f : EvidenceMorphism c d),
    distF P (deltaF P (eo_name c)) (deltaF P (eo_name d))
    <= Qc2R (em_bound f).
Proof. intros c d f. apply spine_sound. Qed.

(** Every morphism certifies its endpoints at its own bound. *)

Theorem em_certifies :
  forall (c d : EvidenceObject) (f : EvidenceMorphism c d),
    certified_dist P (eo_name c) (eo_name d) (em_bound f).
Proof. intros c d f. exists f. apply Qcle_refl. Qed.

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
        comp_evidence_id_l, comp_evidence_id_r, comp_evidence_assoc
        — the category laws, as LEIBNIZ equalities.
      Correspondence: DEFINITION-EXACT for objects, morphisms,
      identity and composition, WITH the strict laws proved. This
      discharges the deferral recorded in the previous revision of
      this module.

      Residual assumptions, deliberately visible: [EvidenceClosure]
      still posits SYMMETRY and WEAKENING of certified distance. Both
      are rules of the paper's evidence language; neither is realized
      by the current normal form. They are stated over
      [certified_dist] (a Prop) rather than over spines, so a
      presentation may discharge them semantically. Reflexivity and
      the triangle rule are NOT assumed — they are theorems
      ([certified_dist_refl], [certified_dist_trans]). *)

End V3_Evidence.
