(** * Evidence.v — v3 proof-relevant evidence category (§3, Def 3.1)

    Paper reference: Ballús Santacana, "Universal Gluing and Contextual Choice: Certificate-Carrying Approximation, Functorial Evidence, and Effective Descent", arXiv:2506.22693 v3, Definitions 2.3, 3.1,
    and §2 evidence-language closure rules.

    STATUS: IN-PROGRESS (see docs/FORMALIZATION_STATUS.md).

    This module builds three logically distinct things on top of the
    Def 2.1 presentation record in [V3.Presentation]:

    1. [EvidenceClosure P] — the §2 closure rules on the evidence
       language (reflexivity at bound 0, weakening, symmetry,
       triangle). These are HYPOTHESES the paper imposes on the
       evidence language, not consequences of Def 2.1 alone. A
       concrete presentation must exhibit an [EvidenceClosure]
       witness.

    2. [CertSystem P nu] — Def 2.3, certificate system: a uniform
       procedure over the named point [nu] that returns a certificate
       (p, ε̄, V) for every positive rational tolerance.

    3. [EvidenceObject P] and [EvidenceMorphism P c d] — Def 3.1,
       objects and morphisms of the proof-relevant evidence category
       [Cert_ev(F)]. Identity and composition are constructed using
       the [EvidenceClosure] witness.

    What this file DOES claim: constructor infrastructure for the v3
    evidence category, with the closure rules made explicit rather
    than hidden.

    What this file does NOT yet claim:

      * Category laws (identity, associativity) on the nose. The
        paper obtains these from "the normalized witness convention in
        Definition 2.1" — a structural proof-tree normal form we have
        not yet made explicit here. Until we do, [id_evidence] and
        [comp_evidence] are constructors, not the objects of a proved
        [Category] instance.
      * The Lawvere metric [d_Cert] of Def 3.2 — that requires an
        infimum over ℚ_{≥0} which is a separate design decision (see
        [V3/MetricReflection.v], planned).
      * The soundness Prop 3.3 (‖U_F c − U_F d‖ ≤ d_Cert(c,d)) — needs
        d_Cert first.

    Correspondence recorded in docs/FORMALIZATION_STATUS.md rows
    "Def 3.1 Proof-relevant evidence category" (IN-PROGRESS). *)

From Stdlib Require Import Reals QArith Qcanon Lra Lia.
From UELAT.V3 Require Import Presentation.
Local Open Scope Q_scope.

Module V3_Evidence.

Import V3_Presentation.

Section WithPresentation.
Variable P : Presentation.

(** ** §2 evidence-language closure rules — as a witness record.

    The paper states (page 5, after Definition 2.1):
    "We require the evidence language to be closed under the standard
    finite norm rules: reflexivity at bound zero, weakening of a
    rational bound, symmetry, the triangle inequality, finite sums
    where declared, and application of a stored Lipschitz estimate."

    Here we expose reflexivity/weakening/symmetry/triangle for
    [DistCheck]. Finite-sum and stored-Lipschitz rules will be added
    when a downstream module (e.g. [V3/RealizableMap.v]) needs them,
    to keep this record minimal for what §3 already uses. *)

Record EvidenceClosure : Type := {
  (* Constructors returning the concrete proof-tree witness. *)
  ec_refl_witness    : NameF P -> list bool;
  ec_weaken_witness  : NameF P -> NameF P -> Q -> Q -> list bool -> list bool;
  ec_sym_witness     : NameF P -> NameF P -> Q -> list bool -> list bool;
  ec_triangle_witness :
    NameF P -> NameF P -> NameF P -> Q -> Q -> list bool -> list bool -> list bool;

  (* Their acceptance conditions. *)
  ec_refl_ok :
    forall nu, DistCheck P nu nu 0 (ec_refl_witness nu) = true;

  ec_weaken_ok :
    forall nu mu q q' W,
      (q <= q')%Q ->
      DistCheck P nu mu q W = true ->
      DistCheck P nu mu q' (ec_weaken_witness nu mu q q' W) = true;

  ec_sym_ok :
    forall nu mu q W,
      DistCheck P nu mu q W = true ->
      DistCheck P mu nu q (ec_sym_witness nu mu q W) = true;

  ec_triangle_ok :
    forall nu mu xi q1 q2 W1 W2,
      DistCheck P nu mu q1 W1 = true ->
      DistCheck P mu xi q2 W2 = true ->
      DistCheck P nu xi (q1 + q2)
                (ec_triangle_witness nu mu xi q1 q2 W1 W2) = true
}.

Variable EC : EvidenceClosure.

(** ** Def 2.3 — Certificate system over a named point.

    A certificate system c over ν is a uniform terminating procedure
    which, on input ε ∈ ℚ_{>0}, returns a certificate (p, ε̄, V) for
    (ν, ε) — i.e. ε̄ < ε and [AppCheck ν p ε̄ V] accepts.

    We package the procedure as [cs_run], the strict bound as
    [cs_bound_lt], and acceptance as [cs_accept]. Product-return
    keeps the procedure a first-class value so downstream lemmas can
    reason about the specific p and ε̄ it produces. *)

Record CertSystem (nu : NameF P) : Type := {
  cs_run     : Q -> CodeF P * Q * list bool;
  cs_bound_lt :
    forall eps : Q, (0 < eps)%Q ->
      let '(_p, ebar, _V) := cs_run eps in (0 <= ebar < eps)%Q;
  cs_accept :
    forall eps : Q, (0 < eps)%Q ->
      let '(p, ebar, V) := cs_run eps in
      AppCheck P nu p ebar V = true
}.

(* Section-local Arguments removed — they were being clobbered when the
   section variable P was generalized on End. Full Arguments block
   sits after End WithPresentation, below. *)

(** ** Def 3.1 — Objects and morphisms of Cert_ev(F).

    An object is a pair (ν, c) with ν a name and c a certificate
    system over ν. We package these in [EvidenceObject].

    A morphism (ν, c) → (μ, d) is a pair (q, W) with q ∈ ℚ_{≥0} and
    [DistCheck ν μ q W = true]. The certificate systems of the
    endpoints do not appear in the morphism data itself — they are
    part of the object identity. *)

Record EvidenceObject : Type := {
  eo_name   : NameF P;
  eo_system : CertSystem eo_name
}.

Record EvidenceMorphism (c d : EvidenceObject) : Type := {
  em_bound        : Q;
  em_bound_nonneg : (0 <= em_bound)%Q;
  em_witness      : list bool;
  em_ok           : DistCheck P (eo_name c) (eo_name d)
                              em_bound em_witness = true
}.

Arguments em_bound       [c d] _.
Arguments em_bound_nonneg [c d] _.
Arguments em_witness     [c d] _.
Arguments em_ok          [c d] _.

(** ** Identity morphism — reflexivity at bound 0.

    Uses [ec_refl_witness] / [ec_refl_ok] from the closure record. *)

Definition id_evidence (c : EvidenceObject) : EvidenceMorphism c c :=
  {| em_bound        := 0
   ; em_bound_nonneg := Qle_refl 0
   ; em_witness      := ec_refl_witness EC (eo_name c)
   ; em_ok           := ec_refl_ok EC (eo_name c) |}.

(** ** Composition — triangle rule.

    Concatenates evidence witnesses via [ec_triangle_witness] and adds
    the two rational bounds. Nonnegativity of the sum follows from
    the two summands being nonneg. *)

Lemma Qplus_nonneg : forall a b : Q, (0 <= a)%Q -> (0 <= b)%Q -> (0 <= a + b)%Q.
Proof.
  intros a b Ha Hb.
  apply (Qle_trans _ (0 + 0)); [rewrite Qplus_0_l; apply Qle_refl|].
  apply Qplus_le_compat; assumption.
Qed.

Definition comp_evidence
  {c d e : EvidenceObject}
  (f : EvidenceMorphism c d) (g : EvidenceMorphism d e)
  : EvidenceMorphism c e :=
  {| em_bound := em_bound f + em_bound g
   ; em_bound_nonneg :=
       Qplus_nonneg _ _ (em_bound_nonneg f) (em_bound_nonneg g)
   ; em_witness :=
       ec_triangle_witness EC (eo_name c) (eo_name d) (eo_name e)
                              (em_bound f) (em_bound g)
                              (em_witness f) (em_witness g)
   ; em_ok :=
       ec_triangle_ok EC (eo_name c) (eo_name d) (eo_name e)
                         (em_bound f) (em_bound g)
                         (em_witness f) (em_witness g)
                         (em_ok f) (em_ok g) |}.

(** ** Bound behaviour under identity and composition.

    These small lemmas are the arithmetic content of the "identity
    and associativity laws" of the paper's category, isolated from
    the proof-tree normalization question. They ARE provable now:

      - [id_evidence] contributes 0 to the bound sum,
      - [comp_evidence] adds bounds,

    so the Lawvere metric can be computed from these lemmas alone even
    before the on-the-nose category laws are settled. *)

(** The identity morphism's bound is literally 0 (Leibniz), from the
    id_evidence definition; the other three bound identities hold up
    to Qeq only, since Qplus/Qmult on Q is not Leibniz-associative or
    Leibniz-unital. Stating them as Qeq is the correct shape and lets
    downstream metric arguments use the setoid rewriting Q provides. *)

Lemma id_evidence_bound : forall c, em_bound (id_evidence c) = 0.
Proof. intro c. reflexivity. Qed.

Lemma comp_evidence_bound :
  forall c d e (f : EvidenceMorphism c d) (g : EvidenceMorphism d e),
    em_bound (comp_evidence f g) = em_bound f + em_bound g.
Proof. intros; reflexivity. Qed.

Lemma comp_evidence_id_right_bound :
  forall c d (f : EvidenceMorphism c d),
    (em_bound (comp_evidence f (id_evidence d)) == em_bound f)%Q.
Proof.
  intros c d f. cbn. apply Qplus_0_r.
Qed.

Lemma comp_evidence_id_left_bound :
  forall c d (f : EvidenceMorphism c d),
    (em_bound (comp_evidence (id_evidence c) f) == em_bound f)%Q.
Proof.
  intros c d f. cbn. apply Qplus_0_l.
Qed.

Lemma comp_evidence_assoc_bound :
  forall c d e h
         (f : EvidenceMorphism c d)
         (g : EvidenceMorphism d e)
         (k : EvidenceMorphism e h),
    (em_bound (comp_evidence (comp_evidence f g) k)
     == em_bound (comp_evidence f (comp_evidence g k)))%Q.
Proof.
  intros. cbn. symmetry. apply Qplus_assoc.
Qed.

End WithPresentation.

(** ** Cross-section implicit-arguments plumbing.

    Every definition inside [WithPresentation] that uses [P] as a
    Section variable gets [P] generalized as an explicit parameter on
    section close. When a downstream module (e.g.
    [V3/EffectiveCompleteness.v]) writes
    [ec_sym_witness EC nu ...] with [EC : EvidenceClosure P], Rocq
    otherwise interprets [EC] as the first explicit argument [P] and
    fails ("The term EC has type EvidenceClosure P while it is
    expected to have type Presentation"). Making [P] implicit on
    every projection and section-generalized definition fixes this. *)

(* Positional (`_`) rather than named — `Arguments f x y` renames the
   binder to `x`, `y`, and the record projection's auto-generated
   binder names don't match what we'd type. `_` skips the rename. *)

Arguments ec_refl_witness    {_} _ _.
Arguments ec_weaken_witness  {_} _ _ _ _ _ _.
Arguments ec_sym_witness     {_} _ _ _ _ _.
Arguments ec_triangle_witness {_} _ _ _ _ _ _ _ _.
Arguments ec_refl_ok         {_} _ _.
Arguments ec_weaken_ok       {_} _ _ _ _ _ _ _.
Arguments ec_sym_ok          {_} _ _ _ _ _ _.
Arguments ec_triangle_ok     {_} _ _ _ _ _ _ _ _ _.

Arguments cs_run     {_ _} _ _.
Arguments cs_bound_lt {_ _} _ _ _.
Arguments cs_accept  {_ _} _ _ _.

Arguments eo_name {_} _.
Arguments eo_system {_} _.

Arguments em_bound {_ _ _} _.
Arguments em_bound_nonneg {_ _ _} _.
Arguments em_witness {_ _ _} _.
Arguments em_ok {_ _ _} _.

Arguments id_evidence {_} _ _.
Arguments comp_evidence {_} _ {_ _ _} _ _.

(** ** What this file DOES NOT contain

    - Def 3.2 [d_Cert] Lawvere metric — needs infimum over ℚ_{≥0}.
      Planned in [V3/MetricReflection.v].
    - Prop 3.3 soundness of the evidence metric — depends on d_Cert.
    - The on-the-nose category laws (associativity, identity as
      literal equalities in [EvidenceMorphism]). The paper obtains
      these from a "normalized witness convention"; we would need to
      define a proof-tree normal form on evidence witnesses (or work
      up to a witness-equivalence relation) to state them. The
      arithmetic content (bounds) IS proved above and is enough for
      metric-level statements.
    - The §2 finite-sum and stored-Lipschitz closure rules — will be
      added to [EvidenceClosure] when [V3/RealizableMap.v] needs them.

    Correspondence with v3:

      Paper theorem:
        Definition 2.3 (Certificate and certificate system).
      Rocq definition:
        V3_Evidence.CertSystem.
      Correspondence: EXACT (the "certificate" itself is (p, ε̄, V)
      returned by [cs_run]; [cs_bound_lt] enforces ε̄ < ε; [cs_accept]
      is the required AppCheck acceptance).

      Paper theorem:
        Definition 3.1 (Proof-relevant evidence category Cert_ev(F)).
      Rocq definitions:
        V3_Evidence.EvidenceObject, V3_Evidence.EvidenceMorphism,
        V3_Evidence.id_evidence, V3_Evidence.comp_evidence.
      Correspondence: RESTRICTED — objects and morphisms match the
      paper exactly; identity and composition constructors match; on-
      the-nose category laws pending proof-tree normalization. *)

End V3_Evidence.
