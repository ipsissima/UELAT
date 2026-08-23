(** * Presentation.v — v3 approximation-presentation interface (§2)

    Paper reference: Ballús Santacana, "Universal Gluing and Contextual
    Choice: Certificate-Carrying Approximation, Functorial Evidence, and
    Effective Descent", arXiv:2506.22693 v3, Definition 2.1.

    STATUS: IN-PROGRESS (see docs/FORMALIZATION_STATUS.md).

    ** What changed, and why

    Earlier this record carried a whole-claim distance checker

      DistCheck : NameF -> NameF -> Q -> list bool -> bool

    together with an ASSUMED soundness field. That conflated two
    different things: the primitive act of verifying one elementary
    distance witness, and the structural act of composing verified
    steps along a triangle spine. The paper separates them — §2 lists
    the structural rules (reflexivity, weakening, symmetry, triangle,
    finite sums, stored Lipschitz) as closure properties OF the
    evidence language, not as primitive checks.

    So the presentation now supplies only the PRIMITIVE leaf checker

      DistLeaf : NameF -> NameF -> Qc -> list bool -> bool

    with its soundness. Composite distance certification is then
    [V3_EvidenceSyntax.Spine], and whole-spine soundness is DERIVED
    here as [spine_sound] — the "checker-realization bridge". The
    triangle rule is consequently a theorem about [distF], proved from
    [distF_triangle], rather than an assumed closure constructor.

    Bounds moved from [Q] to [Qc] so that bound arithmetic is Leibniz;
    see the header of [V3_EvidenceSyntax] for why that matters to the
    strict laws Def 5.1 requires. *)

From Stdlib Require Import Reals QArith Qreals Qcanon Lra Lia.
From UELAT.V3 Require Import EvidenceSyntax.
Local Open Scope R_scope.

Module V3_Presentation.

Import V3_EvidenceSyntax.

(** ** Canonical rationals as reals.

    [Qc] is [Q] restricted to canonical form, so its underlying
    rational is recovered by the [this] projection. *)

Definition Qc2R (q : Qc) : R := Q2R (this q).

(** [Qcplus] is [Q2Qc] of the underlying sum, so the projection of a
    [Qc] sum is [Qred] of the [Q] sum — equal to it under [Qeq], hence
    equal after [Q2R]. [apply Qred_correct] unifies up to delta, so no
    [simpl] is needed and the proof does not depend on the exact shape
    [simpl] would produce. *)

Lemma Qc2R_plus : forall p q : Qc, Qc2R (p + q)%Qc = Qc2R p + Qc2R q.
Proof.
  intros p q. unfold Qc2R. rewrite <- Q2R_plus.
  apply Qeq_eqR. apply Qred_correct.
Qed.

(** Derived from [Qc2R_plus] rather than from a [Q2R]-level zero lemma.
    An earlier revision used [Q2R_0], which does not exist in this
    stdlib; deriving it here removes the dependency on that name
    entirely. *)

Lemma Qc2R_0 : Qc2R 0 = 0.
Proof.
  assert (H : Qc2R (0 + 0)%Qc = Qc2R 0 + Qc2R 0) by apply Qc2R_plus.
  rewrite qc_add_0_l in H. lra.
Qed.

Lemma Qc2R_le : forall p q : Qc, (p <= q)%Qc -> Qc2R p <= Qc2R q.
Proof. intros p q H. unfold Qc2R. apply Qle_Rle. exact H. Qed.

(** ** The presentation record.

    The ambient space stays abstract, represented by a carrier [F] and
    an analytic distance [distF] obeying the pseudo-metric laws — the
    structure the paper's checker interface actually uses. A concrete
    presentation over a genuine normed space takes
    [distF a b := ‖a − b‖]. *)

Record Presentation : Type := {
  (* --- carriers --- *)
  CodeF   : Type;
  NameF   : Type;
  F       : Type;
  distF   : F -> F -> R;
  (* --- pseudo-metric laws --- *)
  distF_nonneg   : forall a b : F, 0 <= distF a b;
  distF_self0    : forall a : F, distF a a = 0;
  distF_sym      : forall a b : F, distF a b = distF b a;
  distF_triangle : forall a b c : F, distF a c <= distF a b + distF b c;
  (* --- decoders --- *)
  rhoF    : CodeF -> F;
  deltaF  : NameF -> F;
  iotaF   : CodeF -> NameF;
  code_size : CodeF -> nat;
  (* --- checkers: approximation, and PRIMITIVE distance leaf --- *)
  AppCheck : NameF -> CodeF -> Qc -> list bool -> bool;
  DistLeaf : NameF -> NameF -> Qc -> list bool -> bool;
  (* --- structural coherence (Def 2.1 item 3) --- *)
  canonical_name_ok : forall p : CodeF, deltaF (iotaF p) = rhoF p;
  (* --- soundness (Def 2.1 items 5 and 6, leaf form) --- *)
  AppCheck_sound :
    forall (nu : NameF) (p : CodeF) (q : Qc) (V : list bool),
      AppCheck nu p q V = true -> distF (deltaF nu) (rhoF p) <= Qc2R q;
  DistLeaf_sound :
    forall (nu mu : NameF) (q : Qc) (W : list bool),
      DistLeaf nu mu q W = true -> distF (deltaF nu) (deltaF mu) <= Qc2R q
}.

(** ** Normalized distance evidence over a presentation. *)

Definition PSpine (P : Presentation) (a b : NameF P) : Type :=
  Spine (DistLeaf P) a b.

(** ** The checker-realization bridge.

    A whole normalized spine certifies the analytic distance between
    the decoded endpoints, at its announced bound. This is the theorem
    that replaces the old assumed [DistCheck_sound]: the triangle rule
    is now PROVED from [distF_triangle] and leaf soundness, not
    postulated as a closure constructor. *)

Theorem spine_sound :
  forall (P : Presentation) (a b : NameF P) (W : PSpine P a b),
    distF P (deltaF P a) (deltaF P b) <= Qc2R (sp_bound W).
Proof.
  intros P a b W. induction W as [x | x m y s rest IH].
  - (* reflexivity: distance from a point to itself is 0 *)
    simpl. rewrite distF_self0, Qc2R_0. apply Rle_refl.
  - (* triangle step *)
    simpl. rewrite Qc2R_plus.
    eapply Rle_trans; [apply distF_triangle with (b := deltaF P m) |].
    apply Rplus_le_compat; [| exact IH].
    eapply DistLeaf_sound. exact (ps_ok s).
Qed.

(** ** Certified distance, as a relation on names.

    "The pair (nu, mu) is certified at rational bound q" means some
    normalized spine runs from nu to mu with announced bound at most q.
    Taking [<=] rather than [=] builds in weakening at the level of the
    RELATION, which is where the paper uses it; it does not assume a
    syntactic weakening constructor on spines (there is none yet — see
    the gap note in EvidenceSyntax). *)

Definition certified_dist (P : Presentation) (nu mu : NameF P) (q : Qc) : Prop :=
  exists W : PSpine P nu mu, (sp_bound W <= q)%Qc.

Theorem certified_dist_sound :
  forall (P : Presentation) (nu mu : NameF P) (q : Qc),
    certified_dist P nu mu q ->
    distF P (deltaF P nu) (deltaF P mu) <= Qc2R q.
Proof.
  intros P nu mu q [W Hle].
  eapply Rle_trans; [apply spine_sound | apply Qc2R_le; exact Hle].
Qed.

(** Reflexivity of certified distance at bound 0 — the empty spine. *)

Theorem certified_dist_refl :
  forall (P : Presentation) (nu : NameF P), certified_dist P nu nu 0.
Proof.
  intros P nu. exists (sp_nil nu). simpl. apply Qcle_refl.
Qed.

(** Transitivity, at the sum of the bounds — the triangle rule,
    realized by spine concatenation. *)

Theorem certified_dist_trans :
  forall (P : Presentation) (nu mu xi : NameF P) (q r : Qc),
    certified_dist P nu mu q ->
    certified_dist P mu xi r ->
    certified_dist P nu xi (q + r).
Proof.
  intros P nu mu xi q r [W1 H1] [W2 H2].
  exists (sp_app W1 W2). rewrite sp_bound_app.
  apply Qcplus_le_compat; assumption.
Qed.

(** ** Small helpers inside a fixed presentation. *)

Section WithPresentation.
Variable P : Presentation.

Lemma canonical_name_distF_zero : forall p,
  distF P (deltaF P (iotaF P p)) (rhoF P p) = 0.
Proof. intro p. rewrite canonical_name_ok. apply distF_self0. Qed.

Lemma AppCheck_bound_nonneg :
  forall nu p q V, AppCheck P nu p q V = true -> 0 <= Qc2R q.
Proof.
  intros nu p q V H.
  eapply Rle_trans; [apply distF_nonneg | eapply AppCheck_sound; exact H].
Qed.

End WithPresentation.

(** ** Correspondence with v3

      Paper definition:
        Definition 2.1 (Approximation presentation).
      Rocq definition:
        V3_Presentation.Presentation.
      Correspondence:
        SEMANTIC CHECKER CORE of Def 2.1 — not EXACT. The record
        captures carriers, decoders, canonical-name coherence, the
        approximation checker, and the PRIMITIVE distance-leaf checker
        with their soundness. Def 2.1 additionally requires:
          (i)  [CodeF] effectively enumerable;
          (ii) [rhoF] with dense range in the completion;
          (iii) a represented subdomain D_F with [deltaF] surjective
                onto it.
        None of (i)–(iii) is encoded yet.

        NOTE on the checker split: Def 2.1 states a whole-claim
        DistCheck. Here the presentation supplies only the leaf
        checker, and whole-claim certification is derived
        ([certified_dist], [certified_dist_sound]). This is a
        REFINEMENT rather than a weakening — any presentation with a
        leaf checker induces a whole-claim one, and the paper's
        structural rules become theorems. A presentation whose only
        natural checker is genuinely whole-claim and NOT decomposable
        into leaves would not fit this record; no such presentation
        appears in the paper, but the restriction is recorded here
        rather than left implicit.

      Paper text:
        §2 triangle rule for the evidence language.
      Rocq theorem:
        V3_Presentation.certified_dist_trans (and [spine_sound]).
      Correspondence: the triangle rule is PROVED from
      [distF_triangle] plus leaf soundness, not assumed. *)

End V3_Presentation.
