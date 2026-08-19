(** * Presentation.v — v3 approximation-presentation interface (§2)

    Paper reference: Ballús Santacana, "Universal Gluing and Contextual Choice: Certificate-Carrying Approximation, Functorial Evidence, and Effective Descent", arXiv:2506.22693 v3, Definition 2.1.

    STATUS: IN-PROGRESS (see docs/FORMALIZATION_STATUS.md).

    This module carries the v3 approximation-presentation record and
    the soundness laws that Definition 2.1 requires of any concrete
    presentation. It intentionally does NOT reuse the legacy
    [Coq/Foundations/Certificate.v] grammar, which is a structural
    inductive object (`cert_wf` checks well-formedness, not analytic
    soundness) and does not correspond to v3's semantic interface.
    See docs/LEGACY_AUDIT.md §Foundations/Certificate.v.

    Design contract:

    - Finite codes [CodeF] are a Type with decidable content in
      concrete instances but stated abstractly here.
    - Names [NameF] are an abstract type paired with a decoder
      [deltaF] into an ambient normed space.
    - We do NOT axiomatize the full normed-vector-space structure of
      [F]. Instead we expose an *analytic distance* [distF : F → F → R]
      obeying non-negativity, self-zero, symmetry and the triangle
      inequality — the metric structure the paper actually uses at
      the checker interface. A concrete presentation with a genuine
      normed space defines [distF a b := ‖a − b‖].
    - [AppCheck] and [DistCheck] are Boolean-valued terminating
      checkers whose acceptance implies the rational bound on
      [distF].
    - The soundness laws are the theorem-level content of the
      record; a concrete presentation MUST discharge them.

    Nothing in this file claims to formalize any v3 THEOREM. It
    formalizes the v3 DEFINITION 2.1. Downstream v3 modules will
    consume this record. *)

From Stdlib Require Import Reals QArith Lra Lia.
Local Open Scope R_scope.

Module V3_Presentation.

(** ** The presentation record

    We keep the ambient normed space abstract, represented by a
    carrier [F] and an analytic distance [distF]. This lets
    [Presentation] be instantiated for W^{1,2}(I) or L¹(ℝ³) later
    (Coq/V3/Models/) without hard-coding a real-analysis library up
    front.

    A concrete Rocq value of type [Presentation] IS a v3 approximation
    presentation. To conclude anything is to feed this record into
    downstream modules; nothing about the mere definition constitutes
    a theorem claim. *)

Record Presentation : Type := {
  (* --- carriers --- *)
  CodeF   : Type;
  NameF   : Type;
  F       : Type;                       (* completion carrier *)
  distF   : F -> F -> R;                (* analytic distance ‖·−·‖ *)
  (* --- distance axioms (make F a pseudo-metric space) --- *)
  distF_nonneg   : forall a b : F, 0 <= distF a b;
  distF_self0    : forall a : F, distF a a = 0;
  distF_sym      : forall a b : F, distF a b = distF b a;
  distF_triangle : forall a b c : F, distF a c <= distF a b + distF b c;
  (* --- decoders --- *)
  rhoF    : CodeF -> F;                 (* code decoder *)
  deltaF  : NameF -> F;                 (* name decoder into represented domain *)
  iotaF   : CodeF -> NameF;             (* canonical name of a code *)
  (* --- size --- *)
  code_size : CodeF -> nat;
  (* --- checkers --- *)
  AppCheck  : NameF -> CodeF -> Q -> list bool -> bool;
  DistCheck : NameF -> NameF -> Q -> list bool -> bool;
  (* --- structural coherence --- *)
  canonical_name_ok :
    forall p : CodeF, deltaF (iotaF p) = rhoF p;
  (* --- soundness laws (Def 2.1 items (5) and (6)) --- *)
  AppCheck_sound :
    forall (nu : NameF) (p : CodeF) (q : Q) (V : list bool),
      AppCheck nu p q V = true ->
      distF (deltaF nu) (rhoF p) <= Q2R q;
  DistCheck_sound :
    forall (nu mu : NameF) (q : Q) (W : list bool),
      DistCheck nu mu q W = true ->
      distF (deltaF nu) (deltaF mu) <= Q2R q
}.

(** ** Small helpers, restated inside a fixed presentation. *)

Section WithPresentation.
Variable P : Presentation.

(** Canonical-name coherence in distance form: the analytic distance
    from the canonical-name decode of [p] to the code decode of [p]
    vanishes. Follows immediately from [canonical_name_ok] and
    [distF_self0]. *)

Lemma canonical_name_distF_zero : forall p,
  distF P (deltaF P (iotaF P p)) (rhoF P p) = 0.
Proof.
  intro p. rewrite canonical_name_ok. apply distF_self0.
Qed.

(** For every accepted [DistCheck] pair, the *reverse* direction also
    gives the same rational bound, by [distF_sym]. This is the "distF
    is symmetric" companion of [DistCheck_sound] — no additional
    hypothesis on the checker itself; it comes from the metric
    axiom. *)

Lemma DistCheck_sound_sym :
  forall nu mu q W,
    DistCheck P nu mu q W = true ->
    distF P (deltaF P mu) (deltaF P nu) <= Q2R q.
Proof.
  intros nu mu q W H.
  rewrite distF_sym.
  apply DistCheck_sound with (W := W). exact H.
Qed.

(** Any accepted [DistCheck] bound is non-negative on the rational
    side, because [distF] is non-negative on the analytic side. *)

Lemma DistCheck_bound_nonneg :
  forall nu mu q W,
    DistCheck P nu mu q W = true -> 0 <= Q2R q.
Proof.
  intros nu mu q W H.
  eapply Rle_trans; [apply distF_nonneg | ].
  apply DistCheck_sound with (W := W). exact H.
Qed.

End WithPresentation.

(** ** What this file DOES NOT contain

    - The evidence category [Cert_ev(F)] of Definition 3.1 — that
      lives in [Coq/V3/Evidence.v].
    - The Lawvere metric [d_Cert] of Definition 3.2 — planned in
      [Coq/V3/MetricReflection.v].
    - The full §2 evidence-language closure rules (reflexivity,
      weakening, symmetry, triangle, finite sum, stored Lipschitz)
      as checker properties. Those live in
      [V3_Evidence.EvidenceClosure], since they are a *hypothesis
      structure on top of* Def 2.1, not a field of Def 2.1 itself.

    Correspondence with v3 (per §11 of the project brief):

      Paper definition:
        Definition 2.1 (Approximation presentation).
      Rocq definition:
        V3_Presentation.Presentation.
      Correspondence:
        SEMANTIC CHECKER CORE of Def 2.1 — not EXACT. The record
        captures the checker interface (finite codes / names /
        decoders / analytic distance / canonical-name coherence /
        AppCheck and DistCheck with soundness), which is what the
        rest of the v3 development consumes. Def 2.1 additionally
        requires:

          (i) [CodeF] to be *effectively enumerable* — i.e. a total
              computable enumeration `nat → CodeF`;
          (ii) the decoding [rhoF : CodeF → F] to have *dense range*
               in the completion of F;
          (iii) the represented subdomain D_F ⊆ F and the assertion
                that [deltaF : NameF → D_F] is *surjective* onto it.

        None of (i)–(iii) is encoded here. They are properties a
        concrete presentation must exhibit — future work will factor
        them into an [EnumerableCode] structure, a represented-domain
        predicate/subtype, and a density property, at which point this
        record can be upgraded toward EXACT.

    This file is CHECKED under Rocq 9 (in the CI-built module set).
    It is not yet a v3 THEOREM — it is a v3 DEFINITION on which v3
    theorems will be stated. *)

End V3_Presentation.
