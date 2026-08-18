(** * Presentation.v — v3 approximation-presentation interface (§2)

    Paper reference: Ballús Santacana, "Certificate-Carrying
    Approximation…", arXiv:2506.22693 v3, Definition 2.1.

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
    - [AppCheck] and [DistCheck] are Boolean-valued terminating
      checkers whose acceptance implies the rational bound.
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
    carrier [F] and a norm function [normF]. This lets [Presentation]
    be instantiated for [W^{1,2}(I)] later (Coq/V3/Models/) without
    hard-coding a real-analysis library up front.

    A concrete Rocq value of type [Presentation] IS a v3 approximation
    presentation. To conclude anything is to feed this record into
    downstream modules; nothing about the mere definition constitutes
    a theorem claim. *)

Record Presentation : Type := {
  (* --- carriers --- *)
  CodeF   : Type;
  NameF   : Type;
  F       : Type;                       (* completion carrier *)
  normF   : F -> R;
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
      normF (deltaF nu) - normF (rhoF p) <= Q2R q
      /\ - (Q2R q) <= normF (deltaF nu) - normF (rhoF p);
  DistCheck_sound :
    forall (nu mu : NameF) (q : Q) (W : list bool),
      DistCheck nu mu q W = true ->
      normF (deltaF nu) - normF (deltaF mu) <= Q2R q
      /\ - (Q2R q) <= normF (deltaF nu) - normF (deltaF mu)
}.

(** ** Notation shorthand for use inside a fixed presentation. *)

Section WithPresentation.
Variable P : Presentation.

Notation "|| x ||" := (normF P x) (at level 65).

(** The Def 2.1 soundness statements as ordinary R-inequalities.
    These are the shapes downstream v3 modules will consume; the two
    projections of the [/\] in [AppCheck_sound] bundle to
    [Rabs (|delta nu| - |rho p|) <= Q2R q]. We keep them as separate
    lemmas so callers can pick the direction they need. *)

Lemma app_upper :
  forall nu p q V,
    AppCheck P nu p q V = true ->
    normF P (deltaF P nu) - normF P (rhoF P p) <= Q2R q.
Proof.
  intros nu p q V H. destruct (AppCheck_sound P nu p q V H) as [Hup _]. exact Hup.
Qed.

Lemma app_lower :
  forall nu p q V,
    AppCheck P nu p q V = true ->
    - Q2R q <= normF P (deltaF P nu) - normF P (rhoF P p).
Proof.
  intros nu p q V H. destruct (AppCheck_sound P nu p q V H) as [_ Hlo]. exact Hlo.
Qed.

Lemma dist_upper :
  forall nu mu q W,
    DistCheck P nu mu q W = true ->
    normF P (deltaF P nu) - normF P (deltaF P mu) <= Q2R q.
Proof.
  intros nu mu q W H. destruct (DistCheck_sound P nu mu q W H) as [Hup _]. exact Hup.
Qed.

Lemma dist_lower :
  forall nu mu q W,
    DistCheck P nu mu q W = true ->
    - Q2R q <= normF P (deltaF P nu) - normF P (deltaF P mu).
Proof.
  intros nu mu q W H. destruct (DistCheck_sound P nu mu q W H) as [_ Hlo]. exact Hlo.
Qed.

(** Canonical-name identity, restated in norm form for downstream
    convenience: the norm of a canonical-name decode equals the norm
    of the code decode. Follows from [canonical_name_ok] by
    congruence. *)

Lemma canonical_name_norm : forall p,
  normF P (deltaF P (iotaF P p)) = normF P (rhoF P p).
Proof. intro p. now rewrite canonical_name_ok. Qed.

End WithPresentation.

(** ** What this file DOES NOT contain

    - The evidence category [Cert_ev(F)] of Definition 3.1 —
      that lives in [Coq/V3/Evidence.v] (planned).
    - The Lawvere metric [d_Cert] of Definition 3.2 — planned in
      [Coq/V3/MetricReflection.v].
    - Any of the closure rules on the evidence language
      (reflexivity, weakening, symmetry, triangle, finite sum, stored
      Lipschitz). Those are properties of [AppCheck]/[DistCheck] that
      a concrete presentation must exhibit; the [Presentation] record
      does not enforce them at the abstract level. Concrete
      instances (e.g. [Coq/V3/Models/W12Presentation.v]) will build
      them into their checkers and expose them as separate lemmas.

    Correspondence with v3 (per §11 of the project brief):

      Paper theorem:
        Definition 2.1 (Approximation presentation).
      Rocq definition:
        V3_Presentation.Presentation.
      Correspondence:
        EXACT for the record shape and the two soundness laws (items
        (5) and (6) of Def 2.1). Structural coherence
        [canonical_name_ok] is item (3). The other Def 2.1 items —
        finite enumerability of [CodeF], size function, closure of
        the evidence language under the standard finite norm rules —
        are conditions IMPOSED ON [Presentation] AT USE, not fields
        of the record.

    This file is CHECKED under Rocq 9 (in the CI-built module set).
    It is not yet a v3 THEOREM — it is a v3 DEFINITION on which v3
    theorems will be stated. *)

End V3_Presentation.
