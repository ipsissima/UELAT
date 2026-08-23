(** * EffectiveCompleteness.v — evidence regularity, principal
       evidence, finite-core density (§4 Def 4.3, §6)

    Paper reference: Ballús Santacana, "Universal Gluing and Contextual
    Choice: Certificate-Carrying Approximation, Functorial Evidence, and
    Effective Descent", arXiv:2506.22693 v3, Definitions 4.3, 6.1, 6.4
    and Theorem 6.5.

    STATUS: IN-PROGRESS (see docs/FORMALIZATION_STATUS.md).

    Evidence regularity is represented computationally: promotion of an
    accepted approximation certificate supplies an actual normalized
    distance spine, with a separate correctness theorem proving its
    bound. This is stronger than a Prop-only existential and is exactly
    the form needed later to compute the target certificate system in
    the generic lifting theorem. *)

From Stdlib Require Import Reals QArith Qreals Qcanon Lra Lia.
From UELAT.V3 Require Import EvidenceSyntax Presentation Evidence MetricReflection.
Local Open Scope Qc_scope.

Module V3_EffectiveCompleteness.

Import V3_EvidenceSyntax.
Import V3_Presentation.
Import V3_Evidence.
Import V3_MetricReflection.

Section WithPresentation.
Variable P : Presentation.
Variable EC : EvidenceClosure (P := P).

(** ** Def 4.3 — Evidence-regular presentation.

    (ER1) a finite code certifies its own canonical name exactly;
    (ER2) approximation evidence promotes UNIFORMLY to an actual
          normalized distance witness against the canonical name.

    [er_promote_spine] is defined for every finite input tuple; the
    correctness field [er_promote_bound] is conditional on AppCheck
    acceptance. This keeps the computational witness independent of
    eliminating a proof from Prop into Type. *)

Record EvidenceRegular : Type := {
  er_exact_witness : CodeF P -> list bool;
  er_exact_ok :
    forall p, AppCheck P (iotaF P p) p 0 (er_exact_witness p) = true;

  er_promote_spine :
    forall (nu : NameF P) (p : CodeF P) (q : Qc) (V : list bool),
      PSpine P nu (iotaF P p);
  er_promote_bound :
    forall (nu : NameF P) (p : CodeF P) (q : Qc) (V : list bool),
      AppCheck P nu p q V = true ->
      (sp_bound (er_promote_spine nu p q V) <= q)%Qc
}.

Variable ER : EvidenceRegular.

(** Prop-level promotion is derived from the witness-producing fields. *)

Theorem er_promote_certified :
  forall (nu : NameF P) (p : CodeF P) (q : Qc) (V : list bool),
    AppCheck P nu p q V = true ->
    certified_dist P nu (iotaF P p) q.
Proof.
  intros nu p q V Happ.
  exists (er_promote_spine ER nu p q V).
  apply er_promote_bound. exact Happ.
Qed.

(** The reverse bound of Def 4.3's remark — obtained from the
    witness-producing symmetry constructor, proved rather than posited
    as a further field. *)

Lemma er_promote_reverse :
  forall (nu : NameF P) (p : CodeF P) (q : Qc) (V : list bool),
    AppCheck P nu p q V = true ->
    certified_dist P (iotaF P p) nu q.
Proof.
  intros nu p q V Happ.
  apply (ec_sym_certified P EC).
  eapply er_promote_certified. exact Happ.
Qed.

(** ** Def 6.4 — Principal evidence over a finite code. *)

Definition principal_cert_system (p : CodeF P) : CertSystem (iotaF P p).
Proof.
  refine {| cs_run := fun _ => (p, 0, er_exact_witness ER p)
          ; cs_bound_lt := _
          ; cs_accept := _ |}.
  - intros eps Heps. simpl. split; [apply Qcle_refl | exact Heps].
  - intros eps _. simpl. apply er_exact_ok.
Defined.

Definition principal_evidence (p : CodeF P) : EvidenceObject P :=
  {| eo_name := iotaF P p ; eo_system := principal_cert_system p |}.

(** ** Thm 6.5 (1) — principal evidence is dense. *)

Theorem principal_evidence_dense :
  forall (c : EvidenceObject P) (eps : Qc), 0 < eps ->
    exists (p : CodeF P) (q : Qc),
      0 <= q /\ q < eps /\ achievable_bound P c (principal_evidence p) q.
Proof.
  intros c eps Heps.
  set (nu := eo_name c).
  set (cs := eo_system c).
  destruct (cs_run cs eps) as [[p ebar] V] eqn:Hrun.
  pose proof (cs_bound_lt cs eps Heps) as Hb.
  pose proof (cs_accept  cs eps Heps) as Ha.
  rewrite Hrun in Hb, Ha. cbn iota beta in Hb, Ha.
  destruct Hb as [Hnn Hlt].
  exists p, ebar.
  split; [exact Hnn |]. split; [exact Hlt |].
  unfold achievable_bound, principal_evidence, eo_name.
  eapply er_promote_certified. exact Ha.
Qed.

(** Analytic corollary: the decoded points are that close. *)

Corollary principal_evidence_dense_analytic :
  forall (c : EvidenceObject P) (eps : Qc), 0 < eps ->
    exists (p : CodeF P) (q : Qc),
      0 <= q /\ q < eps /\
      (distF P (deltaF P (eo_name c)) (deltaF P (iotaF P p)) <= Qc2R q)%R.
Proof.
  intros c eps Heps.
  destruct (principal_evidence_dense c eps Heps) as [p [q [Hnn [Hlt Hacc]]]].
  exists p, q. split; [exact Hnn|]. split; [exact Hlt|].
  apply certified_dist_sound. exact Hacc.
Qed.

End WithPresentation.

Arguments EvidenceRegular {_}.
Arguments er_exact_witness {_ _} _ _.
Arguments er_exact_ok {_ _} _ _.
Arguments er_promote_spine {_ _} _ _ _ _ _.
Arguments er_promote_bound {_ _} _ {_ _ _ _} _.

(** ** Correspondence with v3

      Def 4.3   → EvidenceRegular                (DEFINITION-EXACT
                                                  candidate pending CI)
      Def 6.4   → principal_cert_system,
                  principal_evidence             (DEFINITION-EXACT)
      Thm 6.5(1)→ principal_evidence_dense
                  (+ analytic corollary)         (CHECKED-RESTRICTED)

    The important refinement in this revision is computational rather
    than logical: [er_promote_spine] returns the finite distance witness
    itself and [er_promote_bound] verifies it. The older Prop-only
    existential wrapper is retained as the derived theorem
    [er_promote_certified]. This is required by Theorem 5.2's
    object-level lift, whose target certificate system must compute its
    witness data.

    Def 6.1 (effective completeness), Thm 6.2 (effective limits lift to
    evidence) and Thm 6.5(2) remain PAPER-ONLY. *)

End V3_EffectiveCompleteness.
