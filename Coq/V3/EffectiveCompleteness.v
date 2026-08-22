(** * EffectiveCompleteness.v — evidence regularity, principal
       evidence, finite-core density (§4 Def 4.3, §6)

    Paper reference: Ballús Santacana, "Universal Gluing and Contextual
    Choice: Certificate-Carrying Approximation, Functorial Evidence, and
    Effective Descent", arXiv:2506.22693 v3, Definitions 4.3, 6.1, 6.4
    and Theorem 6.5.

    STATUS: IN-PROGRESS (see docs/FORMALIZATION_STATUS.md).

    Rebased onto normalized evidence. The promotion constructor of
    Def 4.3 now lands in [certified_dist] — "some normalized spine
    certifies this bound" — rather than producing an opaque witness for
    an assumed whole-claim checker. *)

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
    (ER2) accepted approximation evidence promotes, uniformly, to
          certified distance against that canonical name at the same
          bound. *)

Record EvidenceRegular : Type := {
  er_exact_witness : CodeF P -> list bool;
  er_exact_ok :
    forall p, AppCheck P (iotaF P p) p 0 (er_exact_witness p) = true;
  er_promote :
    forall (nu : NameF P) (p : CodeF P) (q : Qc) (V : list bool),
      AppCheck P nu p q V = true -> certified_dist P nu (iotaF P p) q
}.

Variable ER : EvidenceRegular.

(** The reverse bound of Def 4.3's remark — obtained from symmetry,
    proved rather than posited as a further field. *)

Lemma er_promote_reverse :
  forall (nu : NameF P) (p : CodeF P) (q : Qc) (V : list bool),
    AppCheck P nu p q V = true ->
    certified_dist P (iotaF P p) nu q.
Proof.
  intros nu p q V Happ.
  apply (ec_sym EC). eapply er_promote. exact Happ.
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

(** ** Thm 6.5 (1) — principal evidence is dense.

    For every evidence object and every positive tolerance there is a
    finite code whose principal evidence is certified within that
    tolerance. Stated at the certified-distance level, which is where
    the rest of §6 consumes it. *)

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
  eapply er_promote. exact Ha.
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

(** ** Correspondence with v3

      Def 4.3   → EvidenceRegular                (DEFINITION-EXACT)
      Def 6.4   → principal_cert_system,
                  principal_evidence             (DEFINITION-EXACT)
      Thm 6.5(1)→ principal_evidence_dense
                  (+ analytic corollary)         (CHECKED-RESTRICTED)

    Def 6.1 (effective completeness), Thm 6.2 (effective limits lift to
    evidence) and Thm 6.5(2) remain PAPER-ONLY. *)

End V3_EffectiveCompleteness.
