(** * EffectiveCompleteness.v — v3 evidence regularity, principal
       evidence, and finite-core density (§4 Def 4.3, §6)

    Paper reference: Ballús Santacana, "Certificate-Carrying
    Approximation…", arXiv:2506.22693 v3, Definition 4.3,
    Definition 6.1, Definition 6.4, Theorem 6.5.

    STATUS: IN-PROGRESS (see docs/FORMALIZATION_STATUS.md).

    This module formalizes the following v3 items on top of the
    [V3_Presentation.Presentation] record and its
    [V3_Evidence.EvidenceClosure]:

    1. [EvidenceRegular P] — Def 4.3 as a record of two uniform
       proof constructors: canonical-name exact witness, and
       promotion of approximation evidence to distance evidence
       against the canonical name.

    2. [principal_cert_system], [principal_evidence] — Def 6.4.

    3. [principal_evidence_dense] — the first (density) half of
       Thm 6.5: every evidence object is achieved arbitrarily
       closely by a principal evidence object over some finite code.
       Proved rigorously from [EvidenceClosure] + [EvidenceRegular].

    Not in this commit (all IN-PROGRESS in
    docs/FORMALIZATION_STATUS.md):

    - Def 6.1 (effective completeness for the evidence interface)
      as a record of a Cauchy-limit procedure. Requires sequences
      of names with a modulus.
    - Thm 6.2 (Effective limits lift to evidence). Depends on the
      Def 6.1 record.
    - Thm 6.5 part (2) — Cauchy limits of principal evidence. Depends
      on Thm 6.2.
    - The size estimate of Thm 6.5 (encoded certificate lengths).

    No axiom, no Admitted. *)

From Stdlib Require Import Reals QArith Lra Lia.
From UELAT.V3 Require Import Presentation Evidence MetricReflection.
Local Open Scope Q_scope.

Module V3_EffectiveCompleteness.

Import V3_Presentation.
Import V3_Evidence.
Import V3_MetricReflection.

Section WithPresentationAndClosure.
Variable P : Presentation.
Variable EC : EvidenceClosure P.

(** ** Def 4.3 — Evidence-regular presentation.

    Two uniform proof constructors:

    (ER1) [er_exact_witness p] is finite data such that
          [AppCheck (iotaF p) p 0 (er_exact_witness p) = true],
          i.e. a finite code exactly certifies its own canonical name.

    (ER2) [er_promote_witness nu p q V] uniformly promotes an
          accepted approximation witness [(nu, p, q, V)] into
          accepted distance witness against the canonical name
          [iotaF p] at the same bound q.

    The paper's Def 4.3 mentions "by the symmetry rule of the
    evidence language the reverse distance bound is then also
    available"; that reverse bound is not a new field of Def 4.3 —
    it is [ec_sym_witness] applied to the promoted witness, and we
    prove it as [er_promote_reverse_ok] below. *)

Record EvidenceRegular : Type := {
  er_exact_witness   : CodeF P -> list bool;
  er_promote_witness :
    NameF P -> CodeF P -> Q -> list bool -> list bool;

  er_exact_ok :
    forall p, AppCheck P (iotaF P p) p 0 (er_exact_witness p) = true;

  er_promote_ok :
    forall nu p q V,
      AppCheck P nu p q V = true ->
      DistCheck P nu (iotaF P p) q (er_promote_witness nu p q V) = true
}.

Variable ER : EvidenceRegular.

(** Reverse promotion — witnessed by symmetry closure on the
    promoted witness. This is the "reverse distance bound" from the
    paper's Def 4.3 remark. Not a new field of Def 4.3: it is a
    proved lemma. *)

Definition er_promote_reverse_witness
    (nu : NameF P) (p : CodeF P) (q : Q) (V : list bool) : list bool :=
  ec_sym_witness EC nu (iotaF P p) q (er_promote_witness ER nu p q V).

Lemma er_promote_reverse_ok :
  forall nu p q V,
    AppCheck P nu p q V = true ->
    DistCheck P (iotaF P p) nu q
              (er_promote_reverse_witness nu p q V) = true.
Proof.
  intros nu p q V Happ.
  unfold er_promote_reverse_witness.
  apply ec_sym_ok.
  apply er_promote_ok. exact Happ.
Qed.

(** ** Def 6.4 — Principal evidence over a finite code.

    The principal evidence object over [p] is over the canonical
    name [iotaF p], and its certificate system returns the exact
    certificate [(p, 0, er_exact_witness p)] at every positive
    rational tolerance. *)

Definition principal_cert_system (p : CodeF P) : CertSystem P (iotaF P p).
Proof.
  refine
    {| cs_run     := fun _ => (p, 0%Q, er_exact_witness ER p)
     ; cs_bound_lt := _
     ; cs_accept   := _
    |}.
  - intros eps Heps. simpl. split; [apply Qle_refl | exact Heps].
  - intros eps _. simpl. apply er_exact_ok.
Defined.

Definition principal_evidence (p : CodeF P) : EvidenceObject P :=
  {| eo_name   := iotaF P p
   ; eo_system := principal_cert_system p |}.

(** ** Thm 6.5 part (1) — Principal evidence is dense.

    "Every evidence object c is the effective metric limit of a
    computable sequence of principal evidence objects." We formalize
    the density content directly: for every tolerance ε > 0 there
    exists a finite code p and a bound q < ε such that DistCheck
    accepts a witness between the name of [c] and the canonical name
    [iotaF p] at bound q. Under [is_lawvere_dist], this bounds
    d_Cert(c, principal_evidence p) < ε.

    The stated 2^{-n}-parametrized form of the paper is the
    special case ε = 2^{-n}; we keep the ε-form because the
    2^{-n} form requires a chosen rational encoding of 2^{-n} and
    obscures the mathematical content. *)

Theorem principal_evidence_dense :
  forall (c : EvidenceObject P) (eps : Q), (0 < eps)%Q ->
    exists (p : CodeF P) (q : Q),
      (0 <= q)%Q /\ (q < eps)%Q /\
      achievable_bound P c (principal_evidence p) q.
Proof.
  intros c eps Heps.
  (* Get the certificate the certificate system of c produces at eps. *)
  set (nu := eo_name c).
  set (cs := eo_system c).
  destruct (cs_run cs eps) as [[p ebar] V] eqn:Hcs_run.
  pose proof (cs_bound_lt cs eps Heps) as Hbounds.
  pose proof (cs_accept  cs eps Heps) as Haccept.
  rewrite Hcs_run in Hbounds, Haccept. cbn iota beta in *.
  destruct Hbounds as [Hebar_nonneg Hebar_lt_eps].
  (* Promote AppCheck to DistCheck against iotaF p using ER. *)
  pose proof (er_promote_ok ER nu p ebar V Haccept) as Hdist.
  exists p, ebar.
  split; [exact Hebar_nonneg |].
  split; [exact Hebar_lt_eps |].
  (* achievable_bound c (principal_evidence p) ebar is
     dist_accepted P (eo_name c) (eo_name (principal_evidence p)) ebar.
     eo_name (principal_evidence p) = iotaF p by definition. *)
  unfold achievable_bound, dist_accepted, principal_evidence, eo_name.
  exists (er_promote_witness ER nu p ebar V).
  exact Hdist.
Qed.

(** Corollary at the analytic-distance level: under evidence
    regularity, the analytic distance from the underlying point of c
    to the decoded finite code is bounded by the density ε. Follows
    from [principal_evidence_dense] and [DistCheck_sound]. This is
    the reals-level content downstream analytic modules will consume.

    The full Lawvere-distance corollary [d_Cert(c, hat_p) < ε] is
    deferred until [Coq/V3/MetricReflection.v] provides a d_Cert as
    a term rather than as a predicate; the density-at-the-checker
    level captured in [principal_evidence_dense] already carries the
    mathematical content the rest of §6 propagates. *)

Corollary principal_evidence_dense_analytic :
  forall (c : EvidenceObject P) (eps : Q), (0 < eps)%Q ->
    exists (p : CodeF P) (q : Q),
      (0 <= q)%Q /\ (q < eps)%Q /\
      distF P
        (deltaF P (eo_name c))
        (deltaF P (iotaF P p))
      <= Q2R q.
Proof.
  intros c eps Heps.
  destruct (principal_evidence_dense c eps Heps)
    as [p [q [Hnn [Hlt Hacc]]]].
  exists p, q. split; [exact Hnn|]. split; [exact Hlt|].
  destruct Hacc as [W HW].
  eapply DistCheck_sound. exact HW.
Qed.

End WithPresentationAndClosure.

(** ** What this file DOES NOT contain

    - Def 6.1 [EffectiveComplete] record — sequences of names with
      Cauchy modulus, limit-name procedure, tail-evidence procedure.
    - Thm 6.2 [effective_limits_lift] — construction of a certificate
      system over the computed limit name, plus size estimate.
    - Thm 6.5 part (2) — Cauchy-completion at the evidence level.
    - Thm 6.5 size estimate |C_∞(ε)| ≤ |C_{c_n}(ε/4)| + |W| + O(log n) + O(1).
    - The [principal_evidence_dist_lt] corollary in its intended
      Lawvere-distance form — pending a d_Cert-as-term construction
      in [V3/MetricReflection.v] (currently d_Cert is a predicate;
      the density content is captured by [principal_evidence_dense]
      already, which is what downstream modules will consume).

    Correspondence with v3:

      Paper theorem:
        Definition 4.3 (Evidence-regular presentation).
      Rocq definition:
        V3_EffectiveCompleteness.EvidenceRegular.
      Correspondence: EXACT for the two uniform constructors
      (er_exact_witness / er_exact_ok, er_promote_witness /
      er_promote_ok). The reverse-bound remark of Def 4.3 is
      proved as er_promote_reverse_ok, not axiomatized.

      Paper theorem:
        Definition 6.4 (Principal evidence).
      Rocq definitions:
        V3_EffectiveCompleteness.principal_cert_system,
        V3_EffectiveCompleteness.principal_evidence.
      Correspondence: EXACT. The certificate system returns
      (p, 0, er_exact_witness p) at every positive tolerance.

      Paper theorem:
        Theorem 6.5 part (1) — density of principal evidence.
      Rocq theorem:
        V3_EffectiveCompleteness.principal_evidence_dense.
      Correspondence: CHECKED-RESTRICTED. The Rocq theorem proves
      the density content directly at the DistCheck-acceptance
      level: for every ε > 0 there is p and q with 0 ≤ q < ε
      and DistCheck between the name of c and the canonical name
      of p at bound q. The Lawvere-distance form d_Cert(c, hat_p) < ε
      follows by combining with lawvere_bounds_analytic /
      is_lawvere_dist once d_Cert is available as a term.
      The certified-Cauchy-modulus claim of Thm 6.5 (that the
      sequence of hat_{p_n} chosen at ε = 2^{-n} has a computable
      modulus) is not yet proved — requires effective completeness. *)

End V3_EffectiveCompleteness.
