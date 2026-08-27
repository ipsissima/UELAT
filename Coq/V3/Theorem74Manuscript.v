(** Theorem74Manuscript.v -- manuscript-facing authoritative Theorem 7.4.

    This is the current replacement for the superseded Theorem73Manuscript.v.
    It packages the finite inequalities from the H1--H7 descent development in
    the exact rational-epsilon language of the authoritative manuscript.

    The finite statements below are the constructive content underlying the
    manuscript big-O clauses. A row in FORMALIZATION_STATUS.md remains
    IN-PROGRESS until the asymptotic m(epsilon) / standard-regime wrappers and
    full H1--H7 correspondence have passed the pinned build, coqchk and
    assumptions audit.
*)

From Coq Require Import Reals QArith Qreals.
From UELAT.V3 Require Import
  CertificateEnrichment RepresentedSpace ProofDAG OrderNeutralDescent
  H1H7Descent DescentCertificateSize FiniteCodeDescent
  EpsilonPrecision OrderNeutralEpsilonDescent ManuscriptH1H7.

Module UELAT_V3_Theorem74Manuscript.
Import UELAT_V3_CertificateEnrichment.
Import UELAT_V3_RepresentedSpace.
Import UELAT_V3_ProofDAG.
Import UELAT_V3_OrderNeutralDescent.
Import UELAT_V3_H1H7Descent.
Import UELAT_V3_DescentCertificateSize.
Import UELAT_V3_FiniteCodeDescent.
Import UELAT_V3_EpsilonPrecision.
Import UELAT_V3_OrderNeutralEpsilonDescent.
Import UELAT_V3_ManuscriptH1H7.

Section ManuscriptTheorem.
  Context {X : MetricPresentation}.
  Context {Code Payload Rule : Type}.
  Variable decode : Code -> carrier X.
  Variable f : carrier X.
  Variable pcode : nat -> Code.
  Let p := realized_approximant decode pcode.

  Variable H : H1H7Data (Payload:=Payload) (Rule:=Rule) f p.
  Variables h0 Cchi C0 C1 Rbound : R.
  Variable r : nat.
  Variable MH : ManuscriptH1H7Data f p H h0 Cchi C0 C1 Rbound r.

  Definition theorem74_epsilon_level
      (eps : Q) (Heps : (0 < eps)%Q) : nat :=
    epsilon_level decode f pcode H eps Heps.

  Definition theorem74_epsilon_certificate
      (eps : Q) (Heps : (0 < eps)%Q) :=
    epsilon_certificate decode f pcode H eps Heps.

  Definition theorem74_limit : RepresentedPoint X :=
    epsilon_limit decode f pcode H.

  Theorem theorem74_finite_resource_form :
    forall (eps : Q) (Heps : (0 < eps)%Q) (Heps1 : (eps <= 1)%Q),
    represented_value theorem74_limit = f
    /\ fpc_level (theorem74_epsilon_certificate eps Heps)
         = theorem74_epsilon_level eps Heps
    /\ distance f
         (decode (fpc_code (theorem74_epsilon_certificate eps Heps))) < Q2R eps
    /\ size_denominator H
         * selected_certificate_bits decode f pcode H (epsilon_precision eps Heps)
         <= total_factor H * h_ordinary_bits H (theorem74_epsilon_level eps Heps)
    /\ h_cnum H * h_Cden H
         * nsum_upto (h_level_verification H) (theorem74_epsilon_level eps Heps)
         <= 2 * h_cverify H * h_cden H * h_Cnum H
              * h_M H (theorem74_epsilon_level eps Heps)
              * h_A H (h_beta H (theorem74_epsilon_level eps Heps))
    /\ h_source_lookahead H (theorem74_epsilon_level eps Heps)
         <= h_csource H * h_beta_factor H * S (theorem74_epsilon_level eps Heps)
    /\ h_target_queries H = 0.
  Proof.
    intros eps Heps Heps1.
    exact (order_neutral_descent_at_rational_epsilon decode f pcode H eps Heps).
  Qed.

  Theorem theorem74_precision_exponent : forall eps Heps,
    epsilon_precision eps Heps + 1 + h_offset H
      <= h_alpha H * theorem74_epsilon_level eps Heps.
  Proof.
    intros eps Heps.
    unfold theorem74_epsilon_level, epsilon_level.
    apply h_mu_exponent_dominates.
  Qed.

  Theorem theorem74_genealogy_sum_at_selected_level : forall eps Heps,
    h_cnum H * h_Cden H
      * nsum_upto (h_new_payload_bits H) (theorem74_epsilon_level eps Heps)
      <= 2 * h_cpayload H * h_cden H * h_Cnum H
           * h_base_factor H
           * h_ordinary_bits H (theorem74_epsilon_level eps Heps).
  Proof.
    intros eps Heps.
    unfold theorem74_epsilon_level.
    apply h1h7_genealogy_size.
  Qed.

  Variable SinkIdentifiesCode : Code -> Payload -> Prop.
  Hypothesis Hsink : forall n,
    exists sink_payload,
      (nth_error (dag_nodes (h_history H n)) (dag_sink (h_history H n))
         = Some (InputNode sink_payload)
       \/ exists rr refs,
         nth_error (dag_nodes (h_history H n)) (dag_sink (h_history H n))
           = Some (RuleNode rr refs sink_payload))
      /\ SinkIdentifiesCode (pcode n) sink_payload.

  Theorem theorem74_preserves_selected_ancestry : forall eps Heps,
    exists sink_payload,
      (nth_error
         (dag_nodes (fpc_history (theorem74_epsilon_certificate eps Heps)))
         (dag_sink (fpc_history (theorem74_epsilon_certificate eps Heps)))
         = Some (InputNode sink_payload)
       \/ exists rr refs,
         nth_error
           (dag_nodes (fpc_history (theorem74_epsilon_certificate eps Heps)))
           (dag_sink (fpc_history (theorem74_epsilon_certificate eps Heps)))
           = Some (RuleNode rr refs sink_payload))
      /\ SinkIdentifiesCode
           (fpc_code (theorem74_epsilon_certificate eps Heps)) sink_payload.
  Proof.
    intros eps Heps.
    apply epsilon_certificate_keeps_selected_ancestry.
    exact Hsink.
  Qed.
End ManuscriptTheorem.

End UELAT_V3_Theorem74Manuscript.
