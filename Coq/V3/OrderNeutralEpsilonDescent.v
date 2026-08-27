(** OrderNeutralEpsilonDescent.v -- rational-epsilon core of authoritative Theorem 7.4.

    The descent development is first indexed by a dyadic precision exponent s.
    EpsilonPrecision.v computes such an s from any positive rational epsilon.
    This file packages represented-limit, finite-code, size, verification,
    source-lookahead and Q_target=0 conclusions in the paper's tolerance
    language.
*)

From Coq Require Import Reals QArith Qreals Lra.
From UELAT.V3 Require Import
  CertificateEnrichment RepresentedSpace ProofDAG OrderNeutralDescent
  H1H7Descent DescentCertificateSize FiniteCodeDescent
  EpsilonPrecision.

Module UELAT_V3_OrderNeutralEpsilonDescent.
Import UELAT_V3_CertificateEnrichment.
Import UELAT_V3_RepresentedSpace.
Import UELAT_V3_ProofDAG.
Import UELAT_V3_OrderNeutralDescent.
Import UELAT_V3_H1H7Descent.
Import UELAT_V3_DescentCertificateSize.
Import UELAT_V3_FiniteCodeDescent.
Import UELAT_V3_EpsilonPrecision.

Section EpsilonTheorem.
  Context {X : MetricPresentation}.
  Context {Code Payload Rule : Type}.
  Variable decode : Code -> carrier X.
  Variable f : carrier X.
  Variable pcode : nat -> Code.

  Let p := realized_approximant decode pcode.
  Variable H : H1H7Data (Payload:=Payload) (Rule:=Rule) f p.

  Definition epsilon_level (eps : Q) (Heps : (0 < eps)%Q) : nat :=
    h_mu H (epsilon_precision eps Heps).

  Definition epsilon_certificate
      (eps : Q) (Heps : (0 < eps)%Q) :
      FinitePrecisionCertificate decode f pcode H
        (epsilon_precision eps Heps) :=
    finite_precision_certificate decode f pcode H (epsilon_precision eps Heps).

  Definition epsilon_limit : RepresentedPoint X := h1h7_represented_limit H.

  Theorem epsilon_certificate_is_valid : forall eps Heps,
    distance f (decode (fpc_code (epsilon_certificate eps Heps))) < Q2R eps.
  Proof.
    intros eps Heps.
    pose proof (fpc_realized_error (epsilon_certificate eps Heps)) as Herr.
    pose proof (epsilon_precision_half_tail eps Heps) as Htail.
    lra.
  Qed.

  Theorem order_neutral_descent_at_rational_epsilon : forall eps Heps,
    represented_value epsilon_limit = f
    /\ fpc_level (epsilon_certificate eps Heps) = epsilon_level eps Heps
    /\ distance f (decode (fpc_code (epsilon_certificate eps Heps))) < Q2R eps
    /\ size_denominator H
         * selected_certificate_bits decode f pcode H (epsilon_precision eps Heps)
         <= total_factor H * h_ordinary_bits H (epsilon_level eps Heps)
    /\ h_cnum H * h_Cden H
         * nsum_upto (h_level_verification H) (epsilon_level eps Heps)
         <= 2 * h_cverify H * h_cden H * h_Cnum H
              * h_M H (epsilon_level eps Heps)
              * h_A H (h_beta H (epsilon_level eps Heps))
    /\ h_source_lookahead H (epsilon_level eps Heps)
         <= h_csource H * h_beta_factor H * S (epsilon_level eps Heps)
    /\ h_target_queries H = 0.
  Proof.
    intros eps Heps. repeat split.
    - apply h1h7_limit_is_f.
    - reflexivity.
    - apply epsilon_certificate_is_valid.
    - unfold epsilon_level. apply selected_certificate_size_order_neutral.
    - unfold epsilon_level. apply h1h7_verification_bound.
    - unfold epsilon_level. apply h1h7_source_lookahead_bound.
    - apply h1h7_target_query_zero.
  Qed.

  Variable SinkIdentifiesCode : Code -> Payload -> Prop.
  Hypothesis Hsink : forall n,
    exists sink_payload,
      (nth_error (dag_nodes (h_history H n)) (dag_sink (h_history H n))
         = Some (InputNode sink_payload)
       \/ exists r refs,
         nth_error (dag_nodes (h_history H n)) (dag_sink (h_history H n))
           = Some (RuleNode r refs sink_payload))
      /\ SinkIdentifiesCode (pcode n) sink_payload.

  Theorem epsilon_certificate_keeps_selected_ancestry : forall eps Heps,
    exists sink_payload,
      (nth_error (dag_nodes (fpc_history (epsilon_certificate eps Heps)))
         (dag_sink (fpc_history (epsilon_certificate eps Heps)))
         = Some (InputNode sink_payload)
       \/ exists r refs,
         nth_error (dag_nodes (fpc_history (epsilon_certificate eps Heps)))
           (dag_sink (fpc_history (epsilon_certificate eps Heps)))
           = Some (RuleNode r refs sink_payload))
      /\ SinkIdentifiesCode (fpc_code (epsilon_certificate eps Heps)) sink_payload.
  Proof.
    intros eps Heps.
    apply selected_history_sink_identifies_selected_code.
    exact Hsink.
  Qed.
End EpsilonTheorem.

End UELAT_V3_OrderNeutralEpsilonDescent.
