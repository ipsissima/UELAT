(** Theorem74Manuscript.v -- manuscript-facing statement of authoritative
    Theorem 7.4, "Encoding-cost evidence transport under Sobolev refinement".

    The core theorem below uses H1--H7 only. The explicit linear-bit regime
    and the still stronger source-lookahead regime are separate, matching the
    manuscript's conditional clauses.
*)

From Coq Require Import Reals QArith Qreals.
From UELAT.V3 Require Import
  CertificateEnrichment RepresentedSpace ProofDAG
  H1H7Descent FiniteCodeDescent DescentCertificateSize
  EpsilonPrecision ManuscriptH1H7 OrderNeutralEpsilonDescent.

Module UELAT_V3_Theorem74Manuscript.
Import UELAT_V3_CertificateEnrichment.
Import UELAT_V3_RepresentedSpace.
Import UELAT_V3_ProofDAG.
Import UELAT_V3_H1H7Descent.
Import UELAT_V3_FiniteCodeDescent.
Import UELAT_V3_DescentCertificateSize.
Import UELAT_V3_EpsilonPrecision.
Import UELAT_V3_ManuscriptH1H7.
Import UELAT_V3_OrderNeutralEpsilonDescent.

Section ManuscriptTheorem.
  Context {X : MetricPresentation}.
  Context {Code Payload Rule : Type}.
  Variable decode : Code -> carrier X.
  Variable f : carrier X.
  Variable pcode : nat -> Code.
  Let p := realized_approximant decode pcode.

  Variable H : H1H7Data (Payload:=Payload) (Rule:=Rule) f p.

  Variable Cchi C0 C1 Rbound : R.
  Variable r : nat.
  Variable MH :
    ManuscriptH1H7Data f p H Cchi C0 C1 Rbound r.

  Definition theorem74_epsilon_certificate
      (eps : Q) (Heps : (0 < eps)%Q) :=
    epsilon_certificate decode f pcode H eps Heps.

  Definition theorem74_level
      (eps : Q) (Heps : (0 < eps)%Q) : nat :=
    epsilon_level decode f pcode H eps Heps.

  Theorem theorem74_manuscript_core :
    forall (eps : Q) (Heps : (0 < eps)%Q) (Heps1 : (eps <= 1)%Q),
    represented_value (epsilon_limit decode f pcode H) = f
    /\ distance f
         (decode (fpc_code (theorem74_epsilon_certificate eps Heps)))
         < Q2R eps
    /\ size_denominator H
         * selected_certificate_bits decode f pcode H
             (epsilon_precision eps Heps)
         <= total_factor H
              * h_ordinary_bits H (theorem74_level eps Heps)
    /\ h_cnum H * h_Cden H
         * nsum_upto (h_level_verification H) (theorem74_level eps Heps)
         <= 2 * h_cverify H * h_cden H * h_Cnum H
              * h_M H (theorem74_level eps Heps)
              * h_A H (h_beta H (theorem74_level eps Heps))
    /\ h_target_queries H = 0.
  Proof.
    intros eps Heps Heps1.
    pose proof
      (order_neutral_descent_at_rational_epsilon
        decode f pcode H eps Heps) as Hmain.
    destruct Hmain as [Hlim [Hlevel [Herr [Hsize [Hverify Htarget]]]]].
    repeat split; assumption.
  Qed.

  Theorem theorem74_level_exponent_control : forall eps Heps,
    epsilon_precision eps Heps + 1 + h_offset H
      <= Nat.pred r * theorem74_level eps Heps.
  Proof.
    intros eps Heps.
    unfold theorem74_level, epsilon_level.
    rewrite <- (mh_alpha_is_r_minus_1 MH).
    apply h_mu_exponent_dominates.
  Qed.

  Section LinearBits.
    Variable LB : LinearBitRegime H.

    Theorem theorem74_linear_bit_schedule : forall eps Heps,
      h_beta H (theorem74_level eps Heps)
        <= lb_beta_factor LB * S (theorem74_level eps Heps).
    Proof.
      intros eps Heps.
      apply lb_beta_linear.
    Qed.

    Section SourceLookahead.
      Variable SR : SourceLookaheadRegime H LB.

      Theorem theorem74_manuscript_source_lookahead : forall eps Heps,
        sr_source_lookahead SR (theorem74_level eps Heps)
          <= sr_csource SR * lb_beta_factor LB * S (theorem74_level eps Heps).
      Proof.
        intros eps Heps.
        unfold theorem74_level.
        apply order_neutral_source_lookahead_at_rational_epsilon.
      Qed.
    End SourceLookahead.
  End LinearBits.

  Variable SinkIdentifiesCode : Code -> Payload -> Prop.
  Hypothesis Hsink : forall n,
    exists sink_payload,
      (nth_error (dag_nodes (h_history H n)) (dag_sink (h_history H n))
         = Some (InputNode sink_payload)
       \/ exists rr refs,
         nth_error (dag_nodes (h_history H n)) (dag_sink (h_history H n))
           = Some (RuleNode rr refs sink_payload))
      /\ SinkIdentifiesCode (pcode n) sink_payload.

  Theorem theorem74_manuscript_preserves_ancestry : forall eps Heps,
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
