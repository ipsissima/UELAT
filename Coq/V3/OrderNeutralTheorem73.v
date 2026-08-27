(** OrderNeutralTheorem73.v -- bundled finite-code statement closest to the
    manuscript's Theorem 7.3.

    The theorem below simultaneously returns the selected finite code and its
    persistent history, proves the represented-limit stage/error property,
    compares full certificate size with the ordinary finite encoding, bounds
    verification and source lookahead, and records zero target recertification.

    H1--H7 are supplied through H1H7Data; the remaining formalization gap is the
    concrete construction of those H2/H3/H4 fields from the rational PUFEM
    checker/compiler, not the refinement-to-limit or resource argument itself.
*)

From Coq Require Import Reals Arith.
From UELAT.V3 Require Import
  CertificateEnrichment RepresentedSpace ProofDAG
  H1H7Descent DescentCertificateSize FiniteCodeDescent.

Module UELAT_V3_OrderNeutralTheorem73.
Import UELAT_V3_CertificateEnrichment.
Import UELAT_V3_RepresentedSpace.
Import UELAT_V3_ProofDAG.
Import UELAT_V3_H1H7Descent.
Import UELAT_V3_DescentCertificateSize.
Import UELAT_V3_FiniteCodeDescent.

Section Theorem73.

  Context {X : MetricPresentation}.
  Context {Code Payload Rule : Type}.
  Variable decode : Code -> carrier X.
  Variable f : carrier X.
  Variable pcode : nat -> Code.

  Let p := realized_approximant decode pcode.

  Variable H : H1H7Data (Payload:=Payload) (Rule:=Rule) f p.
  Variable SinkIdentifiesCode : Code -> Payload -> Prop.
  Hypothesis Hsink : forall n,
    exists sink_payload,
      (nth_error (dag_nodes (h_history H n)) (dag_sink (h_history H n))
         = Some (InputNode sink_payload)
       \/ exists r refs,
         nth_error (dag_nodes (h_history H n)) (dag_sink (h_history H n))
           = Some (RuleNode r refs sink_payload))
      /\ SinkIdentifiesCode (pcode n) sink_payload.

  Definition theorem73_certificate (s : nat) :
      FinitePrecisionCertificate decode f pcode H s :=
    finite_precision_certificate decode f pcode H s.

  Definition theorem73_limit : RepresentedPoint X :=
    h1h7_represented_limit H.

  Theorem order_neutral_proof_carrying_descent : forall s,
    represented_value theorem73_limit = f
    /\ approximant (represented_name theorem73_limit) s
         = decode (pcode (h_mu H s))
    /\ distance f (decode (fpc_code (theorem73_certificate s))) <= dyadic s / 2
    /\ size_denominator H * selected_certificate_bits decode f pcode H s
         <= total_factor H * h_ordinary_bits H (h_mu H s)
    /\ h_cnum H * h_Cden H
         * nsum_upto (h_level_verification H) (h_mu H s)
         <= 2 * h_cverify H * h_cden H * h_Cnum H
              * h_M H (h_mu H s) * h_A H (h_beta H (h_mu H s))
    /\ h_source_lookahead H (h_mu H s)
         <= h_csource H * h_beta_factor H * S (h_mu H s)
    /\ h_target_queries H = 0.
  Proof.
    intro s.
    repeat split.
    - apply h1h7_limit_is_f.
    - apply h1h7_name_stage.
    - exact (fpc_realized_error (theorem73_certificate s)).
    - apply selected_certificate_size_order_neutral.
    - apply h1h7_verification_bound.
    - apply h1h7_source_lookahead_bound.
    - apply h1h7_target_query_zero.
  Qed.

  Theorem theorem73_certificate_has_selected_ancestry : forall s,
    exists sink_payload,
      (nth_error (dag_nodes (fpc_history (theorem73_certificate s)))
         (dag_sink (fpc_history (theorem73_certificate s)))
         = Some (InputNode sink_payload)
       \/ exists r refs,
         nth_error (dag_nodes (fpc_history (theorem73_certificate s)))
           (dag_sink (fpc_history (theorem73_certificate s)))
           = Some (RuleNode r refs sink_payload))
      /\ SinkIdentifiesCode (fpc_code (theorem73_certificate s)) sink_payload.
  Proof.
    intro s.
    apply selected_history_sink_identifies_selected_code.
    exact Hsink.
  Qed.

End Theorem73.

End UELAT_V3_OrderNeutralTheorem73.
