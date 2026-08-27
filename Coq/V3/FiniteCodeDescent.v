(** FiniteCodeDescent.v -- finite-code form of the H1--H7 descent output.

    H1H7Descent.v is phrased over realized analytic approximants p_n. The
    authoritative paper additionally requires each p_n to be an actual finite
    code and the proof DAG sink to identify that code. This module restores
    that intensional layer explicitly.
*)

From Coq Require Import Reals Arith.
From UELAT.V3 Require Import
  CertificateEnrichment RepresentedSpace ProofDAG
  H1H7Descent DescentCertificateSize.

Module UELAT_V3_FiniteCodeDescent.
Import UELAT_V3_CertificateEnrichment.
Import UELAT_V3_RepresentedSpace.
Import UELAT_V3_ProofDAG.
Import UELAT_V3_H1H7Descent.
Import UELAT_V3_DescentCertificateSize.

Section FiniteCodes.
  Context {X : MetricPresentation}.
  Context {Code Payload Rule : Type}.
  Variable decode : Code -> carrier X.
  Variable f : carrier X.
  Variable pcode : nat -> Code.

  Definition realized_approximant (n : nat) : carrier X := decode (pcode n).

  Variable H : H1H7Data (Payload:=Payload) (Rule:=Rule)
                 f realized_approximant.
  Variable SinkIdentifiesCode : Code -> Payload -> Prop.

  Hypothesis history_sink_identifies_code : forall n,
    exists sink_payload,
      (nth_error (dag_nodes (h_history H n)) (dag_sink (h_history H n))
         = Some (InputNode sink_payload)
       \/ exists r refs,
         nth_error (dag_nodes (h_history H n)) (dag_sink (h_history H n))
           = Some (RuleNode r refs sink_payload))
      /\ SinkIdentifiesCode (pcode n) sink_payload.

  Record FinitePrecisionCertificate (s : nat) := {
    fpc_level : nat;
    fpc_level_eq : fpc_level = h_mu H s;
    fpc_code : Code;
    fpc_code_eq : fpc_code = pcode fpc_level;
    fpc_history : ProofDAG Payload Rule;
    fpc_history_eq : fpc_history = h_history H fpc_level;
    fpc_realized_error : distance f (decode fpc_code) <= dyadic s / 2
  }.

  Definition finite_precision_certificate (s : nat) :
      FinitePrecisionCertificate s.
  Proof.
    refine {| fpc_level := h_mu H s;
              fpc_level_eq := eq_refl;
              fpc_code := pcode (h_mu H s);
              fpc_code_eq := eq_refl;
              fpc_history := h_history H (h_mu H s);
              fpc_history_eq := eq_refl |}.
    exact (h_scheduled_error H s).
  Defined.

  Theorem selected_history_sink_identifies_selected_code : forall s,
    exists sink_payload,
      (nth_error (dag_nodes (fpc_history (finite_precision_certificate s)))
         (dag_sink (fpc_history (finite_precision_certificate s)))
         = Some (InputNode sink_payload)
       \/ exists r refs,
         nth_error (dag_nodes (fpc_history (finite_precision_certificate s)))
           (dag_sink (fpc_history (finite_precision_certificate s)))
           = Some (RuleNode r refs sink_payload))
      /\ SinkIdentifiesCode (fpc_code (finite_precision_certificate s)) sink_payload.
  Proof. intro s. simpl. apply history_sink_identifies_code. Qed.

  Definition selected_certificate_bits (s : nat) : nat :=
    precision_certificate_bits H s.

  Theorem selected_certificate_size_order_neutral : forall s,
    size_denominator H * selected_certificate_bits s
      <= total_factor H * h_ordinary_bits H (h_mu H s).
  Proof. intro s. apply precision_certificate_size_relative_to_B. Qed.
End FiniteCodes.

End UELAT_V3_FiniteCodeDescent.
