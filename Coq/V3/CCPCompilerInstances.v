(** CCPCompilerInstances.v -- concrete closure instances for v3 Proposition 8.2.

    ContextualChoice.v proves the structural identity/product/composition
    calculus with input-dependent finite query plans and moduli.  This file
    connects that calculus to two manuscript compiler paths: the checker-level
    Lipschitz evidence lift and the H1--H7 refinement-limit constructor.
*)

From Coq Require Import List.
Import ListNotations.
From UELAT.V3 Require Import
  CertificateEnrichment EvidenceCategory EvidenceTransport
  ContextualChoice H1H7Descent.

Module UELAT_V3_CCPCompilerInstances.
Import UELAT_V3_CertificateEnrichment.
Import UELAT_V3_EvidenceCategory.
Import UELAT_V3_EvidenceTransport.
Import UELAT_V3_ContextualChoice.
Import UELAT_V3_H1H7Descent.

Section LipschitzInstance.

  Context {X Y : MetricPresentation}.
  Variable EX : CertificateEnrichment X.
  Variable EY : CertificateEnrichment Y.
  Variable T : carrier X -> carrier Y.
  Variable Tname : name X -> name Y.
  Variable Lambda : R.
  Hypothesis Lambda_nonnegative : 0 <= Lambda.
  Hypothesis Tname_correct : forall nu,
    decode_name (Tname nu) = T (decode_name nu).

  Variable C : EvidenceLocalCompiler EX EY T Tname Lambda.
  Variable nu : name X.

  Definition source_semantic
      (c : CertificateSystem EX nu) : carrier X := decode_name nu.

  Definition target_semantic
      (c : CertificateSystem EY (Tname nu)) : carrier Y :=
    decode_name (Tname nu).

  Definition lipschitz_ccp_constructor :
    CCPConstructor source_semantic target_semantic.
  Proof.
    refine {| ccp_evidence_map := fun c =>
                lift_certificate_system EX EY T Tname Lambda
                  Lambda_nonnegative Tname_correct C nu c;
              ccp_analytic_map := T;
              ccp_queries := fun n _ => [n];
              ccp_modulus := fun n _ => n |}.
    intro c.
    unfold source_semantic, target_semantic.
    apply Tname_correct.
  Defined.

  Theorem lipschitz_ccp_uses_one_declared_source_query : forall n c,
    ccp_query_count lipschitz_ccp_constructor n c = 1.
  Proof. reflexivity. Qed.

End LipschitzInstance.

Section DescentInstance.

  Context {X : MetricPresentation}.
  Context {Payload Rule : Type}.
  Variable f : carrier X.
  Variable p : nat -> carrier X.

  Definition descent_input_semantic
      (H : H1H7Data (Payload:=Payload) (Rule:=Rule) f p) : unit := tt.

  Definition descent_output_semantic
      (x : RepresentedPoint X) : carrier X := represented_value x.

  Definition descent_ccp_constructor :
    CCPConstructor descent_input_semantic descent_output_semantic.
  Proof.
    refine {| ccp_evidence_map := fun H => h1h7_represented_limit H;
              ccp_analytic_map := fun _ => f;
              ccp_queries := fun s H => [h_mu H s];
              ccp_modulus := fun s H => h_mu H s |}.
    intro H. simpl.
    apply h1h7_limit_is_f.
  Defined.

  Theorem descent_ccp_finite_query : forall s H,
    ccp_query_count descent_ccp_constructor s H = 1.
  Proof. reflexivity. Qed.

  Theorem descent_ccp_modulus_is_derived_schedule : forall s H,
    ccp_modulus descent_ccp_constructor s H = h_mu H s.
  Proof. reflexivity. Qed.

  Theorem descent_ccp_target_recertification_zero : forall H,
    h_target_queries H = 0.
  Proof.
    intro H. apply h1h7_target_query_zero.
  Qed.

End DescentInstance.

End UELAT_V3_CCPCompilerInstances.
