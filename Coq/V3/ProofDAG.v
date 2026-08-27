(** ProofDAG.v -- finite proof genealogy and encoding for reconstructed UELAT v3.

    This module formalizes the structural content of manuscript Definition 6.1
    and Definition 7.1. A provenance-complete certificate consists of an
    accepted ordinary certificate plus a finite rooted proof DAG. References
    point strictly backwards, so shared subproofs are stored once. The module
    fixes a concrete binary-reference size model, a reachable-node checking
    condition, and an explicit relation identifying the sink payload with the
    finite code constructed by the certificate.
*)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From UELAT.V3 Require Import CertificateEnrichment.

Module UELAT_V3_ProofDAG.
Import UELAT_V3_CertificateEnrichment.

Inductive ProofNode (Payload Rule : Type) : Type :=
| InputNode : Payload -> ProofNode Payload Rule
| RuleNode : Rule -> list nat -> Payload -> ProofNode Payload Rule.

Arguments InputNode {Payload Rule} _.
Arguments RuleNode {Payload Rule} _ _ _.

Definition node_payload {Payload Rule} (n : ProofNode Payload Rule) : Payload :=
  match n with
  | InputNode p => p
  | RuleNode _ _ p => p
  end.

Record ProofDAG (Payload Rule : Type) := {
  dag_nodes : list (ProofNode Payload Rule);
  dag_sink : nat;
  dag_sink_in_range : dag_sink < length dag_nodes;
  dag_backward : forall i rule refs payload,
      nth_error dag_nodes i = Some (RuleNode rule refs payload) ->
      Forall (fun j => j < i) refs
}.

Arguments dag_nodes {Payload Rule} _.
Arguments dag_sink {Payload Rule} _.
Arguments dag_sink_in_range {Payload Rule} _.
Arguments dag_backward {Payload Rule} _ _ _ _ _ _.

Definition node_count {Payload Rule} (H : ProofDAG Payload Rule) : nat :=
  length (dag_nodes H).

Lemma proof_dag_nonempty {Payload Rule} (H : ProofDAG Payload Rule) :
  0 < node_count H.
Proof.
  unfold node_count.
  pose proof (dag_sink_in_range H).
  lia.
Qed.

Definition nat_bitlength (n : nat) : nat := S (Nat.log2 n).

Fixpoint sum_nat (xs : list nat) : nat :=
  match xs with
  | [] => 0
  | x :: xs' => x + sum_nat xs'
  end.

Definition references_bitlength (refs : list nat) : nat :=
  sum_nat (map nat_bitlength refs).

Definition proof_node_bitlength
    {Payload Rule}
    (payload_bits : Payload -> nat)
    (rule_bits : Rule -> nat)
    (n : ProofNode Payload Rule) : nat :=
  match n with
  | InputNode p => 1 + payload_bits p
  | RuleNode r refs p =>
      1 + rule_bits r + payload_bits p
        + nat_bitlength (length refs)
        + references_bitlength refs
  end.

Fixpoint nodes_bitlength
    {Payload Rule}
    (payload_bits : Payload -> nat)
    (rule_bits : Rule -> nat)
    (xs : list (ProofNode Payload Rule)) : nat :=
  match xs with
  | [] => 0
  | n :: xs' => proof_node_bitlength payload_bits rule_bits n
                + nodes_bitlength payload_bits rule_bits xs'
  end.

Definition dag_encoded_bitlength
    {Payload Rule}
    (payload_bits : Payload -> nat)
    (rule_bits : Rule -> nat)
    (H : ProofDAG Payload Rule) : nat :=
  nat_bitlength (length (dag_nodes H))
  + nat_bitlength (dag_sink H)
  + nodes_bitlength payload_bits rule_bits (dag_nodes H).

Definition incremental_dag_bits
    {Payload Rule}
    (payload_bits : Payload -> nat)
    (rule_bits : Rule -> nat)
    (Hin Hout : ProofDAG Payload Rule) : nat :=
  dag_encoded_bitlength payload_bits rule_bits Hout
  - dag_encoded_bitlength payload_bits rule_bits Hin.

Lemma nat_bitlength_positive : forall n, 0 < nat_bitlength n.
Proof. intro n. unfold nat_bitlength. lia. Qed.

Inductive Reachable {Payload Rule} (H : ProofDAG Payload Rule) : nat -> Prop :=
| reachable_sink : Reachable H (dag_sink H)
| reachable_reference : forall i rule refs payload j,
    Reachable H i ->
    nth_error (dag_nodes H) i = Some (RuleNode rule refs payload) ->
    In j refs ->
    Reachable H j.

Definition ReachableNodesCheck
    {Payload Rule}
    (checker : nat -> ProofNode Payload Rule -> bool)
    (H : ProofDAG Payload Rule) : Prop :=
  forall i n,
    Reachable H i ->
    nth_error (dag_nodes H) i = Some n ->
    checker i n = true.

Lemma reachable_indices_in_range
    {Payload Rule} (H : ProofDAG Payload Rule) :
  forall i, Reachable H i -> i < length (dag_nodes H).
Proof.
  intros i Hr.
  induction Hr as
      [| i rule refs payload j Hreach IH Hnth Hin].
  - exact (dag_sink_in_range H).
  - pose proof (dag_backward H i rule refs payload Hnth) as Hb.
    pose proof ((proj1 (@Forall_forall nat (fun j0 => j0 < i) refs)) Hb j Hin) as Hji.
    exact (Nat.lt_trans j i (length (dag_nodes H)) Hji IH).
Qed.

Section ProvenanceCertificate.
  Context {X : MetricPresentation} (E : CertificateEnrichment X).
  Context {Payload Rule : Type}.
  Variable SinkIdentifies : Payload -> code E -> Prop.

  Record ProvenanceCertificate (nu : name X) := {
    pc_ordinary : Certificate E nu;
    pc_history : ProofDAG Payload Rule;
    pc_sink_node : ProofNode Payload Rule;
    pc_sink_lookup :
      nth_error (dag_nodes pc_history) (dag_sink pc_history) = Some pc_sink_node;
    pc_sink_identifies :
      SinkIdentifies (node_payload pc_sink_node) (@cert_code X E nu pc_ordinary)
  }.

  Definition provenance_node_count {nu}
      (c : ProvenanceCertificate nu) : nat :=
    node_count (pc_history c).

  Lemma provenance_has_history {nu}
      (c : ProvenanceCertificate nu) :
    0 < provenance_node_count c.
  Proof. apply proof_dag_nonempty. Qed.

  Lemma provenance_sink_reachable {nu}
      (c : ProvenanceCertificate nu) :
    Reachable (pc_history c) (dag_sink (pc_history c)).
  Proof. apply reachable_sink. Qed.

  Definition provenance_encoded_bitlength
      (code_bits : code E -> nat)
      (bound_bits : R -> nat)
      (evidence_bits : app_witness E -> nat)
      (payload_bits : Payload -> nat)
      (rule_bits : Rule -> nat)
      {nu} (c : ProvenanceCertificate nu) : nat :=
    code_bits (@cert_code X E nu (pc_ordinary c))
    + bound_bits (@cert_bound X E nu (pc_ordinary c))
    + evidence_bits (@cert_evidence X E nu (pc_ordinary c))
    + dag_encoded_bitlength payload_bits rule_bits (pc_history c).

  Definition ProvenanceChecks
      (checker : nat -> ProofNode Payload Rule -> bool)
      {nu} (c : ProvenanceCertificate nu) : Prop :=
    ReachableNodesCheck checker (pc_history c).

End ProvenanceCertificate.
End UELAT_V3_ProofDAG.
