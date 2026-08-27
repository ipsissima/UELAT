(** ProofDAGEncodingAppend.v -- encoded size of append-only genealogy.

    ProofDAGBuilder proves structural sharing.  This module connects that
    operation to the fixed binary encoding of Definition 6.1.  Appending one
    node adds exactly its node encoding plus only the changed finite DAG header;
    the old node payload is not copied.
*)

From Coq Require Import List Arith Lia Nia.
Import ListNotations.
From UELAT.V3 Require Import ProofDAG ProofDAGBuilder.

Module UELAT_V3_ProofDAGEncodingAppend.
Import UELAT_V3_ProofDAG.
Import UELAT_V3_ProofDAGBuilder.

Section Encoding.
  Context {Payload Rule : Type}.
  Variable payload_bits : Payload -> nat.
  Variable rule_bits : Rule -> nat.

  Lemma nodes_bitlength_app : forall xs ys,
    nodes_bitlength payload_bits rule_bits (xs ++ ys)
      = nodes_bitlength payload_bits rule_bits xs
        + nodes_bitlength payload_bits rule_bits ys.
  Proof.
    intros xs ys. induction xs as [|x xs IH]; simpl; lia.
  Qed.

  Lemma singleton_node_bitlength : forall n,
    nodes_bitlength payload_bits rule_bits [n]
      = proof_node_bitlength payload_bits rule_bits n.
  Proof. reflexivity. Qed.

  Theorem append_rule_encoded_size_formula :
    forall (H : ProofDAG Payload Rule) r refs p Hrefs,
    dag_encoded_bitlength payload_bits rule_bits
      (append_rule H r refs p Hrefs)
    = nat_bitlength (S (length (dag_nodes H)))
      + nat_bitlength (length (dag_nodes H))
      + nodes_bitlength payload_bits rule_bits (dag_nodes H)
      + proof_node_bitlength payload_bits rule_bits
          (RuleNode r refs p).
  Proof.
    intros H r refs p Hrefs.
    unfold dag_encoded_bitlength, append_rule. simpl.
    rewrite app_length. simpl.
    rewrite nodes_bitlength_app. simpl.
    lia.
  Qed.

  (** Safe incremental envelope.  The previous encoding already contains its
      old headers, so adding the two new header lengths is conservative. *)
  Theorem append_rule_encoded_size_bound :
    forall (H : ProofDAG Payload Rule) r refs p Hrefs,
    dag_encoded_bitlength payload_bits rule_bits
      (append_rule H r refs p Hrefs)
    <= dag_encoded_bitlength payload_bits rule_bits H
       + proof_node_bitlength payload_bits rule_bits (RuleNode r refs p)
       + nat_bitlength (S (length (dag_nodes H)))
       + nat_bitlength (length (dag_nodes H)).
  Proof.
    intros H r refs p Hrefs.
    rewrite append_rule_encoded_size_formula.
    unfold dag_encoded_bitlength.
    pose proof (nat_bitlength_positive (dag_sink H)).
    pose proof (nat_bitlength_positive (length (dag_nodes H))).
    nia.
  Qed.

  (** If both the new node and the two current header references fit a common
      bit envelope B, one append costs at most 3B beyond the previous DAG. *)
  Theorem append_rule_uniform_bit_bound :
    forall (H : ProofDAG Payload Rule) r refs p Hrefs B,
      proof_node_bitlength payload_bits rule_bits (RuleNode r refs p) <= B ->
      nat_bitlength (S (length (dag_nodes H))) <= B ->
      nat_bitlength (length (dag_nodes H)) <= B ->
      dag_encoded_bitlength payload_bits rule_bits
        (append_rule H r refs p Hrefs)
      <= dag_encoded_bitlength payload_bits rule_bits H + 3 * B.
  Proof.
    intros H r refs p Hrefs B Hnode Hnew Hold.
    pose proof (append_rule_encoded_size_bound H r refs p Hrefs).
    nia.
  Qed.

End Encoding.

End UELAT_V3_ProofDAGEncodingAppend.
