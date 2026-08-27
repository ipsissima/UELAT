(** ProofDAGBuilder.v -- append-only persistent proof genealogy.

    The refinement compiler extends a history by shared reference rather than
    copying previous nodes. This file appends one backward-referencing rule node,
    preserves the old node list as a literal prefix, and makes the new node the sink.
*)

From Coq Require Import List Arith Lia.
Import ListNotations.
From UELAT.V3 Require Import ProofDAG.

Module UELAT_V3_ProofDAGBuilder.
Import UELAT_V3_ProofDAG.

Section Builder.
  Context {Payload Rule : Type}.

  Definition dag_prefix (H H' : ProofDAG Payload Rule) : Prop :=
    exists tail, dag_nodes H' = dag_nodes H ++ tail.

  Definition append_rule
      (H : ProofDAG Payload Rule)
      (rule : Rule) (refs : list nat) (payload : Payload)
      (Hrefs : Forall (fun j => j < length (dag_nodes H)) refs) :
      ProofDAG Payload Rule.
  Proof.
    refine {| dag_nodes := dag_nodes H ++ [RuleNode rule refs payload];
              dag_sink := length (dag_nodes H) |}.
    - rewrite app_length. simpl. lia.
    - intros i r rs p Hnth.
      destruct (lt_dec i (length (dag_nodes H))) as [Hold|Hnew].
      + rewrite nth_error_app1 in Hnth by exact Hold.
        eapply dag_backward; eauto.
      + assert (Hi : i < length (dag_nodes H ++ [RuleNode rule refs payload])).
        { apply (proj1 (nth_error_Some _ i)). rewrite Hnth. discriminate. }
        rewrite app_length in Hi. simpl in Hi.
        assert (Heq : i = length (dag_nodes H)) by lia.
        subst i.
        rewrite nth_error_app2 in Hnth by lia.
        simpl in Hnth. inversion Hnth; subst. exact Hrefs.
  Defined.

  Theorem append_rule_is_persistent : forall H rule refs payload Hrefs,
    dag_prefix H (append_rule H rule refs payload Hrefs).
  Proof. intros. unfold dag_prefix, append_rule. simpl. eexists. reflexivity. Qed.

  Theorem append_rule_sink_is_new_node : forall H rule refs payload Hrefs,
    nth_error (dag_nodes (append_rule H rule refs payload Hrefs))
      (dag_sink (append_rule H rule refs payload Hrefs))
      = Some (RuleNode rule refs payload).
  Proof.
    intros. unfold append_rule. simpl.
    rewrite nth_error_app2 by lia. simpl. reflexivity.
  Qed.

  Theorem append_rule_adds_one_node : forall H rule refs payload Hrefs,
    node_count (append_rule H rule refs payload Hrefs) = S (node_count H).
  Proof.
    intros. unfold node_count, append_rule. simpl.
    rewrite app_length. simpl. lia.
  Qed.

  Theorem old_nodes_keep_indices : forall H rule refs payload Hrefs i node,
    nth_error (dag_nodes H) i = Some node ->
    nth_error (dag_nodes (append_rule H rule refs payload Hrefs)) i = Some node.
  Proof.
    intros H rule refs payload Hrefs i node Hnth.
    unfold append_rule. simpl.
    rewrite nth_error_app1.
    - exact Hnth.
    - apply (proj1 (nth_error_Some _ i)). rewrite Hnth. discriminate.
  Qed.
End Builder.

End UELAT_V3_ProofDAGBuilder.
