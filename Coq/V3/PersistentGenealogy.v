(** PersistentGenealogy.v -- executable shared-history skeleton for H5.

    The manuscript requires H_{n+1} to contain H_n by shared reference, not by
    copying.  Starting from one input leaf, this module appends bounded-arity
    rule nodes whose default reference is the previous sink.  The resulting
    node list is persistent and grows by exactly the number of new steps.
*)

From Coq Require Import List Arith Lia.
Import ListNotations.
From UELAT.V3 Require Import ProofDAG ProofDAGBuilder.

Module UELAT_V3_PersistentGenealogy.
Import UELAT_V3_ProofDAG.
Import UELAT_V3_ProofDAGBuilder.

Section Genealogy.
  Context {Payload Rule : Type}.

  Definition singleton_input (payload : Payload) : ProofDAG Payload Rule.
  Proof.
    refine {| dag_nodes := [InputNode payload]; dag_sink := 0 |}.
    - simpl. lia.
    - intros i r refs p Hnth.
      destruct i; simpl in Hnth; discriminate.
  Defined.

  Theorem singleton_input_sink : forall payload,
    nth_error (dag_nodes (singleton_input payload))
      (dag_sink (singleton_input payload)) = Some (InputNode payload).
  Proof. reflexivity. Qed.

  Definition append_to_sink
      (H : ProofDAG Payload Rule) (rule : Rule) (payload : Payload) :
      ProofDAG Payload Rule :=
    append_rule H rule [dag_sink H] payload
      (Forall_cons _ (dag_sink_in_range H) (Forall_nil _)).

  Theorem append_to_sink_persistent : forall H rule payload,
    dag_prefix H (append_to_sink H rule payload).
  Proof.
    intros. unfold append_to_sink.
    apply append_rule_is_persistent.
  Qed.

  Theorem append_to_sink_adds_one : forall H rule payload,
    node_count (append_to_sink H rule payload) = S (node_count H).
  Proof.
    intros. unfold append_to_sink.
    apply append_rule_adds_one_node.
  Qed.

  Fixpoint append_steps
      (H : ProofDAG Payload Rule)
      (steps : list (Rule * Payload)) : ProofDAG Payload Rule :=
    match steps with
    | [] => H
    | (r,p) :: rest => append_steps (append_to_sink H r p) rest
    end.

  Theorem append_steps_node_count : forall steps H,
    node_count (append_steps H steps) = node_count H + length steps.
  Proof.
    induction steps as [|[r p] rest IH]; intros H; simpl.
    - lia.
    - rewrite IH.
      rewrite append_to_sink_adds_one.
      simpl. lia.
  Qed.

  Theorem append_steps_persistent : forall steps H,
    exists tail,
      dag_nodes (append_steps H steps) = dag_nodes H ++ tail.
  Proof.
    induction steps as [|[r p] rest IH]; intros H; simpl.
    - exists []. rewrite app_nil_r. reflexivity.
    - destruct (IH (append_to_sink H r p)) as [tail Htail].
      unfold append_to_sink in Htail.
      simpl in Htail.
      rewrite Htail.
      exists (RuleNode r [dag_sink H] p :: tail).
      rewrite <- app_assoc. reflexivity.
  Qed.

  Definition compile_refinement_level := append_steps.

  Theorem compile_refinement_level_shares_old_history : forall H steps,
    dag_prefix H (compile_refinement_level H steps).
  Proof.
    intros H steps.
    unfold dag_prefix, compile_refinement_level.
    apply append_steps_persistent.
  Qed.

End Genealogy.

End UELAT_V3_PersistentGenealogy.
