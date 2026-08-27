(** RefinementGenealogyCompiler.v -- concrete H5 persistence across levels.

    Given a base proof leaf and a finite list of new proof steps for each
    refinement level, the history at level n is obtained by append-only
    compilation of levels 0..n.  The previous history is literally a prefix of
    the next history, so shared ancestry is not copied.
*)

From Coq Require Import List Arith Lia.
Import ListNotations.
From UELAT.V3 Require Import ProofDAG ProofDAGBuilder PersistentGenealogy.

Module UELAT_V3_RefinementGenealogyCompiler.
Import UELAT_V3_ProofDAG.
Import UELAT_V3_ProofDAGBuilder.
Import UELAT_V3_PersistentGenealogy.

Section Compiler.
  Context {Payload Rule : Type}.

  Variable base_payload : Payload.
  Variable level_steps : nat -> list (Rule * Payload).

  Fixpoint history (n : nat) : ProofDAG Payload Rule :=
    match n with
    | O => compile_refinement_level (singleton_input base_payload) (level_steps 0)
    | S k => compile_refinement_level (history k) (level_steps (S k))
    end.

  Theorem history_persistent : forall n,
    dag_prefix (history n) (history (S n)).
  Proof.
    intro n. simpl.
    apply compile_refinement_level_shares_old_history.
  Qed.

  Fixpoint steps_through (n : nat) : nat :=
    match n with
    | O => length (level_steps 0)
    | S k => steps_through k + length (level_steps (S k))
    end.

  Theorem history_node_count : forall n,
    node_count (history n) = 1 + steps_through n.
  Proof.
    induction n as [|n IH].
    - simpl history. rewrite append_steps_node_count.
      unfold node_count, singleton_input. simpl. lia.
    - simpl history. rewrite append_steps_node_count.
      rewrite IH. simpl steps_through. lia.
  Qed.

  Theorem history_contains_base : forall n,
    exists tail,
      dag_nodes (history n) = [InputNode base_payload] ++ tail.
  Proof.
    induction n as [|n IH].
    - simpl history.
      destruct (append_steps_persistent (level_steps 0)
                  (singleton_input base_payload)) as [tail Htail].
      simpl in Htail. now exists tail.
    - simpl history.
      destruct IH as [oldtail Hold].
      destruct (append_steps_persistent (level_steps (S n)) (history n))
        as [newtail Hnew].
      rewrite Hnew, Hold.
      exists (oldtail ++ newtail).
      rewrite app_assoc. reflexivity.
  Qed.

End Compiler.

End UELAT_V3_RefinementGenealogyCompiler.
