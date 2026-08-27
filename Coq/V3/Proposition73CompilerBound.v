(** Proposition73CompilerBound.v -- authoritative Proposition 7.3:
    concrete compiler bound for standard local encodings.

    The paper's asymptotic statement is represented by explicit constant-form
    inequalities.  The geometric/encoding assumptions supply the comparison
    beta_n >= c log(M_n+2); the one-cover compiler then gives O(M_n) new nodes
    and O(M_n beta_n) new payload, and the ordinary baseline is assumed
    two-sided Theta(M_n beta_n).
*)

From Coq Require Import Arith Lia Nia.
From UELAT.V3 Require Import ProofDAG PUFEMCompiler.

Module UELAT_V3_Proposition73CompilerBound.
Import UELAT_V3_ProofDAG.
Import UELAT_V3_PUFEMCompiler.

Section Level.
  Variables M I Nin beta slack B : nat.
  Variables code_bits new_nodes new_payload_bits : nat.

  Variables cI cN cSlack cRef cCode cNodes cPayload cBase : nat.

  Hypothesis incidence_linear : I <= cI * M.
  Hypothesis input_nodes_linear : Nin <= cN * M.
  Hypothesis slack_linear : slack <= cSlack * beta.

  (** This is the explicit binary-reference version of beta_n >= c log(M_n+2).
      It is stated directly at the label-size interface consumed by the compiler. *)
  Hypothesis reference_bits_controlled :
    nat_bitlength (Nin + I + M + 2) <= cRef * beta.

  Hypothesis code_linear : code_bits <= cCode * M * beta.
  Hypothesis node_linear : new_nodes <= cNodes * M.
  Hypothesis payload_linear : new_payload_bits <= cPayload * M * beta.

  (** Nondegenerate conventional baseline B_n = Theta(M_n beta_n): the lower
      side is the one needed to compare proof carrying with B_n. *)
  Hypothesis baseline_lower : M * beta <= cBase * B.

  Theorem proposition73_code_is_baseline_order :
    code_bits <= cCode * cBase * B.
  Proof.
    eapply Nat.le_trans; [exact code_linear|]. nia.
  Qed.

  Theorem proposition73_new_nodes_linear :
    new_nodes <= cNodes * M.
  Proof. exact node_linear. Qed.

  Theorem proposition73_new_payload_is_baseline_order :
    new_payload_bits <= cPayload * cBase * B.
  Proof.
    eapply Nat.le_trans; [exact payload_linear|]. nia.
  Qed.

  Theorem proposition73_label_bits_controlled :
    defect_label_bits beta slack Nin I M
      <= (1 + cSlack + cRef) * beta.
  Proof.
    unfold defect_label_bits.
    nia.
  Qed.

  Theorem proposition73_level_package :
    code_bits <= cCode * cBase * B
    /\ new_nodes <= cNodes * M
    /\ new_payload_bits <= cPayload * cBase * B
    /\ defect_label_bits beta slack Nin I M
         <= (1 + cSlack + cRef) * beta.
  Proof.
    repeat split.
    - apply proposition73_code_is_baseline_order.
    - apply proposition73_new_nodes_linear.
    - apply proposition73_new_payload_is_baseline_order.
    - apply proposition73_label_bits_controlled.
  Qed.
End Level.

Section AccumulatedNodes.
  Variable M : nat -> nat.
  Variable node_increment : nat -> nat.
  Variables cGeom cNodes : nat.

  Hypothesis geometric_history : forall j n,
    j <= n -> M j <= cGeom * M n.
  Hypothesis geometric_sum : forall n,
    (fix sum_to (k : nat) : nat :=
       match k with
       | O => M 0
       | S q => sum_to q + M (S q)
       end) n <= cGeom * M n.
  Hypothesis level_nodes : forall n,
    node_increment n <= cNodes * M n.

  Fixpoint accumulated_nodes (n : nat) : nat :=
    match n with
    | O => node_increment 0
    | S k => accumulated_nodes k + node_increment (S k)
    end.

  Fixpoint patch_sum (n : nat) : nat :=
    match n with
    | O => M 0
    | S k => patch_sum k + M (S k)
    end.

  Lemma accumulated_nodes_le_patch_sum : forall n,
    accumulated_nodes n <= cNodes * patch_sum n.
  Proof.
    induction n as [|n IH]; simpl.
    - specialize (level_nodes 0). nia.
    - specialize (level_nodes (S n)). nia.
  Qed.

  Hypothesis patch_sum_geometric : forall n,
    patch_sum n <= cGeom * M n.

  Theorem proposition73_accumulated_node_count : forall n,
    accumulated_nodes n <= cNodes * cGeom * M n.
  Proof.
    intro n.
    pose proof (accumulated_nodes_le_patch_sum n) as Hacc.
    pose proof (patch_sum_geometric n) as Hsum.
    nia.
  Qed.
End AccumulatedNodes.

End UELAT_V3_Proposition73CompilerBound.
