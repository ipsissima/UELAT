(** DescentFailureModes.v -- explicit failure modes for v3 Section 7.

    These elementary counterexamples isolate the two mechanisms identified by
    the manuscript as necessary for order-neutral genealogy: geometric growth
    of the ordinary finite representation and a uniform local proof-payload
    scale.  They are resource counterexamples, not analytic counterexamples to
    PUFEM itself.
*)

From Coq Require Import Arith Lia.
From UELAT.V3 Require Import OrderNeutralDescent.

Module UELAT_V3_DescentFailureModes.
Import UELAT_V3_OrderNeutralDescent.

Definition constant_baseline (_ : nat) : nat := 1.
Definition unit_payload (_ : nat) : nat := 1.
Definition growing_payload (n : nat) : nat := S n.

Lemma cumulative_unit_payload : forall n,
  nsum_upto unit_payload n = S n.
Proof.
  induction n; simpl; lia.
Qed.

Theorem no_uniform_order_neutrality_without_geometric_growth :
  forall C, exists n,
    nsum_upto unit_payload n > C * constant_baseline n.
Proof.
  intro C. exists C.
  rewrite cumulative_unit_payload.
  unfold constant_baseline. lia.
Qed.

Theorem no_uniform_bound_for_oversized_local_payload :
  forall C, exists n,
    growing_payload n > C * constant_baseline n.
Proof.
  intro C. exists C.
  unfold growing_payload, constant_baseline. lia.
Qed.

End UELAT_V3_DescentFailureModes.
