(** GlobalCodeSize.v -- fixed-encoding form of authoritative Proposition 6.4.

    Packages common-mesh cell count, one-degree rise under PWL multiplication,
    and safe bounded-overlap raw numerator/denominator bit growth under the
    explicitly fixed binary-rational encoding.
*)

From Coq Require Import Arith Lia.
From UELAT.V3 Require Import PUFEMCompiler RationalBitBudget.

Module UELAT_V3_GlobalCodeSize.
Import UELAT_V3_PUFEMCompiler.
Import UELAT_V3_RationalBitBudget.

Section CodeSize.
  Variables actual_cells dmax actual_degree : nat.
  Variables local_cells partition_cells : list nat.
  Variables B kappa : nat.
  Hypothesis Hcells :
    actual_cells <= synthesized_cell_budget local_cells partition_cells.
  Hypothesis Hdegree : actual_degree <= S dmax.
  Hypothesis Hkappa : 0 < kappa.

  Definition coefficient_output_budget : nat :=
    kappa * (B + overlap_log_budget (kappa - 1)).

  Theorem global_rational_code_size_package :
    actual_cells <= nsum local_cells + nsum partition_cells
    /\ actual_degree <= S dmax
    /\ sum_budget B (kappa - 1) <= coefficient_output_budget.
  Proof.
    split.
    - exact Hcells.
    - split; [exact Hdegree|].
      unfold coefficient_output_budget.
      pose proof (manuscript_style_overlap_budget B (kappa - 1)) as Hbits.
      replace (S (kappa - 1)) with kappa in Hbits by lia.
      exact Hbits.
  Qed.
End CodeSize.

End UELAT_V3_GlobalCodeSize.
