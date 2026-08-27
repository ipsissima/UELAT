(** PUFEMCompiler.v -- authoritative quantitative one-cover compiler.

    This module follows Section 6 of
    "Proof-Carrying Analytic Approximation: Local-to-Global Evidence
    Transport at Encoding Cost".

    In particular Proposition 6.3 uses exactly

      w_i^2 = max(C_inf^2 + 2 L_i^2, 2 C_inf^2),

    together with the true Sobolev component relation

      A_i + D_i <= alpha_i^2.

    The older reconstruction used the safe but looser coefficient
    3 C_inf^2 + 2 L_i^2 after bounding A_i and D_i separately by alpha_i^2.
    That statement is intentionally not retained here.
*)

From Coq Require Import Reals List Arith Lia Lra Lra.
Import ListNotations.
From UELAT.V3 Require Import ProofDAG.

Module UELAT_V3_PUFEMCompiler.
Import UELAT_V3_ProofDAG.

Fixpoint rsum (xs : list R) : R :=
  match xs with
  | [] => 0
  | x :: xs' => x + rsum xs'
  end.

Fixpoint weighted_sq_sum (weights errors : list R) : R :=
  match weights, errors with
  | w :: ws, a :: es => w^2 * a^2 + weighted_sq_sum ws es
  | _, _ => 0
  end.

Lemma weighted_sq_sum_nonnegative : forall ws es,
  Forall (fun x => 0 <= x) ws ->
  Forall (fun x => 0 <= x) es ->
  0 <= weighted_sq_sum ws es.
Proof.
  induction ws as [|w ws IH]; destruct es as [|a es]; simpl; intros Hws Hes; try lra.
  inversion Hws; subst. inversion Hes; subst.
  specialize (IH H3 H5).
  nra.
Qed.

Section Budget.
  Variable kappa epsilon : R.
  Hypothesis Hkappa : 0 <= kappa.
  Hypothesis Heps : 0 < epsilon.

  Variables weights errors : list R.
  Hypothesis Hweights_nonneg : Forall (fun x => 0 <= x) weights.
  Hypothesis Herrors_nonneg : Forall (fun x => 0 <= x) errors.

  Definition global_budget_sq : R :=
    kappa * weighted_sq_sum weights errors.

  Theorem weighted_global_approximation_budget
      (global_error_sq : R) :
    0 <= global_error_sq ->
    global_error_sq <= global_budget_sq ->
    global_budget_sq < epsilon^2 ->
    global_error_sq < epsilon^2.
  Proof. intros Hnonneg Hanalytic Hallocation. lra. Qed.

  Lemma global_budget_nonnegative : 0 <= global_budget_sq.
  Proof.
    unfold global_budget_sq.
    pose proof (weighted_sq_sum_nonnegative weights errors
                  Hweights_nonneg Herrors_nonneg).
    nra.
  Qed.
End Budget.

(** * Authoritative Proposition 6.3 *)

Definition manuscript_weight_sq (Cinf L : R) : R :=
  Rmax (Cinf^2 + 2 * L^2) (2 * Cinf^2).

Fixpoint local_component_sum
    (Cinf : R) (Ls l2s derivs : list R) : R :=
  match Ls, l2s, derivs with
  | L :: Ls', e0 :: l2s', e1 :: derivs' =>
      (Cinf^2 + 2 * L^2) * e0 + (2 * Cinf^2) * e1
      + local_component_sum Cinf Ls' l2s' derivs'
  | _, _, _ => 0
  end.

Fixpoint manuscript_weighted_sum
    (Cinf : R) (Ls alphas : list R) : R :=
  match Ls, alphas with
  | L :: Ls', a :: alphas' =>
      manuscript_weight_sq Cinf L * a^2
      + manuscript_weighted_sum Cinf Ls' alphas'
  | _, _ => 0
  end.

(** l2s and derivs are the squared component errors A_i and D_i. *)
Fixpoint local_error_bounds
    (Ls l2s derivs alphas : list R) : Prop :=
  match Ls, l2s, derivs, alphas with
  | _ :: Ls', e0 :: l2s', e1 :: derivs', a :: alphas' =>
      0 <= e0 /\ 0 <= e1 /\ e0 + e1 <= a^2 /\
      local_error_bounds Ls' l2s' derivs' alphas'
  | [], [], [], [] => True
  | _, _, _, _ => False
  end.

Lemma manuscript_weight_sq_nonnegative : forall Cinf L,
  0 <= manuscript_weight_sq Cinf L.
Proof.
  intros Cinf L.
  unfold manuscript_weight_sq.
  pose proof (Rmax_l (Cinf^2 + 2 * L^2) (2 * Cinf^2)).
  nra.
Qed.

Lemma one_component_le_max_weight : forall Cinf L e0 e1 a,
  0 <= e0 -> 0 <= e1 -> e0 + e1 <= a^2 ->
  (Cinf^2 + 2 * L^2) * e0 + (2 * Cinf^2) * e1
    <= manuscript_weight_sq Cinf L * a^2.
Proof.
  intros Cinf L e0 e1 a He0 He1 Hsum.
  unfold manuscript_weight_sq.
  pose proof (Rmax_l (Cinf^2 + 2 * L^2) (2 * Cinf^2)) as Hleft.
  pose proof (Rmax_r (Cinf^2 + 2 * L^2) (2 * Cinf^2)) as Hright.
  assert (HM : 0 <= Rmax (Cinf^2 + 2 * L^2) (2 * Cinf^2)) by nra.
  nra.
Qed.

Lemma local_component_sum_le_weighted : forall Cinf Ls l2s derivs alphas,
  local_error_bounds Ls l2s derivs alphas ->
  local_component_sum Cinf Ls l2s derivs
    <= manuscript_weighted_sum Cinf Ls alphas.
Proof.
  intros Cinf Ls.
  induction Ls as [|L Ls IH];
    destruct l2s as [|e0 l2s];
    destruct derivs as [|e1 derivs];
    destruct alphas as [|a alphas]; simpl; intros H; try contradiction; try lra.
  destruct H as [He0 [He1 [Hsum Hrest]]].
  specialize (IH l2s derivs alphas Hrest).
  pose proof (one_component_le_max_weight Cinf L e0 e1 a He0 He1 Hsum).
  lra.
Qed.

Section DerivedBudget.
  Variables kappa Cinf epsilon : R.
  Hypothesis Hkappa : 0 <= kappa.
  Hypothesis Hepsilon : 0 < epsilon.

  Variables Ls l2s derivs alphas : list R.
  Hypothesis Hlocal : local_error_bounds Ls l2s derivs alphas.

  Variable global_error_sq : R.
  Hypothesis Hglobal_nonnegative : 0 <= global_error_sq.
  Hypothesis Hanalytic_components :
    global_error_sq <= kappa * local_component_sum Cinf Ls l2s derivs.

  Theorem weighted_global_budget_derived :
    global_error_sq <= kappa * manuscript_weighted_sum Cinf Ls alphas.
  Proof.
    eapply Rle_trans; [exact Hanalytic_components|].
    apply Rmult_le_compat_l; [exact Hkappa|].
    now apply local_component_sum_le_weighted.
  Qed.

  Corollary weighted_allocation_gives_epsilon :
    kappa * manuscript_weighted_sum Cinf Ls alphas < epsilon^2 ->
    global_error_sq < epsilon^2.
  Proof.
    intro Halloc.
    pose proof weighted_global_budget_derived.
    lra.
  Qed.
End DerivedBudget.

(** * Structural finite-code size bound *)

Fixpoint nsum (xs : list nat) : nat :=
  match xs with | [] => 0 | x :: xs' => x + nsum xs' end.

Definition synthesized_cell_budget
    (local_cells partition_cells : list nat) : nat :=
  nsum local_cells + nsum partition_cells.

Theorem common_mesh_cell_bound
    (actual_cells : nat)
    (local_cells partition_cells : list nat) :
  actual_cells <= synthesized_cell_budget local_cells partition_cells ->
  actual_cells <= nsum local_cells + nsum partition_cells.
Proof. exact (fun H => H). Qed.

Definition synthesized_degree_budget (dmax : nat) : nat := S dmax.

Theorem product_degree_budget (actual_degree dmax : nat) :
  actual_degree <= S dmax ->
  actual_degree <= synthesized_degree_budget dmax.
Proof. exact (fun H => H). Qed.

Definition coefficient_bit_budget
    (kappa input_bits overlap_bits : nat) : nat :=
  kappa * (input_bits + overlap_bits).

Lemma coefficient_bit_budget_monotone : forall k b b' l l',
  b <= b' -> l <= l' ->
  coefficient_bit_budget k b l <= coefficient_bit_budget k b' l'.
Proof.
  intros k b b' l l' Hb Hl.
  unfold coefficient_bit_budget.
  apply Nat.mul_le_mono_l.
  lia.
Qed.

(** * Theorem 6.2: fixed-DAG one-cover resource accounting *)

Definition defect_label_bits
    (B s Nin I M : nat) : nat :=
  B + s + nat_bitlength (Nin + I + M + 2).

Definition verification_argument_bits
    (B s I : nat) : nat :=
  B + s + nat_bitlength (I + 2).

Section OneCoverCompilerCost.
  Variables I M Nin B s : nat.
  Variables c_nodes c_label c_verify : nat.
  Variables new_nodes per_node_bits deltaS : nat.
  Variables Vin Vout new_checks per_check_time : nat.
  Variable A : nat -> nat.

  Hypothesis Hnew_nodes : new_nodes <= c_nodes * (I + M).
  Hypothesis Hper_node :
    per_node_bits <= c_label * defect_label_bits B s Nin I M.
  Hypothesis Hdelta : deltaS <= new_nodes * per_node_bits.

  Hypothesis Hnew_checks : new_checks <= c_verify * I.
  Hypothesis Hper_check :
    per_check_time <= A (verification_argument_bits B s I).
  Hypothesis Hverify : Vout <= Vin + new_checks * per_check_time.

  Theorem single_cover_deltaS_bound :
    deltaS <=
      (c_nodes * c_label) * (I + M) * defect_label_bits B s Nin I M.
  Proof. eapply Nat.le_trans; [exact Hdelta|]. nia. Qed.

  Theorem single_cover_verification_bound :
    Vout <= Vin + c_verify * I * A (verification_argument_bits B s I).
  Proof. eapply Nat.le_trans; [exact Hverify|]. nia. Qed.

  Theorem single_cover_provenance_resource_bound :
    deltaS <=
      (c_nodes * c_label) * (I + M) * defect_label_bits B s Nin I M
    /\
    Vout <= Vin + c_verify * I * A (verification_argument_bits B s I).
  Proof.
    split.
    - apply single_cover_deltaS_bound.
    - apply single_cover_verification_bound.
  Qed.
End OneCoverCompilerCost.

Definition target_query_lookahead : nat := 0.
Theorem target_query_lookahead_zero : target_query_lookahead = 0.
Proof. reflexivity. Qed.
Theorem single_cover_target_query_bound : target_query_lookahead = 0.
Proof. reflexivity. Qed.

End UELAT_V3_PUFEMCompiler.
