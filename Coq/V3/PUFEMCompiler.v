(** PUFEMCompiler.v -- authoritative quantitative one-cover compiler.

    This version follows the 35-page manuscript
      Proof-Carrying Analytic Approximation:
      Local-to-Global Evidence Transport at Encoding Cost.

    In particular Proposition 6.3 uses

      w_i^2 = max { C_inf^2 + 2 L_i^2, 2 C_inf^2 }

    together with the genuine W^{1,2} local budget

      A_i + D_i <= alpha_i^2,

    where A_i = ||e_i||_{L2}^2 and D_i = ||e_i'||_{L2}^2.
    The older reconstructed interface that assumed A_i <= alpha_i^2 and
    D_i <= alpha_i^2 separately led only to the looser coefficient
    3 C_inf^2 + 2 L_i^2 and is superseded for current-paper correspondence.
*)

From Coq Require Import Reals List Arith Lia Lra Nra.
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
  Proof. intros; lra. Qed.

End Budget.

(** Manuscript Proposition 6.3 component expression. *)
Fixpoint local_component_sum
    (Cinf : R) (Ls l2s derivs : list R) : R :=
  match Ls, l2s, derivs with
  | L :: Ls', A :: l2s', D :: derivs' =>
      Cinf^2 * A + 2 * (L^2 * A + Cinf^2 * D)
      + local_component_sum Cinf Ls' l2s' derivs'
  | _, _, _ => 0
  end.

Definition manuscript_weight_sq (Cinf L : R) : R :=
  Rmax (Cinf^2 + 2 * L^2) (2 * Cinf^2).

Fixpoint manuscript_weighted_sum
    (Cinf : R) (Ls alphas : list R) : R :=
  match Ls, alphas with
  | L :: Ls', a :: alphas' =>
      manuscript_weight_sq Cinf L * a^2
      + manuscript_weighted_sum Cinf Ls' alphas'
  | _, _ => 0
  end.

(** This is the exact local information used in the paper:
    A_i,D_i are squared component norms and their sum is the squared W12 norm. *)
Fixpoint local_w12_error_budget
    (l2s derivs alphas : list R) : Prop :=
  match l2s, derivs, alphas with
  | A :: l2s', D :: derivs', a :: alphas' =>
      0 <= A /\ 0 <= D /\ A + D <= a^2 /\
      local_w12_error_budget l2s' derivs' alphas'
  | [], [], [] => True
  | _, _, _ => False
  end.

Lemma manuscript_weight_ge_l2 : forall Cinf L,
  Cinf^2 + 2 * L^2 <= manuscript_weight_sq Cinf L.
Proof.
  intros Cinf L.
  unfold manuscript_weight_sq, Rmax.
  destruct (Rle_dec (Cinf ^ 2 + 2 * L ^ 2) (2 * Cinf ^ 2)); lra.
Qed.

Lemma manuscript_weight_ge_deriv : forall Cinf L,
  2 * Cinf^2 <= manuscript_weight_sq Cinf L.
Proof.
  intros Cinf L.
  unfold manuscript_weight_sq, Rmax.
  destruct (Rle_dec (Cinf ^ 2 + 2 * L ^ 2) (2 * Cinf ^ 2)); lra.
Qed.

Lemma local_component_term_le_authoritative_weight :
  forall Cinf L A D a,
    0 <= A -> 0 <= D -> A + D <= a^2 ->
    Cinf^2 * A + 2 * (L^2 * A + Cinf^2 * D)
      <= manuscript_weight_sq Cinf L * a^2.
Proof.
  intros Cinf L A D a HA HD Hsum.
  pose proof (manuscript_weight_ge_l2 Cinf L) as H0.
  pose proof (manuscript_weight_ge_deriv Cinf L) as H1.
  assert (Hw : 0 <= manuscript_weight_sq Cinf L).
  {
    eapply Rle_trans; [|exact H1]. nra.
  }
  replace (Cinf^2 * A + 2 * (L^2 * A + Cinf^2 * D))
    with ((Cinf^2 + 2 * L^2) * A + (2 * Cinf^2) * D) by ring.
  nra.
Qed.

Lemma local_component_sum_le_authoritative_weighted :
  forall Cinf Ls l2s derivs alphas,
    local_w12_error_budget l2s derivs alphas ->
    length Ls = length alphas ->
    local_component_sum Cinf Ls l2s derivs
      <= manuscript_weighted_sum Cinf Ls alphas.
Proof.
  intros Cinf Ls.
  induction Ls as [|L Ls IH];
    destruct l2s as [|A l2s];
    destruct derivs as [|D derivs];
    destruct alphas as [|a alphas]; simpl; intros Hbudget Hlen;
    try contradiction; try discriminate; try lra.
  destruct Hbudget as [HA [HD [Hsum Hrest]]].
  inversion Hlen as [Htail].
  specialize (IH l2s derivs alphas Hrest Htail).
  pose proof (local_component_term_le_authoritative_weight
                Cinf L A D a HA HD Hsum) as Hterm.
  lra.
Qed.

Section DerivedBudget.
  Variables kappa Cinf epsilon : R.
  Hypothesis Hkappa : 0 <= kappa.
  Hypothesis Hepsilon : 0 < epsilon.

  Variables Ls l2s derivs alphas : list R.
  Hypothesis Hlocal : local_w12_error_budget l2s derivs alphas.
  Hypothesis Hlength : length Ls = length alphas.

  Variable global_error_sq : R.
  Hypothesis Hglobal_nonnegative : 0 <= global_error_sq.
  Hypothesis Hanalytic_components :
    global_error_sq <= kappa * local_component_sum Cinf Ls l2s derivs.

  Theorem proposition_6_3_weighted_global_bound :
    global_error_sq <= kappa * manuscript_weighted_sum Cinf Ls alphas.
  Proof.
    eapply Rle_trans; [exact Hanalytic_components|].
    apply Rmult_le_compat_l; [exact Hkappa|].
    now apply local_component_sum_le_authoritative_weighted.
  Qed.

  Corollary proposition_6_3_epsilon_allocation :
    kappa * manuscript_weighted_sum Cinf Ls alphas < epsilon^2 ->
    global_error_sq < epsilon^2.
  Proof.
    intro Halloc.
    pose proof proposition_6_3_weighted_global_bound.
    lra.
  Qed.
End DerivedBudget.

(** Theorem 6.2: fixed-DAG one-cover resource accounting. *)
Definition defect_label_bits
    (B s Nin I M : nat) : nat :=
  B + s + nat_bitlength (Nin + I + M + 2).

Definition verification_argument_bits
    (B s I M : nat) : nat :=
  B + s + nat_bitlength (I + M + 2).

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

  Hypothesis Hnew_checks : new_checks <= c_verify * (I + M).
  Hypothesis Hper_check :
    per_check_time <= A (verification_argument_bits B s I M).
  Hypothesis Hverify : Vout <= Vin + new_checks * per_check_time.

  Theorem theorem_6_2_deltaS_bound :
    deltaS <=
      (c_nodes * c_label) * (I + M) * defect_label_bits B s Nin I M.
  Proof. eapply Nat.le_trans; [exact Hdelta|]. nia. Qed.

  Theorem theorem_6_2_verification_bound :
    Vout <=
      Vin + c_verify * (I + M) * A (verification_argument_bits B s I M).
  Proof. eapply Nat.le_trans; [exact Hverify|]. nia. Qed.
End OneCoverCompilerCost.

Definition target_query_lookahead : nat := 0.
Theorem theorem_6_2_target_query_zero : target_query_lookahead = 0.
Proof. reflexivity. Qed.

End UELAT_V3_PUFEMCompiler.
