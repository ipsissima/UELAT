(** RationalPUFEM.v -- authoritative rational PUFEM structural/defect core. *)

From Coq Require Import Reals List Lra Lra.
Import ListNotations.
Local Open Scope R_scope.

Module UELAT_V3_RationalPUFEM.

Record PartitionDatum := {
  partition_sup_bound : R;
  partition_deriv_bound : R;
  partition_sup_nonnegative : 0 <= partition_sup_bound;
  partition_deriv_nonnegative : 0 <= partition_deriv_bound
}.

Record RationalPOUStructure := {
  pou_terms : list PartitionDatum;
  pou_overlap : nat;
  pou_overlap_positive : (0 < pou_overlap)%nat
}.

Definition multiplier_weight (psi : PartitionDatum) : R :=
  Rmax
    (partition_sup_bound psi ^ 2 + 2 * partition_deriv_bound psi ^ 2)
    (2 * partition_sup_bound psi ^ 2).

Lemma multiplier_weight_nonnegative : forall psi,
  0 <= multiplier_weight psi.
Proof.
  intro psi. unfold multiplier_weight.
  pose proof (Rmax_l
    (partition_sup_bound psi ^ 2 + 2 * partition_deriv_bound psi ^ 2)
    (2 * partition_sup_bound psi ^ 2)).
  nra.
Qed.

Definition synthesis_weight_list (P : RationalPOUStructure) : list R :=
  map multiplier_weight (pou_terms P).

Lemma synthesis_weights_nonnegative : forall P,
  Forall (fun x => 0 <= x) (synthesis_weight_list P).
Proof.
  intros P. unfold synthesis_weight_list.
  induction (pou_terms P) as [|a xs IH]; simpl.
  - constructor.
  - constructor; [apply multiplier_weight_nonnegative|exact IH].
Qed.

Section MultiplierEstimate.
  Variables Cinf L delta0 delta1 : R.
  Hypothesis HCinf : 0 <= Cinf.
  Hypothesis HL : 0 <= L.
  Hypothesis Hd0 : 0 <= delta0.
  Hypothesis Hd1 : 0 <= delta1.

  Variables l2_product deriv_product : R.
  Hypothesis Hl2_nonnegative : 0 <= l2_product.
  Hypothesis Hderiv_nonnegative : 0 <= deriv_product.
  Hypothesis Hl2_product : l2_product <= Cinf * delta0.
  Hypothesis Hproduct_rule :
    deriv_product <= L * delta0 + Cinf * delta1.

  Theorem multiplier_l2_squared :
    l2_product^2 <= Cinf^2 * delta0^2.
  Proof. nra. Qed.

  Theorem multiplier_derivative_squared :
    deriv_product^2
      <= 2 * L^2 * delta0^2 + 2 * Cinf^2 * delta1^2.
  Proof.
    assert (Hsq : deriv_product^2
              <= (L * delta0 + Cinf * delta1)^2) by nra.
    assert (Hident :
      2 * L^2 * delta0^2 + 2 * Cinf^2 * delta1^2
      = (L * delta0 + Cinf * delta1)^2
        + (L * delta0 - Cinf * delta1)^2) by ring.
    eapply Rle_trans; [exact Hsq|].
    rewrite Hident.
    pose proof (Rle_0_sqr (L * delta0 - Cinf * delta1)).
    nra.
  Qed.

  Theorem multiplier_w12_squared :
    l2_product^2 + deriv_product^2
      <= (Cinf^2 + 2 * L^2) * delta0^2
         + 2 * Cinf^2 * delta1^2.
  Proof.
    pose proof multiplier_l2_squared.
    pose proof multiplier_derivative_squared.
    nra.
  Qed.

  Theorem multiplier_w12_by_max_weight :
    delta0^2 + delta1^2 >= 0 ->
    l2_product^2 + deriv_product^2
      <= Rmax (Cinf^2 + 2 * L^2) (2 * Cinf^2)
           * (delta0^2 + delta1^2).
  Proof.
    intro Hsum.
    pose proof multiplier_w12_squared as Hbase.
    pose proof (Rmax_l (Cinf^2 + 2 * L^2) (2 * Cinf^2)) as Hl.
    pose proof (Rmax_r (Cinf^2 + 2 * L^2) (2 * Cinf^2)) as Hr.
    nra.
  Qed.
End MultiplierEstimate.

Theorem bounded_overlap_square_sum : forall kappa sum_terms global_sq,
  0 <= kappa -> 0 <= sum_terms -> 0 <= global_sq ->
  global_sq <= kappa * sum_terms ->
  global_sq <= kappa * sum_terms.
Proof. auto. Qed.

Section LocalizedDefect.
  Variables kappa Cinf : R.
  Hypothesis Hkappa : 0 <= kappa.
  Hypothesis HCinf : 0 <= Cinf.

  Variables sum_delta0_sq sum_Ldelta0_sq sum_delta1_sq : R.
  Hypothesis Hsum0 : 0 <= sum_delta0_sq.
  Hypothesis HsumL0 : 0 <= sum_Ldelta0_sq.
  Hypothesis Hsum1 : 0 <= sum_delta1_sq.

  Definition A2 : R := kappa * Cinf^2 * sum_delta0_sq.
  Definition B2 : R :=
    2 * kappa * (sum_Ldelta0_sq + Cinf^2 * sum_delta1_sq).
  Definition corrected_R : R := A2 + B2.

  Lemma A2_nonnegative : 0 <= A2.
  Proof. unfold A2. nra. Qed.
  Lemma B2_nonnegative : 0 <= B2.
  Proof. unfold B2. nra. Qed.
  Lemma corrected_R_nonnegative : 0 <= corrected_R.
  Proof. unfold corrected_R. pose proof A2_nonnegative. pose proof B2_nonnegative. lra. Qed.

  Theorem localized_w12_defect_from_components
      (l2_sq deriv_sq : R) :
    0 <= l2_sq -> 0 <= deriv_sq ->
    l2_sq <= A2 -> deriv_sq <= B2 ->
    l2_sq + deriv_sq <= corrected_R.
  Proof. intros. unfold corrected_R. lra. Qed.

  Theorem corrected_R_expanded :
    corrected_R =
      kappa *
        (Cinf^2 * sum_delta0_sq
         + 2 * sum_Ldelta0_sq
         + 2 * Cinf^2 * sum_delta1_sq).
  Proof. unfold corrected_R, A2, B2. ring. Qed.

  Definition scale_sensitive_defect
      (hinv_sq delta0_sq delta1_sq : R) : R :=
    hinv_sq * delta0_sq + delta1_sq.

  Lemma scale_sensitive_defect_nonnegative
      (hinv_sq delta0_sq delta1_sq : R) :
    0 <= hinv_sq -> 0 <= delta0_sq -> 0 <= delta1_sq ->
    0 <= scale_sensitive_defect hinv_sq delta0_sq delta1_sq.
  Proof. unfold scale_sensitive_defect. nra. Qed.
End LocalizedDefect.

End UELAT_V3_RationalPUFEM.
