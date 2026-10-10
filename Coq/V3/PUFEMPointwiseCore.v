(** Constructive finite-overlap and multiplier core for v3 Theorems 5.6/7.2.
    No axiom or abstract overlap estimate is used: the overlap inequality
    is proved from Cauchy-Schwarz on the actual finite list of summands.
    The quadrature consequence is only a finite model, not yet W1,2.
*)
From Coq Require Import Reals List Lra Lia Ring.
Import ListNotations.
Local Open Scope R_scope.

Module UELAT_V3_PUFEMPointwiseCore.

Fixpoint sumR (xs : list R) : R :=
  match xs with [] => 0 | x :: ys => x + sumR ys end.

Fixpoint squareSum (xs : list R) : R :=
  match xs with [] => 0 | x :: ys => x ^ 2 + squareSum ys end.

Lemma squareSum_nonnegative : forall xs, 0 <= squareSum xs.
Proof. induction xs as [|x xs IH]; simpl; nra. Qed.

Lemma cross_sum_bound : forall x xs,
  2 * x * sumR xs <= INR (length xs) * x ^ 2 + squareSum xs.
Proof.
  intros x xs; induction xs as [|y ys IH]; simpl.
  - nra.
  - rewrite S_INR.
    assert (Hpair : 2 * x * y <= x ^ 2 + y ^ 2) by nra.
    nra.
Qed.

(** Cauchy-Schwarz against the vector of ones, proved from squares. *)
Theorem finite_cauchy_overlap : forall xs,
  (sumR xs) ^ 2 <= INR (length xs) * squareSum xs.
Proof.
  induction xs as [|x xs IH]; simpl.
  - nra.
  - rewrite S_INR.
    pose proof (cross_sum_bound x xs) as Hcross.
    nra.
Qed.

Theorem bounded_overlap_squared : forall xs kappa,
  (length xs <= kappa)%nat ->
  (sumR xs) ^ 2 <= INR kappa * squareSum xs.
Proof.
  intros xs kappa Hlen.
  eapply Rle_trans.
  - apply finite_cauchy_overlap.
  - apply Rmult_le_compat_r.
    + apply squareSum_nonnegative.
    + apply le_INR. exact Hlen.
Qed.

Lemma squareSum_map : forall (A : Type) (f : A -> R) (xs : list A),
  squareSum (map f xs) = sumR (map (fun a => (f a) ^ 2) xs).
Proof.
  intros A f xs. induction xs as [|x xs IH]; simpl.
  - reflexivity.
  - now rewrite IH.
Qed.

Lemma sumR_map_mono : forall (A : Type) (f g : A -> R) xs,
  (forall a, In a xs -> f a <= g a) ->
  sumR (map f xs) <= sumR (map g xs).
Proof.
  intros A f g xs.
  induction xs as [|a xs IH]; intro H; simpl; [lra|].
  assert (Ha : f a <= g a) by (apply H; left; reflexivity).
  assert (Ht : sumR (map f xs) <= sumR (map g xs)).
  { apply IH. intros z Hz. apply H. right. exact Hz. }
  lra.
Qed.

Lemma sumR_map_add : forall (A : Type) (f g : A -> R) xs,
  sumR (map (fun a => f a + g a) xs) =
    sumR (map f xs) + sumR (map g xs).
Proof.
  intros A f g xs; induction xs as [|a xs IH]; simpl.
  - ring.
  - rewrite IH. ring.
Qed.

Lemma bounded_multiplier_square : forall C p x,
  - C <= p -> p <= C -> (p * x) ^ 2 <= C ^ 2 * x ^ 2.
Proof.
  intros C p x Hpmin Hpmax.
  assert (Hp : p ^ 2 <= C ^ 2) by nra.
  replace ((p * x) ^ 2) with (p ^ 2 * x ^ 2) by ring.
  apply Rmult_le_compat_r.
  - apply pow2_ge_0.
  - exact Hp.
Qed.

Record Incidence (Cinf : R) := {
  pw_psi : R;
  pw_psi_prime : R;
  pw_error : R;
  pw_error_prime : R;
  pw_L : R;
  pw_psi_lower : - Cinf <= pw_psi;
  pw_psi_upper : pw_psi <= Cinf;
  pw_psi_prime_lower : - pw_L <= pw_psi_prime;
  pw_psi_prime_upper : pw_psi_prime <= pw_L
}.
Arguments pw_psi {Cinf} _.
Arguments pw_psi_prime {Cinf} _.
Arguments pw_error {Cinf} _.
Arguments pw_error_prime {Cinf} _.
Arguments pw_L {Cinf} _.
Arguments pw_psi_lower {Cinf} _.
Arguments pw_psi_upper {Cinf} _.
Arguments pw_psi_prime_lower {Cinf} _.
Arguments pw_psi_prime_upper {Cinf} _.

Definition value_term {Cinf} (z : Incidence Cinf) : R :=
  pw_psi z * pw_error z.
Definition derivative_term {Cinf} (z : Incidence Cinf) : R :=
  pw_psi_prime z * pw_error z + pw_psi z * pw_error_prime z.
Definition l2_allowance {Cinf} (z : Incidence Cinf) : R :=
  Cinf ^ 2 * pw_error z ^ 2.
Definition derivative_allowance {Cinf} (z : Incidence Cinf) : R :=
  2 * (pw_L z ^ 2 * pw_error z ^ 2
       + Cinf ^ 2 * pw_error_prime z ^ 2).
Definition total_allowance {Cinf} (z : Incidence Cinf) : R :=
  l2_allowance z + derivative_allowance z.

Lemma pointwise_value_bound : forall Cinf (z : Incidence Cinf),
  (value_term z) ^ 2 <= l2_allowance z.
Proof.
  intros Cinf z. unfold value_term, l2_allowance.
  apply bounded_multiplier_square.
  - apply pw_psi_lower.
  - apply pw_psi_upper.
Qed.

Lemma pointwise_derivative_bound : forall Cinf (z : Incidence Cinf),
  (derivative_term z) ^ 2 <= derivative_allowance z.
Proof.
  intros Cinf z. unfold derivative_term, derivative_allowance.
  eapply Rle_trans with
    (r2 := 2 * ((pw_psi_prime z * pw_error z) ^ 2
             + (pw_psi z * pw_error_prime z) ^ 2)).
  - nra.
  - apply Rmult_le_compat_l; [lra|].
    apply Rplus_le_compat.
    + apply bounded_multiplier_square.
      * apply pw_psi_prime_lower.
      * apply pw_psi_prime_upper.
    + apply bounded_multiplier_square.
      * apply pw_psi_lower.
      * apply pw_psi_upper.
Qed.

Lemma total_allowance_formula : forall Cinf (z : Incidence Cinf),
  total_allowance z =
    (Cinf ^ 2 + 2 * pw_L z ^ 2) * pw_error z ^ 2
    + 2 * Cinf ^ 2 * pw_error_prime z ^ 2.
Proof.
  intros. unfold total_allowance, l2_allowance, derivative_allowance.
  ring.
Qed.

(** Exact pointwise integrand bound matching the corrected R_j of 5.6. *)
Theorem localized_integrand_56 : forall Cinf (xs : list (Incidence Cinf)) kappa,
  (length xs <= kappa)%nat ->
  (sumR (map (@value_term Cinf) xs)) ^ 2
    + (sumR (map (@derivative_term Cinf) xs)) ^ 2
  <= INR kappa * sumR (map (@total_allowance Cinf) xs).
Proof.
  intros Cinf xs kappa Hlen.
  assert (Hvlen : (length (map (@value_term Cinf) xs) <= kappa)%nat).
  { rewrite map_length. exact Hlen. }
  assert (Hdlen : (length (map (@derivative_term Cinf) xs) <= kappa)%nat).
  { rewrite map_length. exact Hlen. }
  pose proof (bounded_overlap_squared (map (@value_term Cinf) xs)
    kappa Hvlen) as Hv.
  pose proof (bounded_overlap_squared (map (@derivative_term Cinf) xs)
    kappa Hdlen) as Hd.
  rewrite squareSum_map in Hv, Hd.
  assert (Hav :
    sumR (map (fun z => (value_term z) ^ 2) xs)
    <= sumR (map (@l2_allowance Cinf) xs)).
  { apply sumR_map_mono. intros z Hz. apply pointwise_value_bound. }
  assert (Had :
    sumR (map (fun z => (derivative_term z) ^ 2) xs)
    <= sumR (map (@derivative_allowance Cinf) xs)).
  { apply sumR_map_mono. intros z Hz. apply pointwise_derivative_bound. }
  assert (Hk : 0 <= INR kappa) by apply pos_INR.
  assert (Hsum :
    sumR (map (fun z => (value_term z) ^ 2) xs)
    + sumR (map (fun z => (derivative_term z) ^ 2) xs)
    <= sumR (map (@total_allowance Cinf) xs)).
  { unfold total_allowance. rewrite sumR_map_add. lra. }
  eapply Rle_trans with
    (r2 := INR kappa *
      (sumR (map (fun z => (value_term z) ^ 2) xs)
       + sumR (map (fun z => (derivative_term z) ^ 2) xs))).
  - rewrite Rmult_plus_distr_l. lra.
  - apply Rmult_le_compat_l; assumption.
Qed.

(** An exact *finite quadrature* model; not the continuous Sobolev theorem. *)
Record QuadratureSample (Cinf : R) (kappa : nat) := {
  sample_weight : R;
  sample_weight_nonnegative : 0 <= sample_weight;
  sample_incidences : list (Incidence Cinf);
  sample_overlap : (length sample_incidences <= kappa)%nat
}.
Arguments sample_weight {Cinf kappa} _.
Arguments sample_weight_nonnegative {Cinf kappa} _.
Arguments sample_incidences {Cinf kappa} _.
Arguments sample_overlap {Cinf kappa} _.

Definition sample_defect {Cinf kappa}
    (s : QuadratureSample Cinf kappa) : R :=
  sample_weight s *
    ((sumR (map (@value_term Cinf) (sample_incidences s))) ^ 2
     + (sumR (map (@derivative_term Cinf) (sample_incidences s))) ^ 2).
Definition sample_budget {Cinf kappa}
    (s : QuadratureSample Cinf kappa) : R :=
  sample_weight s * INR kappa *
    sumR (map (@total_allowance Cinf) (sample_incidences s)).

Lemma sample_defect_le_budget : forall Cinf kappa
    (s : QuadratureSample Cinf kappa),
  sample_defect s <= sample_budget s.
Proof.
  intros Cinf kappa s.
  unfold sample_defect, sample_budget.
  replace (sample_weight s * INR kappa *
     sumR (map (@total_allowance Cinf) (sample_incidences s)))
    with (sample_weight s *
      (INR kappa * sumR
        (map (@total_allowance Cinf) (sample_incidences s)))) by ring.
  apply Rmult_le_compat_l.
  - apply sample_weight_nonnegative.
  - apply localized_integrand_56. apply sample_overlap.
Qed.

Theorem finite_quadrature_localized_56 : forall Cinf kappa
    (samples : list (QuadratureSample Cinf kappa)),
  sumR (map (@sample_defect Cinf kappa) samples)
  <= sumR (map (@sample_budget Cinf kappa) samples).
Proof.
  intros Cinf kappa samples.
  apply sumR_map_mono.
  intros s Hs. apply sample_defect_le_budget.
Qed.


(** The manuscript assumes at most kappa *active* partition summands
    at each point, not that the entire neighbour list has length kappa.
    Support tags are explicitly supplied, with proofs that inactive
    summands vanish both in value and derivative. This allows a fixed
    neighbour list of arbitrary size without weakening the theorem. *)

Lemma total_allowance_nonnegative : forall Cinf (z : Incidence Cinf),
  0 <= total_allowance z.
Proof.
  intros Cinf z.
  unfold total_allowance, l2_allowance, derivative_allowance.
  assert (H0 : 0 <= Cinf ^ 2 * pw_error z ^ 2).
  { apply Rmult_le_pos; apply pow2_ge_0. }
  assert (H1 : 0 <= pw_L z ^ 2 * pw_error z ^ 2).
  { apply Rmult_le_pos; apply pow2_ge_0. }
  assert (H2 : 0 <= Cinf ^ 2 * pw_error_prime z ^ 2).
  { apply Rmult_le_pos; apply pow2_ge_0. }
  lra.
Qed.

Lemma sumR_filter_nonnegative :
  forall (A : Type) (f : A -> R) (active : A -> bool) xs,
    (forall a, In a xs -> 0 <= f a) ->
    sumR (map f (filter active xs)) <= sumR (map f xs).
Proof.
  intros A f active xs.
  induction xs as [|a xs IH]; intro Hnonneg; simpl.
  - lra.
  - destruct (active a) eqn:Ha; simpl.
    + assert (Ht : sumR (map f (filter active xs)) <=
                    sumR (map f xs)).
      { apply IH. intros z Hz. apply Hnonneg.
        right. exact Hz. }
      lra.
    + assert (Ha0 : 0 <= f a).
      { apply Hnonneg. left. reflexivity. }
      assert (Ht : sumR (map f (filter active xs)) <=
                    sumR (map f xs)).
      { apply IH. intros z Hz. apply Hnonneg.
        right. exact Hz. }
      lra.
Qed.

Record SupportIncidence (Cinf : R) := {
  si_incidence : Incidence Cinf;
  si_active : bool;
  si_zero_if_inactive :
    si_active = false ->
      value_term si_incidence = 0 /\ derivative_term si_incidence = 0
}.
Arguments si_incidence {Cinf} _.
Arguments si_active {Cinf} _.
Arguments si_zero_if_inactive {Cinf} _ _.

Definition active_patch {Cinf} (xs : list (SupportIncidence Cinf)) :
    list (Incidence Cinf) :=
  map si_incidence (filter si_active xs).

Lemma support_value_sum : forall Cinf (xs : list (SupportIncidence Cinf)),
  sumR (map (fun z => value_term (si_incidence z)) xs) =
  sumR (map (@value_term Cinf) (active_patch xs)).
Proof.
  intros Cinf xs. unfold active_patch.
  induction xs as [|z xs IH]; simpl; [reflexivity|].
  destruct (si_active z) eqn:Hz; simpl.
  - rewrite IH. reflexivity.
  - destruct (si_zero_if_inactive z Hz) as [Hvalue _].
    rewrite Hvalue, IH. ring.
Qed.

Lemma support_derivative_sum :
  forall Cinf (xs : list (SupportIncidence Cinf)),
  sumR (map (fun z => derivative_term (si_incidence z)) xs) =
  sumR (map (@derivative_term Cinf) (active_patch xs)).
Proof.
  intros Cinf xs. unfold active_patch.
  induction xs as [|z xs IH]; simpl; [reflexivity|].
  destruct (si_active z) eqn:Hz; simpl.
  - rewrite IH. reflexivity.
  - destruct (si_zero_if_inactive z Hz) as [_ Hderiv].
    rewrite Hderiv, IH. ring.
Qed.

(** Exact pointwise overlap statement: only active terms are counted,
    but the right-hand side sums the defects for the full neighbour list. *)
Theorem localized_integrand_supported_56 :
  forall Cinf (xs : list (SupportIncidence Cinf)) kappa,
    (length (filter si_active xs) <= kappa)%nat ->
    (sumR (map (fun z => value_term (si_incidence z)) xs)) ^ 2
      + (sumR (map (fun z => derivative_term (si_incidence z)) xs)) ^ 2
    <= INR kappa *
       sumR (map (fun z => total_allowance (si_incidence z)) xs).
Proof.
  intros Cinf xs kappa Hactive.
  rewrite (support_value_sum Cinf xs).
  rewrite (support_derivative_sum Cinf xs).
  assert (Hlen : (length (active_patch xs) <= kappa)%nat).
  { unfold active_patch. rewrite map_length. exact Hactive. }
  eapply Rle_trans.
  - apply localized_integrand_56. exact Hlen.
  - apply Rmult_le_compat_l.
    + apply pos_INR.
    + unfold active_patch.
      rewrite map_map.
      apply sumR_filter_nonnegative.
      intros z Hz.
      apply total_allowance_nonnegative.
Qed.

(** Discrete integration over nonnegative weights, with a variable
    set of at most kappa active incidence terms at every sample. *)
Record SupportedSample (Cinf : R) (kappa : nat) := {
  ss_weight : R;
  ss_weight_nonnegative : 0 <= ss_weight;
  ss_neighbours : list (SupportIncidence Cinf);
  ss_active_overlap :
    (length (filter si_active ss_neighbours) <= kappa)%nat
}.
Arguments ss_weight {Cinf kappa} _.
Arguments ss_weight_nonnegative {Cinf kappa} _.
Arguments ss_neighbours {Cinf kappa} _.
Arguments ss_active_overlap {Cinf kappa} _.

Definition supported_sample_defect {Cinf kappa}
    (s : SupportedSample Cinf kappa) : R :=
  ss_weight s *
    ((sumR (map (fun z => value_term (si_incidence z))
       (ss_neighbours s))) ^ 2
    + (sumR (map (fun z => derivative_term (si_incidence z))
       (ss_neighbours s))) ^ 2).

Definition supported_sample_budget {Cinf kappa}
    (s : SupportedSample Cinf kappa) : R :=
  ss_weight s * INR kappa *
    sumR (map (fun z => total_allowance (si_incidence z))
      (ss_neighbours s)).

Lemma supported_sample_defect_bound :
  forall Cinf kappa (s : SupportedSample Cinf kappa),
    supported_sample_defect s <= supported_sample_budget s.
Proof.
  intros Cinf kappa s.
  unfold supported_sample_defect, supported_sample_budget.
  replace (ss_weight s * INR kappa *
      sumR (map (fun z => total_allowance (si_incidence z))
        (ss_neighbours s)))
    with (ss_weight s *
      (INR kappa *
        sumR (map (fun z => total_allowance (si_incidence z))
          (ss_neighbours s)))) by ring.
  apply Rmult_le_compat_l.
  - apply ss_weight_nonnegative.
  - apply localized_integrand_supported_56.
    apply ss_active_overlap.
Qed.

Theorem finite_supported_quadrature_56 :
  forall Cinf kappa (samples : list (SupportedSample Cinf kappa)),
    sumR (map (@supported_sample_defect Cinf kappa) samples)
      <= sumR (map (@supported_sample_budget Cinf kappa) samples).
Proof.
  intros Cinf kappa samples.
  apply sumR_map_mono. intros s Hs.
  apply supported_sample_defect_bound.
Qed.

End UELAT_V3_PUFEMPointwiseCore.
