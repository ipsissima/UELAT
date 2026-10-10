(** EpsilonPrecision.v -- rational epsilon selector for authoritative
    Theorem 7.4. *)

From Coq Require Import Reals QArith Qreals Lra Ring.
From UELAT.V3 Require Import
  RepresentedSpace StrictSlackSearch DyadicVanishing GenericSlackCertification.

Module UELAT_V3_EpsilonPrecision.
Import UELAT_V3_RepresentedSpace.
Import UELAT_V3_StrictSlackSearch.
Import UELAT_V3_DyadicVanishing.
Import UELAT_V3_GenericSlackCertification.

Lemma q2r_zero_local : Q2R (0 : Q) = 0%R.
Proof.
  pose proof (Q2R_plus (0 : Q) (0 : Q)) as H.
  replace ((0 + 0)%Q) with (0 : Q) in H by reflexivity.
  lra.
Qed.

Lemma q2r_four_local : Q2R (4 : Q) = 4%R.
Proof.
  change (4 : Q) with (2 + 2)%Q.
  rewrite Q2R_plus, Q2R_two.
  lra.
Qed.

Definition epsilon_stage_test (eps : Q) (s : nat) : bool :=
  qltb (4 * qdyadic s) eps.

Definition qleb (a b : Q) : bool :=
  if Qlt_le_dec b a then false else true.

Lemma qleb_true_iff : forall a b, qleb a b = true <-> (a <= b)%Q.
Proof.
  intros a b. unfold qleb.
  destruct (Qlt_le_dec b a) as [Hgt|Hle].
  - split; intro H.
    + discriminate.
    + exfalso. exact ((Qlt_not_le _ _ Hgt) H).
  - split; intro H.
    + exact Hle.
    + reflexivity.
Qed.

Definition paper_k_test (eps : Q) (k : nat) : bool :=
  qleb (2 * qdyadic k) eps.

Theorem paper_k_eventually : forall eps,
  (0 < eps)%Q -> exists k, paper_k_test eps k = true.
Proof.
  intros eps Heps.
  pose proof (Qlt_Rlt _ _ Heps) as HepsR.
  rewrite q2r_zero_local in HepsR.
  destruct (dyadic_eventually_below (Q2R eps / 2) ltac:(lra)) as [k Hk].
  exists k. unfold paper_k_test. apply qleb_true_iff.
  apply Rle_Qle.
  rewrite Q2R_mult, qdyadic_real.
  rewrite Q2R_two.
  lra.
Qed.

Definition paper_k_search (eps : Q) (Heps : (0 < eps)%Q) :
    SemidecidableSlackSearch :=
  {| slack_test := paper_k_test eps;
     slack_eventually := paper_k_eventually eps Heps |}.

Definition paper_k (eps : Q) (Heps : (0 < eps)%Q) : nat :=
  run_semidecidable_slack_search (paper_k_search eps Heps).

Theorem paper_k_valid : forall eps Heps,
  (2 * qdyadic (paper_k eps Heps) <= eps)%Q.
Proof.
  intros eps Heps.
  unfold paper_k.
  pose proof
    (semidecidable_slack_search_valid (paper_k_search eps Heps)) as H.
  cbn in H.
  unfold paper_k_test in H.
  now apply qleb_true_iff in H.
Qed.

Theorem paper_k_minimal : forall eps Heps k,
  (2 * qdyadic k <= eps)%Q ->
  paper_k eps Heps <= k.
Proof.
  intros eps Heps k Hk.
  unfold paper_k.
  pose proof
    (semidecidable_slack_search_minimal (paper_k_search eps Heps) k) as Hmin.
  cbn in Hmin.
  apply Hmin.
  unfold paper_k_test.
  now apply qleb_true_iff.
Qed.

Theorem epsilon_stage_eventually : forall eps,
  (0 < eps)%Q -> exists s, epsilon_stage_test eps s = true.
Proof.
  intros eps Heps.
  pose proof (Qlt_Rlt _ _ Heps) as HepsR.
  rewrite q2r_zero_local in HepsR.
  destruct (dyadic_eventually_below (Q2R eps / 4) ltac:(lra)) as [s Hs].
  exists s. unfold epsilon_stage_test. apply qltb_true_iff. apply Rlt_Qlt.
  rewrite Q2R_mult, qdyadic_real. rewrite q2r_four_local. lra.
Qed.

Definition epsilon_search (eps : Q) (Heps : (0 < eps)%Q) :
    SemidecidableSlackSearch :=
  {| slack_test := epsilon_stage_test eps;
     slack_eventually := epsilon_stage_eventually eps Heps |}.

Definition epsilon_precision (eps : Q) (Heps : (0 < eps)%Q) : nat :=
  run_semidecidable_slack_search (epsilon_search eps Heps).

Theorem epsilon_precision_valid : forall eps Heps,
  epsilon_stage_test eps (epsilon_precision eps Heps) = true.
Proof.
  intros eps Heps.
  unfold epsilon_precision.
  pose proof
    (semidecidable_slack_search_valid (epsilon_search eps Heps)) as H.
  cbn in H. exact H.
Qed.

Theorem epsilon_precision_minimal : forall eps Heps s,
  epsilon_stage_test eps s = true ->
  epsilon_precision eps Heps <= s.
Proof.
  intros eps Heps s Hs.
  unfold epsilon_precision.
  pose proof
    (semidecidable_slack_search_minimal (epsilon_search eps Heps) s) as Hmin.
  cbn in Hmin.
  now apply Hmin.
Qed.

Lemma dyadic_plus_two : forall k,
  dyadic (k + 2) = dyadic k / 4.
Proof.
  intro k.
  replace (k + 2)%nat with (S (S k)) by lia.
  simpl. ring.
Qed.

Theorem epsilon_stage_from_announced_dyadic : forall eps k,
  (0 < eps)%Q ->
  (2 * qdyadic k <= eps)%Q ->
  epsilon_stage_test eps (k + 2) = true.
Proof.
  intros eps k Heps Hk.
  unfold epsilon_stage_test.
  apply qltb_true_iff.
  apply Rlt_Qlt.
  rewrite Q2R_mult, qdyadic_real, dyadic_plus_two.
  rewrite q2r_four_local.
  pose proof (Qle_Rle _ _ Hk) as HkR.
  rewrite Q2R_mult, qdyadic_real in HkR.
  rewrite Q2R_two in HkR.
  pose proof (Qlt_Rlt _ _ Heps) as HepsR.
  rewrite q2r_zero_local in HepsR.
  lra.
Qed.

Theorem epsilon_precision_paper_depth_bound : forall eps Heps k,
  (2 * qdyadic k <= eps)%Q ->
  epsilon_precision eps Heps <= k + 2.
Proof.
  intros eps Heps k Hk.
  apply epsilon_precision_minimal.
  now apply epsilon_stage_from_announced_dyadic.
Qed.

Theorem epsilon_precision_dyadic_bound : forall eps Heps,
  4 * dyadic (epsilon_precision eps Heps) < Q2R eps.
Proof.
  intros eps Heps.
  pose proof (epsilon_precision_valid eps Heps) as H.
  unfold epsilon_stage_test in H. apply qltb_true_iff in H.
  pose proof (Qlt_Rlt _ _ H) as HR.
  rewrite Q2R_mult, qdyadic_real in HR.
  rewrite q2r_four_local in HR. exact HR.
Qed.

Corollary epsilon_precision_half_tail : forall eps Heps,
  dyadic (epsilon_precision eps Heps) / 2 < Q2R eps.
Proof.
  intros eps Heps. pose proof (epsilon_precision_dyadic_bound eps Heps).
  pose proof (dyadic_pos (epsilon_precision eps Heps)). lra.
Qed.

End UELAT_V3_EpsilonPrecision.
