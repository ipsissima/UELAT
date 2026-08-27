(** EpsilonPrecision.v -- rational epsilon selector for authoritative
    Theorem 7.4. *)

From Coq Require Import Reals QArith Qreals Lra.
From UELAT.V3 Require Import
  RepresentedSpace StrictSlackSearch DyadicVanishing GenericSlackCertification.

Module UELAT_V3_EpsilonPrecision.
Import UELAT_V3_RepresentedSpace.
Import UELAT_V3_StrictSlackSearch.
Import UELAT_V3_DyadicVanishing.
Import UELAT_V3_GenericSlackCertification.

Definition epsilon_stage_test (eps : Q) (s : nat) : bool :=
  qltb (4 * qdyadic s) eps.

Theorem epsilon_stage_eventually : forall eps,
  (0 < eps)%Q -> exists s, epsilon_stage_test eps s = true.
Proof.
  intros eps Heps.
  pose proof (Qlt_Rlt _ _ Heps) as HepsR.
  change (Q2R (0 : Q)) with 0%R in HepsR.
  destruct (dyadic_eventually_below (Q2R eps / 4) ltac:(lra)) as [s Hs].
  exists s. unfold epsilon_stage_test. apply qltb_true_iff. apply Rlt_Qlt.
  rewrite Q2R_mult, qdyadic_real. change (Q2R (4 : Q)) with 4%R. lra.
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
  intros eps Heps. unfold epsilon_precision. apply semidecidable_slack_search_valid.
Qed.

Theorem epsilon_precision_dyadic_bound : forall eps Heps,
  4 * dyadic (epsilon_precision eps Heps) < Q2R eps.
Proof.
  intros eps Heps.
  pose proof (epsilon_precision_valid eps Heps) as H.
  unfold epsilon_stage_test in H. apply qltb_true_iff in H.
  pose proof (Qlt_Rlt _ _ H) as HR.
  rewrite Q2R_mult, qdyadic_real in HR.
  change (Q2R (4 : Q)) with 4%R in HR. exact HR.
Qed.

Corollary epsilon_precision_half_tail : forall eps Heps,
  dyadic (epsilon_precision eps Heps) / 2 < Q2R eps.
Proof.
  intros eps Heps. pose proof (epsilon_precision_dyadic_bound eps Heps).
  pose proof (dyadic_pos (epsilon_precision eps Heps)). lra.
Qed.

End UELAT_V3_EpsilonPrecision.
