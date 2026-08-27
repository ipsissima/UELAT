(** DyadicVanishing.v -- quantitative tail lemmas for strict-slack search and
    effective descent/range inversion. *)

From Coq Require Import Reals Rseries Lra Lia.
Local Open Scope R_scope.
From UELAT.V3 Require Import RepresentedSpace.

Module UELAT_V3_DyadicVanishing.
Import UELAT_V3_RepresentedSpace.

Lemma dyadic_as_power : forall n, dyadic n = (/ 2) ^ n.
Proof. induction n as [|n IH]; [reflexivity|simpl; rewrite IH; ring]. Qed.

Lemma half_abs_lt_one : Rabs (/ 2) < 1.
Proof.
  rewrite Rabs_pos_eq.
  - apply Rinv_lt_contravar; nra.
  - left. apply Rinv_0_lt_compat. lra.
Qed.

Lemma half_power_nonnegative : forall n, 0 <= (/ 2) ^ n.
Proof. intro n. apply pow_le. left. apply Rinv_0_lt_compat. lra. Qed.

Lemma dyadic_step_le : forall n, dyadic (S n) <= dyadic n.
Proof. intro n. simpl. pose proof (dyadic_nonnegative n). lra. Qed.

Lemma dyadic_antitone : forall n m,
  (n <= m)%nat -> dyadic m <= dyadic n.
Proof.
  intros n m Hnm. induction Hnm as [|m Hnm IH].
  - apply Rle_refl.
  - eapply Rle_trans; [apply dyadic_step_le|exact IH].
Qed.

Lemma two_shifted_dyadics_le : forall n,
  2 * dyadic (S (S n)) <= dyadic n.
Proof. intro n. simpl. pose proof (dyadic_nonnegative n). lra. Qed.

Lemma shifted_dyadic_le : forall n,
  dyadic (S (S n)) <= dyadic n.
Proof. intro n. apply dyadic_antitone. lia. Qed.

Theorem dyadic_eventually_below : forall eps : R,
  0 < eps -> exists n : nat, dyadic n < eps.
Proof.
  intros eps Heps.
  destruct (pow_lt_1_zero (/ 2) half_abs_lt_one eps Heps) as [N HN].
  exists N. specialize (HN N (Nat.le_refl _)).
  rewrite Rabs_pos_eq in HN.
  - rewrite dyadic_as_power. exact HN.
  - apply half_power_nonnegative.
Qed.

Corollary two_dyadic_eventually_below : forall eps : R,
  0 < eps -> exists n : nat, 2 * dyadic n < eps.
Proof.
  intros eps Heps. destruct (dyadic_eventually_below (eps / 2)) as [n Hn]; [lra|].
  exists n. lra.
Qed.

Corollary four_dyadic_eventually_below : forall eps : R,
  0 < eps -> exists n : nat, 4 * dyadic n < eps.
Proof.
  intros eps Heps. destruct (dyadic_eventually_below (eps / 4)) as [n Hn]; [lra|].
  exists n. lra.
Qed.

End UELAT_V3_DyadicVanishing.
