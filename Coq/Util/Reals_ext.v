(** Reals_ext.v — Real number extensions

    This module provides additional lemmas about real numbers
    that are used throughout the UELAT development.

    Reference: UELAT Paper, various sections
*)

From Coq Require Import Reals Lra Lia.
Local Open Scope R_scope.

Module UELAT_Reals_ext.

(** * Power Lemmas *)

Lemma Rpower_pos : forall x y, Rpower x y > 0.
Proof.
  intros x y.
  unfold Rpower.
  apply exp_pos.
Qed.

Lemma Rpower_1 : forall x, x > 0 -> Rpower x 1 = x.
Proof.
  intros x Hx.
  unfold Rpower.
  rewrite Rmult_1_l.
  apply exp_ln.
  exact Hx.
Qed.

Lemma Rpower_O : forall x, x > 0 -> Rpower x 0 = 1.
Proof.
  intros x Hx.
  unfold Rpower.
  rewrite Rmult_0_l.
  apply exp_0.
Qed.

Lemma Rpower_mult : forall x y z,
  x > 0 -> Rpower (Rpower x y) z = Rpower x (y * z).
Proof.
  intros x y z Hx.
  unfold Rpower.
  rewrite ln_exp.
  ring_simplify.
  reflexivity.
Qed.

Lemma Rpower_plus : forall x y z,
  x > 0 -> Rpower x (y + z) = Rpower x y * Rpower x z.
Proof.
  intros x y z Hx.
  unfold Rpower.
  rewrite Rmult_plus_distr_l.
  apply exp_plus.
Qed.

Lemma Rpower_lt : forall x a b,
  0 < x -> x < 1 -> a < b -> Rpower x b < Rpower x a.
Proof.
  intros x a b Hx0 Hx1 Hab.
  unfold Rpower.
  apply exp_increasing.
  apply Rmult_lt_compat_neg_l.
  - apply ln_lt_0. split; lra.
  - exact Hab.
Qed.

Lemma Rle_Rpower_l : forall a x y,
  a >= 0 -> 0 < x <= y -> Rpower x a <= Rpower y a.
Proof.
  intros a x y Ha [Hx Hxy].
  destruct (Req_dec a 0) as [Ha0 | Ha0].
  - subst. rewrite !Rpower_O; lra.
  - unfold Rpower.
    apply Rlt_le.
    apply exp_increasing.
    apply Rmult_lt_compat_l; [lra |].
    apply ln_increasing; lra.
Qed.

(** * Absolute Value Lemmas *)

Lemma Rabs_triang : forall x y z,
  Rabs (x - z) <= Rabs (x - y) + Rabs (y - z).
Proof.
  intros x y z.
  replace (x - z) with ((x - y) + (y - z)) by ring.
  apply Rabs_triang.
Qed.

Lemma Rabs_minus_sym : forall x y,
  Rabs (x - y) = Rabs (y - x).
Proof.
  intros x y.
  rewrite <- Rabs_Ropp.
  f_equal. ring.
Qed.

Lemma Rabs_mult_pos : forall x y,
  y >= 0 -> Rabs (x * y) = Rabs x * y.
Proof.
  intros x y Hy.
  rewrite Rabs_mult.
  rewrite (Rabs_right y); lra.
Qed.

Lemma Rabs_div_pos : forall x y,
  y > 0 -> Rabs (x / y) = Rabs x / y.
Proof.
  intros x y Hy.
  unfold Rdiv.
  rewrite Rabs_mult.
  rewrite Rabs_right; [reflexivity | apply Rlt_le; apply Rinv_0_lt_compat; exact Hy].
Qed.

(** * Sqrt Lemmas *)

Lemma sqrt_pos : forall x, sqrt x >= 0.
Proof.
  intro x.
  apply Rle_ge.
  apply sqrt_positivity.
Qed.

Lemma sqrt_le_compat : forall x y,
  0 <= x -> 0 <= y -> x <= y -> sqrt x <= sqrt y.
Proof.
  intros x y Hx Hy Hxy.
  apply sqrt_le_1.
  - exact Hx.
  - exact Hy.
  - exact Hxy.
Qed.

Lemma sqrt_mult_alt : forall x y,
  0 <= x -> 0 <= y -> sqrt (x * y) = sqrt x * sqrt y.
Proof.
  intros x y Hx Hy.
  apply sqrt_mult; assumption.
Qed.

Lemma sqrt_div_alt : forall x y,
  0 <= x -> 0 < y -> sqrt (x / y) = sqrt x / sqrt y.
Proof.
  intros x y Hx Hy.
  unfold Rdiv.
  rewrite sqrt_mult_alt.
  - rewrite sqrt_Rinv; [reflexivity | lra].
  - exact Hx.
  - apply Rlt_le. apply Rinv_0_lt_compat. exact Hy.
Qed.

(** * Min/Max Lemmas *)

Lemma Rmin_pos : forall x y, 0 < x -> 0 < y -> 0 < Rmin x y.
Proof.
  intros x y Hx Hy.
  apply Rmin_glb_lt; assumption.
Qed.

Lemma Rmax_nonneg : forall x y, 0 <= x -> 0 <= Rmax x y.
Proof.
  intros x y Hx.
  apply Rle_trans with x; [exact Hx | apply Rmax_l].
Qed.

Lemma Rmax_r : forall x y, y <= Rmax x y.
Proof.
  intros x y.
  unfold Rmax.
  destruct (Rle_dec x y); lra.
Qed.

Lemma Rmax_le_compat : forall x1 x2 y1 y2,
  x1 <= y1 -> x2 <= y2 -> Rmax x1 x2 <= Rmax y1 y2.
Proof.
  intros x1 x2 y1 y2 H1 H2.
  apply Rmax_lub.
  - apply Rle_trans with y1; [exact H1 | apply Rmax_l].
  - apply Rle_trans with y2; [exact H2 | apply Rmax_r].
Qed.

Lemma Rle_min_compat_l : forall x y z,
  x <= y -> Rmin x z <= y.
Proof.
  intros x y z Hxy.
  apply Rle_trans with x; [apply Rmin_l | exact Hxy].
Qed.

(** * Summation Lemmas *)

Lemma fold_right_Rplus_nonneg : forall (l : list R),
  Forall (fun x => x >= 0) l ->
  fold_right Rplus 0 l >= 0.
Proof.
  intros l Hl.
  induction l as [|a l' IH].
  - simpl. lra.
  - simpl.
    inversion Hl as [|a' l'' Ha Hl']; subst.
    specialize (IH Hl').
    lra.
Qed.

(** * Archimedes *)

Lemma archimed_upper : forall r,
  0 <= r -> INR (Z.to_nat (up r)) >= r.
Proof.
  intros r Hr.
  destruct (archimed r) as [Hup _].
  assert (Hpos : (0 <= up r)%Z).
  { apply le_IZR. simpl.
    apply Rle_trans with r; [exact Hr | apply Rlt_le; exact Hup]. }
  rewrite INR_IZR_INZ.
  rewrite Z2Nat.id; [| exact Hpos].
  lra.
Qed.

(** * Exponential and Logarithm *)

Lemma exp_pos' : forall x, exp x > 0.
Proof.
  apply exp_pos.
Qed.

Lemma ln_increasing : forall x y, 0 < x -> x < y -> ln x < ln y.
Proof.
  intros x y Hx Hxy.
  apply ln_increasing; [exact Hx | exact Hxy].
Qed.

Lemma ln_lt_0 : forall x, 0 < x < 1 -> ln x < 0.
Proof.
  intros x [Hx0 Hx1].
  rewrite <- ln_1.
  apply ln_increasing; lra.
Qed.

End UELAT_Reals_ext.
