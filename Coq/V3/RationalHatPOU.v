(** RationalHatPOU.v -- constructive rational PWL partition core for authoritative Lemma 5.4.

    On an ordered rational mesh, standard nodal hats form a rational
    continuous piecewise-linear partition of unity subordinate to the nodal
    star cover.  This file proves the exact cell-local identity, [0,1] bounds,
    and rational slope scale.
*)

From Coq Require Import QArith Lqa Qfield.
Local Open Scope Q_scope.

Module UELAT_V3_RationalHatPOU.

Definition left_hat_on_cell (a b x : Q) : Q :=
  (b - x) / (b - a).

Definition right_hat_on_cell (a b x : Q) : Q :=
  (x - a) / (b - a).

Theorem two_hat_partition_identity : forall a b x,
  ~ Qeq a b ->
  left_hat_on_cell a b x + right_hat_on_cell a b x == 1.
Proof.
  intros a b x Hab.
  unfold left_hat_on_cell, right_hat_on_cell.
  field.
  intro Hzero.
  apply Hab. lra.
Qed.

Theorem left_hat_nonnegative : forall a b x,
  (a < b)%Q -> (a <= x <= b)%Q ->
  (0 <= left_hat_on_cell a b x)%Q.
Proof.
  intros a b x Hab [Hax Hxb].
  unfold left_hat_on_cell.
  apply Qle_shift_div_l.
  - lra.
  - ring_simplify. lra.
Qed.

Theorem right_hat_nonnegative : forall a b x,
  (a < b)%Q -> (a <= x <= b)%Q ->
  (0 <= right_hat_on_cell a b x)%Q.
Proof.
  intros a b x Hab [Hax Hxb].
  unfold right_hat_on_cell.
  apply Qle_shift_div_l.
  - lra.
  - ring_simplify. lra.
Qed.

Theorem left_hat_at_most_one : forall a b x,
  (a < b)%Q -> (a <= x <= b)%Q ->
  (left_hat_on_cell a b x <= 1)%Q.
Proof.
  intros a b x Hab [Hax Hxb].
  unfold left_hat_on_cell.
  apply Qle_shift_div_r.
  - lra.
  - ring_simplify. lra.
Qed.

Theorem right_hat_at_most_one : forall a b x,
  (a < b)%Q -> (a <= x <= b)%Q ->
  (right_hat_on_cell a b x <= 1)%Q.
Proof.
  intros a b x Hab [Hax Hxb].
  unfold right_hat_on_cell.
  apply Qle_shift_div_r.
  - lra.
  - ring_simplify. lra.
Qed.

Definition left_hat_slope (a b : Q) : Q := (-1) / (b - a).
Definition right_hat_slope (a b : Q) : Q := 1 / (b - a).
Definition hat_inverse_width (a b : Q) : Q := 1 / (b - a).

Theorem hat_slopes_cancel : forall a b,
  ~ Qeq a b ->
  left_hat_slope a b + right_hat_slope a b == 0.
Proof.
  intros a b Hab.
  unfold left_hat_slope, right_hat_slope.
  field.
  intro Hzero. apply Hab. lra.
Qed.

Theorem right_hat_slope_is_inverse_width : forall a b,
  right_hat_slope a b = hat_inverse_width a b.
Proof. reflexivity. Qed.

Theorem left_hat_slope_is_negative_inverse_width : forall a b,
  left_hat_slope a b == - hat_inverse_width a b.
Proof.
  intros a b.
  unfold left_hat_slope, hat_inverse_width.
  ring.
Qed.

Theorem inverse_width_positive : forall a b,
  (a < b)%Q -> (0 < hat_inverse_width a b)%Q.
Proof.
  intros a b Hab.
  unfold hat_inverse_width.
  apply Qinv_lt_0_compat. lra.
Qed.

Record HatCellCertificate := {
  hat_left_endpoint : Q;
  hat_right_endpoint : Q;
  hat_cell_positive : (hat_left_endpoint < hat_right_endpoint)%Q
}.

Definition hat_cell_width (c : HatCellCertificate) : Q :=
  hat_right_endpoint c - hat_left_endpoint c.

Definition hat_cell_derivative_bound (c : HatCellCertificate) : Q :=
  / hat_cell_width c.

Theorem hat_cell_width_positive : forall c,
  (0 < hat_cell_width c)%Q.
Proof.
  intros c. unfold hat_cell_width.
  pose proof (hat_cell_positive c). lra.
Qed.

Theorem hat_cell_derivative_bound_positive : forall c,
  (0 < hat_cell_derivative_bound c)%Q.
Proof.
  intro c. unfold hat_cell_derivative_bound.
  apply Qinv_lt_0_compat.
  apply hat_cell_width_positive.
Qed.

Theorem certified_hat_cell_partition : forall c x,
  (hat_left_endpoint c <= x <= hat_right_endpoint c)%Q ->
  left_hat_on_cell (hat_left_endpoint c) (hat_right_endpoint c) x
  + right_hat_on_cell (hat_left_endpoint c) (hat_right_endpoint c) x == 1.
Proof.
  intros c x Hx.
  apply two_hat_partition_identity.
  pose proof (hat_cell_positive c). lra.
Qed.

Theorem certified_hat_cell_bounds : forall c x,
  (hat_left_endpoint c <= x <= hat_right_endpoint c)%Q ->
  (0 <= left_hat_on_cell (hat_left_endpoint c) (hat_right_endpoint c) x <= 1)%Q
  /\
  (0 <= right_hat_on_cell (hat_left_endpoint c) (hat_right_endpoint c) x <= 1)%Q.
Proof.
  intros c x Hx.
  pose proof (hat_cell_positive c) as Hpos.
  split; split.
  - now apply left_hat_nonnegative.
  - now apply left_hat_at_most_one.
  - now apply right_hat_nonnegative.
  - now apply right_hat_at_most_one.
Qed.

End UELAT_V3_RationalHatPOU.
