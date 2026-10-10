(**
  RationalHatProductSemantic.v -- exact bridge from the rational hat
  constructor of Lemma 5.4 to the finite multiplication and derivative
  operations used in Theorem 5.6 and the mesh multiplier in 7.2.

  On a certified cell a<b the actual rational hat functions are affine
  polynomials. The identities below are established in Qeq, rather
  than assuming a product-rule oracle for the finite-code compiler.

  No continuous weak-derivative claim is made. The gluing of the
  cellwise derivative into W^{1,2}(0,1) is a separate obligation.
*)
From Coq Require Import QArith List Ring Setoid.
Import ListNotations.
Local Open Scope Q_scope.

From UELAT.V3 Require Import
  RationalSobolev RationalHatPOU RationalPolynomialSemantic.

Module UELAT_V3_RationalHatProductSemantic.
Import UELAT_V3_RationalSobolev.
Import UELAT_V3_RationalHatPOU.
Import UELAT_V3_RationalPolynomialSemantic.

Definition left_hat_poly (a b : Q) : QPoly :=
  [b / (b - a); - (1 / (b - a))].

Definition right_hat_poly (a b : Q) : QPoly :=
  [- a / (b - a); 1 / (b - a)].

Lemma left_hat_poly_semantics : forall a b x,
  qpoly_eval (left_hat_poly a b) x == left_hat_on_cell a b x.
Proof.
  intros a b x. unfold left_hat_poly, left_hat_on_cell.
  simpl. unfold Qdiv. ring.
Qed.

Lemma right_hat_poly_semantics : forall a b x,
  qpoly_eval (right_hat_poly a b) x == right_hat_on_cell a b x.
Proof.
  intros a b x. unfold right_hat_poly, right_hat_on_cell.
  simpl. unfold Qdiv. ring.
Qed.

Lemma left_hat_poly_derivative : forall a b x,
  qpoly_eval (qpoly_deriv (left_hat_poly a b)) x
    == left_hat_slope a b.
Proof.
  intros a b x. unfold left_hat_poly, left_hat_slope.
  simpl. unfold Qdiv. ring.
Qed.

Lemma right_hat_poly_derivative : forall a b x,
  qpoly_eval (qpoly_deriv (right_hat_poly a b)) x
    == right_hat_slope a b.
Proof.
  intros a b x. unfold right_hat_poly, right_hat_slope.
  simpl. unfold Qdiv. ring.
Qed.

(** The true code-level construction represents the two hats
    whose values sum to 1 on the same rational cell. *)
Theorem concrete_hat_partition_identity : forall a b x,
  ~ Qeq a b ->
  qpoly_eval (left_hat_poly a b) x
    + qpoly_eval (right_hat_poly a b) x == 1.
Proof.
  intros a b x Hneq.
  setoid_rewrite left_hat_poly_semantics.
  setoid_rewrite right_hat_poly_semantics.
  apply two_hat_partition_identity. exact Hneq.
Qed.

Theorem concrete_left_hat_product_derivative : forall a b p x,
  qpoly_eval
    (qpoly_deriv (qpoly_mul (left_hat_poly a b) p)) x
  == left_hat_slope a b * qpoly_eval p x
      + left_hat_on_cell a b x * qpoly_eval (qpoly_deriv p) x.
Proof.
  intros a b p x.
  unfold left_hat_poly.
  setoid_rewrite affine_hat_product_derivative.
  unfold left_hat_slope, left_hat_on_cell, Qdiv.
  ring.
Qed.

Theorem concrete_right_hat_product_derivative : forall a b p x,
  qpoly_eval
    (qpoly_deriv (qpoly_mul (right_hat_poly a b) p)) x
  == right_hat_slope a b * qpoly_eval p x
      + right_hat_on_cell a b x * qpoly_eval (qpoly_deriv p) x.
Proof.
  intros a b p x.
  unfold right_hat_poly.
  setoid_rewrite affine_hat_product_derivative.
  unfold right_hat_slope, right_hat_on_cell, Qdiv.
  ring.
Qed.

Theorem concrete_left_hat_product_value : forall a b p x,
  qpoly_eval (qpoly_mul (left_hat_poly a b) p) x
  == left_hat_on_cell a b x * qpoly_eval p x.
Proof.
  intros a b p x.
  setoid_rewrite qpoly_eval_mul_sound.
  setoid_rewrite left_hat_poly_semantics.
  reflexivity.
Qed.

Theorem concrete_right_hat_product_value : forall a b p x,
  qpoly_eval (qpoly_mul (right_hat_poly a b) p) x
  == right_hat_on_cell a b x * qpoly_eval p x.
Proof.
  intros a b p x.
  setoid_rewrite qpoly_eval_mul_sound.
  setoid_rewrite right_hat_poly_semantics.
  reflexivity.
Qed.

End UELAT_V3_RationalHatProductSemantic.
