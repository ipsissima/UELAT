(**
  RationalPolynomialSemantic.v -- exact rational polynomial algebra for
  the localized PUFEM multiplier/product-rule boundary (Theorems 5.6/7.2).

  Unlike the existential statements "there exists an exact rational
  answer", these lemmas establish Qeq equality between the actual
  finite-code operations and their mathematical interpretation.

  The final Leibniz theorem applies to any rational polynomial product;
  the affine corollary applies to rational hat functions on each cell.

  Remaining: continuity/weak derivative identification at piece
  boundaries, the corresponding analytic L2 integration and Sobolev
  norm, and kernel build of this module. No continuous W12 claim here.
*)
From Coq Require Import QArith List Ring Setoid.
Import ListNotations.
Local Open Scope Q_scope.

From UELAT.V3 Require Import RationalSobolev.

Module UELAT_V3_RationalPolynomialSemantic.
Import UELAT_V3_RationalSobolev.

Lemma qpoly_eval_add_sound : forall p q x,
  qpoly_eval (qpoly_add p q) x ==
    qpoly_eval p x + qpoly_eval q x.
Proof.
  intro p. induction p as [|a ps IH]; intros [|b qs] x;
    simpl; try ring.
  setoid_rewrite (IH qs x).
  ring.
Qed.

Lemma qpoly_eval_scale_sound : forall c p x,
  qpoly_eval (qpoly_scale c p) x == c * qpoly_eval p x.
Proof.
  intros c p. induction p as [|a ps IH]; intro x; simpl.
  - ring.
  - setoid_rewrite IH. ring.
Qed.

Lemma qpoly_eval_neg_sound : forall p x,
  qpoly_eval (qpoly_neg p) x == - qpoly_eval p x.
Proof.
  intros p x. unfold qpoly_neg.
  setoid_rewrite qpoly_eval_scale_sound. ring.
Qed.

Lemma qpoly_eval_sub_sound : forall p q x,
  qpoly_eval (qpoly_sub p q) x ==
    qpoly_eval p x - qpoly_eval q x.
Proof.
  intros p q x. unfold qpoly_sub.
  setoid_rewrite qpoly_eval_add_sound.
  setoid_rewrite qpoly_eval_neg_sound.
  ring.
Qed.

(** Horner semantics of the ACTUAL terminating multiplication compiler. *)
Theorem qpoly_eval_mul_sound : forall p q x,
  qpoly_eval (qpoly_mul p q) x ==
    qpoly_eval p x * qpoly_eval q x.
Proof.
  intro p. induction p as [|a ps IH]; intros q x.
  - simpl. ring.
  - simpl qpoly_mul.
    setoid_rewrite qpoly_eval_add_sound.
    setoid_rewrite qpoly_eval_scale_sound.
    simpl qpoly_eval.
    setoid_rewrite (IH q x).
    ring.
Qed.

Lemma deriv_from_add_eval : forall n p q x,
  qpoly_eval (qpoly_deriv_from n (qpoly_add p q)) x ==
    qpoly_eval (qpoly_deriv_from n p) x
      + qpoly_eval (qpoly_deriv_from n q) x.
Proof.
  intros n p. revert n.
  induction p as [|a ps IH]; intros n [|b qs] x;
    simpl; try ring.
  setoid_rewrite (IH (S n) qs x).
  ring.
Qed.

Lemma deriv_from_scale_eval : forall n c p x,
  qpoly_eval (qpoly_deriv_from n (qpoly_scale c p)) x ==
    c * qpoly_eval (qpoly_deriv_from n p) x.
Proof.
  intros n c p. revert n.
  induction p as [|a ps IH]; intros n x; simpl.
  - ring.
  - setoid_rewrite (IH (S n) x). ring.
Qed.

(** Incrementing the coefficient-degree offset adds the polynomial. *)
Lemma deriv_from_step_eval : forall n p x,
  qpoly_eval (qpoly_deriv_from (S n) p) x ==
    qpoly_eval (qpoly_deriv_from n p) x + qpoly_eval p x.
Proof.
  intros n p. revert n.
  induction p as [|a ps IH]; intros n x; simpl.
  - ring.
  - setoid_rewrite (IH (S n) x).
    simpl qnat.
    ring.
Qed.

Lemma qpoly_deriv_add_eval : forall p q x,
  qpoly_eval (qpoly_deriv (qpoly_add p q)) x ==
    qpoly_eval (qpoly_deriv p) x
    + qpoly_eval (qpoly_deriv q) x.
Proof.
  intros [|a ps] [|b qs] x; simpl; try ring.
  apply deriv_from_add_eval.
Qed.

Lemma qpoly_deriv_scale_eval : forall c p x,
  qpoly_eval (qpoly_deriv (qpoly_scale c p)) x ==
    c * qpoly_eval (qpoly_deriv p) x.
Proof.
  intros c [|a ps] x; simpl; [ring|].
  apply deriv_from_scale_eval.
Qed.

(** The derivative of x*p is p + x*p', established on coefficients. *)
Lemma qpoly_deriv_shift_eval : forall p x,
  qpoly_eval (qpoly_deriv (0 :: p)) x ==
    qpoly_eval p x + x * qpoly_eval (qpoly_deriv p) x.
Proof.
  intros [|a ps] x; simpl.
  - ring.
  - setoid_rewrite (deriv_from_step_eval 1 ps x).
    ring.
Qed.

(** True finite-code Leibniz law: the derivative syntax of the product
    compiler computes the expected derivative at every rational x. *)
Theorem qpoly_deriv_mul_eval : forall p q x,
  qpoly_eval (qpoly_deriv (qpoly_mul p q)) x ==
    qpoly_eval (qpoly_deriv p) x * qpoly_eval q x
      + qpoly_eval p x * qpoly_eval (qpoly_deriv q) x.
Proof.
  intro p. induction p as [|a ps IH]; intros q x.
  - simpl. ring.
  - simpl qpoly_mul.
    setoid_rewrite qpoly_deriv_add_eval.
    setoid_rewrite qpoly_deriv_scale_eval.
    setoid_rewrite qpoly_deriv_shift_eval.
    setoid_rewrite (qpoly_eval_mul_sound ps q x).
    setoid_rewrite (IH q x).
    assert (Hshift :
      qpoly_eval (qpoly_deriv (a :: ps)) x ==
        qpoly_eval ps x + x * qpoly_eval (qpoly_deriv ps) x).
    { exact (qpoly_deriv_shift_eval ps x). }
    setoid_rewrite Hshift.
    simpl qpoly_eval.
    ring.
Qed.

(** Each hat restriction to a rational cell is affine. This is its
    exact compiler-level product rule, not an assumed analytic primitive. *)
Corollary affine_hat_product_derivative : forall a b p x,
  qpoly_eval (qpoly_deriv (qpoly_mul [a;b] p)) x ==
    b * qpoly_eval p x
      + (a + b * x) * qpoly_eval (qpoly_deriv p) x.
Proof.
  intros a b p x.
  setoid_rewrite qpoly_deriv_mul_eval.
  simpl.
  ring.
Qed.

Lemma integral_from_scale_eval : forall n a b c p,
  qpoly_integral_between_from n a b (qpoly_scale c p) ==
    c * qpoly_integral_between_from n a b p.
Proof.
  intros n a b c p. revert n.
  induction p as [|y ys IH]; intros n; simpl.
  - ring.
  - setoid_rewrite (IH (S n)).
    unfold Qdiv.
    ring.
Qed.

Lemma integral_from_add_eval : forall n a b p q,
  qpoly_integral_between_from n a b (qpoly_add p q) ==
    qpoly_integral_between_from n a b p
      + qpoly_integral_between_from n a b q.
Proof.
  intros n a b p. revert n.
  induction p as [|y ys IH]; intros n [|z zs]; simpl; try ring.
  setoid_rewrite (IH (S n) zs).
  unfold Qdiv.
  ring.
Qed.

(** Linearity of the concrete rational exact-integral evaluator. *)
Theorem qpoly_integral_add_sound : forall a b p q,
  qpoly_integral_between a b (qpoly_add p q) ==
    qpoly_integral_between a b p
      + qpoly_integral_between a b q.
Proof.
  intros. unfold qpoly_integral_between.
  apply integral_from_add_eval.
Qed.

Theorem qpoly_integral_scale_sound : forall a b c p,
  qpoly_integral_between a b (qpoly_scale c p) ==
    c * qpoly_integral_between a b p.
Proof.
  intros. unfold qpoly_integral_between.
  apply integral_from_scale_eval.
Qed.

End UELAT_V3_RationalPolynomialSemantic.
