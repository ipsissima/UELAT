(**
  RationalRealPolynomialSemantics.v -- the concrete QPoly-to-R-function
  interpretation required by manuscript Theorem 5.6.

  These statements are about the real-valued polynomial represented by
  rational coefficients. Multiplication of finite rational codes
  coincides with multiplication of their interpreted real functions.
  The rational-stage Horner evaluator agrees with this interpretation
  on every rational point.

  Not yet shown: integration against Lebesgue measure, piecewise
  weak derivatives, Sobolev boundary matching, or the full estimates.
*)
From Coq Require Import Reals QArith Qreals List Lra Ring.
Import ListNotations.
Local Open Scope R_scope.

From UELAT.V3 Require Import RationalSobolev.

Module UELAT_V3_RationalRealPolynomialSemantics.
Import UELAT_V3_RationalSobolev.

Lemma Q2R_zero_local : Q2R (0 : Q) = 0.
Proof.
  pose proof (Q2R_plus (0 : Q) (0 : Q)) as H.
  replace ((0 + 0)%Q) with (0 : Q) in H by reflexivity.
  lra.
Qed.

(** Direct real-valued semantics, obtained by Horner evaluation. *)
Fixpoint rpoly_eval (p : QPoly) (x : R) : R :=
  match p with
  | [] => 0
  | a :: ps => Q2R a + x * rpoly_eval ps x
  end.

Theorem rpoly_rational_stage_agrees : forall p q,
  rpoly_eval p (Q2R q) = Q2R (qpoly_eval p q).
Proof.
  intro p. induction p as [|a ps IH]; intro q; simpl.
  - symmetry. apply Q2R_zero_local.
  - rewrite Q2R_plus.
    rewrite Q2R_mult.
    rewrite <- IH.
    ring.
Qed.

Theorem rpoly_eval_add_sound : forall p q x,
  rpoly_eval (qpoly_add p q) x =
    rpoly_eval p x + rpoly_eval q x.
Proof.
  intro p. induction p as [|a ps IH]; intros [|b qs] x;
    simpl; try ring.
  rewrite Q2R_plus.
  rewrite (IH qs x).
  ring.
Qed.

Theorem rpoly_eval_scale_sound : forall c p x,
  rpoly_eval (qpoly_scale c p) x =
    Q2R c * rpoly_eval p x.
Proof.
  intros c p. induction p as [|a ps IH]; intro x; simpl.
  - ring.
  - rewrite Q2R_mult, IH.
    ring.
Qed.

(** Polynomial multiplication in the executable rational syntax agrees
    with multiplication of its interpreted functions at every real x. *)
Theorem rpoly_eval_mul_sound : forall p q x,
  rpoly_eval (qpoly_mul p q) x =
    rpoly_eval p x * rpoly_eval q x.
Proof.
  intro p. induction p as [|a ps IH]; intros q x.
  - simpl. ring.
  - simpl qpoly_mul.
    rewrite rpoly_eval_add_sound.
    rewrite rpoly_eval_scale_sound.
    simpl rpoly_eval.
    rewrite Q2R_zero_local.
    rewrite (IH q x).
    ring.
Qed.

End UELAT_V3_RationalRealPolynomialSemantics.
