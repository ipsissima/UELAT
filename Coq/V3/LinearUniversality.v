(** LinearUniversality.v -- v3 Section 3 formalization track.

    The full effective Banach--Mazur theorem requires a substantial computable-
    analysis library (effective approximate Hahn--Banach, computable compacta,
    Cantor surjections, and function-space realizers).  This file formalizes the
    first invariant mathematical core used by that construction:

      a countable 1-norming family of linear coordinates gives a linear
      evaluation representation whose coordinate sup is exactly the norm, in
      the epsilon characterization of a supremum.

    It also records the final finite-code consequence from a dense ambient code
    presentation.  These are genuine theorem components but not yet a machine
    check of manuscript Theorem 3.2 as a whole.
*)

From Coq Require Import Reals Lra.

Module UELAT_V3_LinearUniversality.

Section NormingEvaluation.

  Context {X : Type}.
  Variable zero : X.
  Variable add : X -> X -> X.
  Variable smul : R -> X -> X.
  Variable norm : X -> R.

  Variable coord : nat -> X -> R.

  Hypothesis coord_add : forall j x y,
      coord j (add x y) = coord j x + coord j y.
  Hypothesis coord_smul : forall j a x,
      coord j (smul a x) = a * coord j x.

  Hypothesis coord_contracting : forall j x,
      Rabs (coord j x) <= norm x.

  Hypothesis one_norming : forall x eta,
      0 < eta ->
      exists j, norm x - eta < Rabs (coord j x).

  Definition evaluation (x : X) : nat -> R := fun j => coord j x.

  Theorem evaluation_linear_add : forall x y j,
    evaluation (add x y) j = evaluation x j + evaluation y j.
  Proof.
    intros. unfold evaluation. apply coord_add.
  Qed.

  Theorem evaluation_linear_smul : forall a x j,
    evaluation (smul a x) j = a * evaluation x j.
  Proof.
    intros. unfold evaluation. apply coord_smul.
  Qed.

  Theorem evaluation_sup_upper : forall x j,
    Rabs (evaluation x j) <= norm x.
  Proof.
    intros. unfold evaluation. apply coord_contracting.
  Qed.

  Theorem evaluation_sup_lower_arbitrarily_close : forall x eta,
    0 < eta ->
    exists j, norm x - eta < Rabs (evaluation x j).
  Proof.
    intros x eta Heta.
    unfold evaluation.
    now apply one_norming.
  Qed.

  Theorem evaluation_isometric_sup_characterization : forall x,
    (forall j, Rabs (evaluation x j) <= norm x) /\
    (forall eta, 0 < eta ->
       exists j, norm x - eta < Rabs (evaluation x j)).
  Proof.
    intro x. split.
    - apply evaluation_sup_upper.
    - apply evaluation_sup_lower_arbitrarily_close.
  Qed.

End NormingEvaluation.

Section DenseAmbientCodes.

  Context {X Y Code : Type}.
  Variable J : X -> Y.
  Variable decode : Code -> Y.
  Variable dist : Y -> Y -> R.

  Hypothesis finite_code_dense : forall y eps,
      0 < eps -> exists p : Code, dist y (decode p) < eps.

  Theorem embedded_points_have_finite_codes : forall x eps,
    0 < eps -> exists p : Code, dist (J x) (decode p) < eps.
  Proof.
    intros x eps Heps.
    now apply finite_code_dense.
  Qed.

End DenseAmbientCodes.

End UELAT_V3_LinearUniversality.
