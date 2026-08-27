(** LinearUniversality.v -- authoritative Section 3 formalization track.

    A 1-norming family of linear coordinates gives a linear evaluation
    representation whose coordinate supremum is exactly the norm, in the
    epsilon characterization of a supremum. The indexed section supports the
    explicit three-parameter effective Hahn--Banach candidate family; the
    natural-number section records the flattened presentation used by the paper.
*)

From Coq Require Import Reals Lra.

Module UELAT_V3_LinearUniversality.

Section IndexedNormingEvaluation.
  Context {Index X : Type}.
  Variable zero : X.
  Variable add : X -> X -> X.
  Variable smul : R -> X -> X.
  Variable norm : X -> R.
  Variable icoord : Index -> X -> R.

  Hypothesis icoord_add : forall j x y,
      icoord j (add x y) = icoord j x + icoord j y.
  Hypothesis icoord_smul : forall j a x,
      icoord j (smul a x) = a * icoord j x.
  Hypothesis icoord_contracting : forall j x,
      Rabs (icoord j x) <= norm x.
  Hypothesis indexed_one_norming : forall x eta,
      0 < eta -> exists j,
        norm x - eta < Rabs (icoord j x).

  Definition indexed_evaluation (x : X) : Index -> R := fun j => icoord j x.

  Theorem indexed_evaluation_linear_add : forall x y j,
    indexed_evaluation (add x y) j
      = indexed_evaluation x j + indexed_evaluation y j.
  Proof. intros. unfold indexed_evaluation. apply icoord_add. Qed.

  Theorem indexed_evaluation_linear_smul : forall a x j,
    indexed_evaluation (smul a x) j = a * indexed_evaluation x j.
  Proof. intros. unfold indexed_evaluation. apply icoord_smul. Qed.

  Theorem indexed_evaluation_isometric_sup_characterization : forall x,
    (forall j, Rabs (indexed_evaluation x j) <= norm x)
    /\ (forall eta, 0 < eta ->
          exists j, norm x - eta < Rabs (indexed_evaluation x j)).
  Proof.
    intro x. split.
    - intro j. unfold indexed_evaluation. apply icoord_contracting.
    - intros eta Heta. unfold indexed_evaluation. now apply indexed_one_norming.
  Qed.
End IndexedNormingEvaluation.

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
      0 < eta -> exists j, norm x - eta < Rabs (coord j x).

  Definition evaluation (x : X) : nat -> R := fun j => coord j x.

  Theorem evaluation_linear_add : forall x y j,
    evaluation (add x y) j = evaluation x j + evaluation y j.
  Proof. intros. unfold evaluation. apply coord_add. Qed.
  Theorem evaluation_linear_smul : forall a x j,
    evaluation (smul a x) j = a * evaluation x j.
  Proof. intros. unfold evaluation. apply coord_smul. Qed.
  Theorem evaluation_sup_upper : forall x j,
    Rabs (evaluation x j) <= norm x.
  Proof. intros. unfold evaluation. apply coord_contracting. Qed.
  Theorem evaluation_sup_lower_arbitrarily_close : forall x eta,
    0 < eta -> exists j, norm x - eta < Rabs (evaluation x j).
  Proof. intros x eta Heta. unfold evaluation. now apply one_norming. Qed.
  Theorem evaluation_isometric_sup_characterization : forall x,
    (forall j, Rabs (evaluation x j) <= norm x) /\
    (forall eta, 0 < eta -> exists j, norm x - eta < Rabs (evaluation x j)).
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
  Proof. intros x eps Heps. now apply finite_code_dense. Qed.
End DenseAmbientCodes.

End UELAT_V3_LinearUniversality.
