(** RationalMeshRefinement.v -- exact common-mesh refinement core for v3 Lemma 5.2.

    RationalSobolev.v computes W^{1,2} quantities exactly on an aligned mesh.
    This file proves that inserting a rational breakpoint and duplicating the
    polynomial pieces on the two subcells preserves the exact integral.  By
    iteration this is the algebraic fact needed to pass two rational meshes to
    any common refinement without changing their represented finite functions.
*)

From Coq Require Import QArith List Ring.
Import ListNotations.
Local Open Scope Q_scope.
From UELAT.V3 Require Import RationalSobolev.

Module UELAT_V3_RationalMeshRefinement.
Import UELAT_V3_RationalSobolev.

Lemma qpoly_integral_between_from_additive :
  forall p n a b c,
    qpoly_integral_between_from n a c p
      = qpoly_integral_between_from n a b p
        + qpoly_integral_between_from n b c p.
Proof.
  induction p as [|x xs IH]; intros n a b c; simpl.
  - ring.
  - rewrite (IH (S n) a b c). ring.
Qed.

Theorem qpoly_integral_between_additive : forall p a b c,
  qpoly_integral_between a c p
    = qpoly_integral_between a b p + qpoly_integral_between b c p.
Proof.
  intros. unfold qpoly_integral_between.
  apply qpoly_integral_between_from_additive.
Qed.

Theorem qpoly_l2_inner_split : forall p q a b c,
  qpoly_l2_inner_on a c p q
    = qpoly_l2_inner_on a b p q + qpoly_l2_inner_on b c p q.
Proof.
  intros. unfold qpoly_l2_inner_on.
  apply qpoly_integral_between_additive.
Qed.

Theorem qpoly_w12_inner_split : forall p q a b c,
  qpoly_w12_inner_on a c p q
    = qpoly_w12_inner_on a b p q + qpoly_w12_inner_on b c p q.
Proof.
  intros. unfold qpoly_w12_inner_on.
  rewrite (qpoly_l2_inner_split p q a b c).
  rewrite (qpoly_l2_inner_split (qpoly_deriv p) (qpoly_deriv q) a b c).
  ring.
Qed.

Theorem qpoly_w12_sqdist_split : forall p q a b c,
  qpoly_w12_sqdist_on a c p q
    = qpoly_w12_sqdist_on a b p q + qpoly_w12_sqdist_on b c p q.
Proof.
  intros. unfold qpoly_w12_sqdist_on.
  apply qpoly_w12_inner_split.
Qed.

Definition split_piece (mid : Q) (c : RationalPiece) : list RationalPiece :=
  [ {| piece_left := piece_left c;
       piece_right := mid;
       piece_poly := piece_poly c |};
    {| piece_left := mid;
       piece_right := piece_right c;
       piece_poly := piece_poly c |} ].

Theorem split_piece_preserves_polynomial : forall c mid x,
  qpoly_eval (piece_poly (hd c (split_piece mid c))) x
    = qpoly_eval (piece_poly c) x.
Proof.
  intros. reflexivity.
Qed.

Definition split_pair_w12
    (mid : Q) (u v : RationalPiece) : Q :=
  qpoly_w12_inner_on (piece_left u) mid
    (piece_poly u) (piece_poly v)
  + qpoly_w12_inner_on mid (piece_right u)
    (piece_poly u) (piece_poly v).

Theorem aligned_piece_split_preserves_w12 : forall u v mid,
  Qeq (piece_left u) (piece_left v) ->
  Qeq (piece_right u) (piece_right v) ->
  split_pair_w12 mid u v
    = qpoly_w12_inner_on (piece_left u) (piece_right u)
        (piece_poly u) (piece_poly v).
Proof.
  intros u v mid Hl Hr.
  unfold split_pair_w12.
  symmetry.
  apply qpoly_w12_inner_split.
Qed.

(** A finite refinement certificate records a sequence of rational split
    points.  Each step is exact by [qpoly_w12_inner_split]; the concrete merge
    algorithm for arbitrary sorted breakpoint lists is kept separate from this
    invariant theorem. *)
Record MeshRefinementCertificate := {
  refinement_points : list Q
}.

Theorem one_split_exactness : forall p q a b c,
  qpoly_w12_sqdist_on a c p q
    = qpoly_w12_sqdist_on a b p q
      + qpoly_w12_sqdist_on b c p q.
Proof.
  apply qpoly_w12_sqdist_split.
Qed.

End UELAT_V3_RationalMeshRefinement.
