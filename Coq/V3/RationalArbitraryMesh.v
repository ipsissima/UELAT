(** RationalArbitraryMesh.v -- exact finite W12 arithmetic without prior mesh alignment.

    Lemma 5.2 needs a terminating exact rational procedure for finite
    piecewise-polynomial codes. Summing polynomial integrals over nonempty
    pairwise cell intersections provides that procedure directly.
*)

From Coq Require Import QArith List.
Import ListNotations.
Local Open Scope Q_scope.
From UELAT.V3 Require Import RationalSobolev.

Module UELAT_V3_RationalArbitraryMesh.
Import UELAT_V3_RationalSobolev.

Definition qmax (a b : Q) : Q := if Qlt_le_dec a b then b else a.
Definition qmin (a b : Q) : Q := if Qlt_le_dec a b then a else b.
Definition overlap_left (u v : RationalPiece) : Q := qmax (piece_left u) (piece_left v).
Definition overlap_right (u v : RationalPiece) : Q := qmin (piece_right u) (piece_right v).

Definition positive_overlapb (u v : RationalPiece) : bool :=
  if Qlt_le_dec (overlap_left u v) (overlap_right u v) then true else false.

Definition pair_w12_inner (u v : RationalPiece) : Q :=
  if positive_overlapb u v then
    qpoly_w12_inner_on (overlap_left u v) (overlap_right u v)
      (piece_poly u) (piece_poly v)
  else 0.

Fixpoint inner_piece_against_list
    (u : RationalPiece) (ys : list RationalPiece) : Q :=
  match ys with
  | [] => 0
  | v :: rest => pair_w12_inner u v + inner_piece_against_list u rest
  end.

Fixpoint arbitrary_mesh_inner_raw (xs ys : list RationalPiece) : Q :=
  match xs with
  | [] => 0
  | u :: rest => inner_piece_against_list u ys + arbitrary_mesh_inner_raw rest ys
  end.

Definition arbitrary_mesh_inner (u v : RationalPiecewiseCode) : Q :=
  arbitrary_mesh_inner_raw (rpc_pieces u) (rpc_pieces v).

Definition arbitrary_mesh_sqdist (u v : RationalPiecewiseCode) : Q :=
  arbitrary_mesh_inner u u + arbitrary_mesh_inner v v - 2 * arbitrary_mesh_inner u v.

Theorem arbitrary_mesh_inner_is_exact_rational : forall u v,
  exists q : Q, q = arbitrary_mesh_inner u v.
Proof. intros. eexists. reflexivity. Qed.

Theorem arbitrary_mesh_sqdist_is_exact_rational : forall u v,
  exists q : Q, q = arbitrary_mesh_sqdist u v.
Proof. intros. eexists. reflexivity. Qed.

Theorem arbitrary_mesh_arithmetic_terminates_on_finite_codes : forall u v,
  exists qinner qdist : Q,
    qinner = arbitrary_mesh_inner u v /\ qdist = arbitrary_mesh_sqdist u v.
Proof. intros. repeat eexists; reflexivity. Qed.

Lemma arbitrary_mesh_inner_raw_nil_l : forall ys,
  arbitrary_mesh_inner_raw [] ys = 0.
Proof. reflexivity. Qed.

Lemma inner_piece_against_list_nil : forall u,
  inner_piece_against_list u [] = 0.
Proof. reflexivity. Qed.

Theorem pair_overlap_endpoints_are_rational : forall u v,
  exists a b : Q,
    a = overlap_left u v /\ b = overlap_right u v.
Proof. intros. repeat eexists; reflexivity. Qed.

End UELAT_V3_RationalArbitraryMesh.
