(** RationalCommonMesh.v -- executable arbitrary rational mesh refinement.

    The finite W12 arithmetic of RationalSobolev.v is exact once two codes are
    aligned. RationalMeshRefinement.v proved that one rational cell split is
    exact. This file implements repeated insertion of arbitrary rational
    breakpoints into every piece and proves that the exact W12 self-energy is
    unchanged. Applying the union of the two finite breakpoint lists to both
    input codes is the concrete common-refinement algorithm used by Lemma 5.2.

    The final proof that two well-formed partitions of the same domain acquire
    literally identical interval lists after union refinement is separated as a
    mesh-combinatorics lemma; semantic exactness of every insertion is proved
    here.
*)

From Coq Require Import QArith List Arith Lia Lqa Qring.
Import ListNotations.
Local Open Scope Q_scope.
From UELAT.V3 Require Import RationalSobolev RationalMeshRefinement.

Module UELAT_V3_RationalCommonMesh.
Import UELAT_V3_RationalSobolev.
Import UELAT_V3_RationalMeshRefinement.

Definition strictly_inside_piece (x : Q) (c : RationalPiece) : bool :=
  if Qlt_le_dec (piece_left c) x then
    if Qlt_le_dec x (piece_right c) then true else false
  else false.

Lemma strictly_inside_piece_spec : forall x c,
  strictly_inside_piece x c = true <->
    (piece_left c < x)%Q /\ (x < piece_right c)%Q.
Proof.
  intros x c. unfold strictly_inside_piece.
  destruct (Qlt_le_dec (piece_left c) x) as [Hl|Hl].
  - destruct (Qlt_le_dec x (piece_right c)) as [Hr|Hr].
    + split; intro H; [now split|reflexivity].
    + split; intro H.
      * discriminate.
      * destruct H as [_ Hx]. exfalso. now apply (Qlt_not_le _ _ Hx).
  - split; intro H.
    + discriminate.
    + destruct H as [Hx _]. exfalso. now apply (Qlt_not_le _ _ Hx).
Qed.

Definition split_piece_at (x : Q) (c : RationalPiece) : list RationalPiece :=
  if strictly_inside_piece x c then
    [ {| piece_left := piece_left c;
         piece_right := x;
         piece_poly := piece_poly c |};
      {| piece_left := x;
         piece_right := piece_right c;
         piece_poly := piece_poly c |} ]
  else [c].

Lemma split_piece_at_length : forall x c,
  length (split_piece_at x c) = 1 \/ length (split_piece_at x c) = 2.
Proof.
  intros x c. unfold split_piece_at.
  destruct (strictly_inside_piece x c); simpl; auto.
Qed.

Definition piece_energy (c : RationalPiece) : Q :=
  qpoly_w12_inner_on (piece_left c) (piece_right c)
    (piece_poly c) (piece_poly c).

Fixpoint pieces_energy (cs : list RationalPiece) : Q :=
  match cs with
  | [] => 0
  | c :: rest => piece_energy c + pieces_energy rest
  end.

Lemma pieces_energy_app : forall xs ys,
  pieces_energy (xs ++ ys) == pieces_energy xs + pieces_energy ys.
Proof.
  intros xs ys. induction xs as [|x xs IH]; simpl.
  - ring.
  - rewrite IH. ring.
Qed.

Lemma split_piece_at_energy : forall x c,
  pieces_energy (split_piece_at x c) == piece_energy c.
Proof.
  intros x c. unfold split_piece_at.
  destruct (strictly_inside_piece x c) eqn:Hinside.
  - simpl. unfold piece_energy. simpl.
    rewrite <- qpoly_w12_inner_split. ring.
  - simpl. ring.
Qed.

Fixpoint refine_pieces_at (x : Q) (cs : list RationalPiece) : list RationalPiece :=
  match cs with
  | [] => []
  | c :: rest => split_piece_at x c ++ refine_pieces_at x rest
  end.

Lemma refine_pieces_at_energy : forall x cs,
  pieces_energy (refine_pieces_at x cs) == pieces_energy cs.
Proof.
  intros x cs. induction cs as [|c rest IH]; simpl.
  - reflexivity.
  - rewrite pieces_energy_app.
    rewrite split_piece_at_energy, IH. ring.
Qed.

Fixpoint refine_by_points (points : list Q) (cs : list RationalPiece) : list RationalPiece :=
  match points with
  | [] => cs
  | x :: xs => refine_by_points xs (refine_pieces_at x cs)
  end.

Theorem refine_by_points_energy : forall points cs,
  pieces_energy (refine_by_points points cs) == pieces_energy cs.
Proof.
  intros points cs. induction points as [|x xs IH]; simpl.
  - reflexivity.
  - rewrite IH. apply refine_pieces_at_energy.
Qed.

Definition internal_breakpoints (cs : list RationalPiece) : list Q :=
  match cs with
  | [] => []
  | _ :: rest => map piece_left rest
  end.

Definition common_breakpoints
    (xs ys : list RationalPiece) : list Q :=
  internal_breakpoints xs ++ internal_breakpoints ys.

Definition refine_pair_to_union
    (xs ys : list RationalPiece) : list RationalPiece * list RationalPiece :=
  let points := common_breakpoints xs ys in
  (refine_by_points points xs, refine_by_points points ys).

Theorem refine_pair_left_energy : forall xs ys,
  pieces_energy (fst (refine_pair_to_union xs ys)) == pieces_energy xs.
Proof.
  intros. unfold refine_pair_to_union. simpl.
  apply refine_by_points_energy.
Qed.

Theorem refine_pair_right_energy : forall xs ys,
  pieces_energy (snd (refine_pair_to_union xs ys)) == pieces_energy ys.
Proof.
  intros. unfold refine_pair_to_union. simpl.
  apply refine_by_points_energy.
Qed.

Lemma refine_pieces_at_length_le_double : forall x cs,
  length (refine_pieces_at x cs) <= 2 * length cs.
Proof.
  intros x cs. induction cs as [|c rest IH]; simpl.
  - lia.
  - rewrite app_length.
    pose proof (split_piece_at_length x c) as Hlen.
    destruct Hlen; nia.
Qed.

End UELAT_V3_RationalCommonMesh.
