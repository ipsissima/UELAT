(** RationalFiniteOperations.v -- arbitrary-mesh finite operations for Lemma 5.2. *)

From Coq Require Import QArith List Arith Lia Lia.
Import ListNotations.
Local Open Scope Q_scope.
From UELAT.V3 Require Import RationalSobolev RationalArbitraryMesh.

Module UELAT_V3_RationalFiniteOperations.
Import UELAT_V3_RationalSobolev.
Import UELAT_V3_RationalArbitraryMesh.

Definition intersection_piece_with
    (op : QPoly -> QPoly -> QPoly)
    (u v : RationalPiece) : option RationalPiece :=
  if positive_overlapb u v then
    Some {| piece_left := overlap_left u v;
            piece_right := overlap_right u v;
            piece_poly := op (piece_poly u) (piece_poly v) |}
  else None.

Definition add_intersection_piece := intersection_piece_with qpoly_add.
Definition mul_intersection_piece := intersection_piece_with qpoly_mul.

Fixpoint collect_against
    (op : QPoly -> QPoly -> QPoly)
    (u : RationalPiece) (ys : list RationalPiece) : list RationalPiece :=
  match ys with
  | [] => []
  | v :: rest =>
      match intersection_piece_with op u v with
      | Some c => c :: collect_against op u rest
      | None => collect_against op u rest
      end
  end.

Fixpoint common_refined_operation
    (op : QPoly -> QPoly -> QPoly)
    (xs ys : list RationalPiece) : list RationalPiece :=
  match xs with
  | [] => []
  | u :: rest => collect_against op u ys ++ common_refined_operation op rest ys
  end.

Definition common_add_pieces := common_refined_operation qpoly_add.
Definition common_mul_pieces := common_refined_operation qpoly_mul.

Fixpoint common_scale_pieces (a : Q) (xs : list RationalPiece) : list RationalPiece :=
  match xs with
  | [] => []
  | u :: rest =>
      {| piece_left := piece_left u;
         piece_right := piece_right u;
         piece_poly := qpoly_scale a (piece_poly u) |}
      :: common_scale_pieces a rest
  end.

Fixpoint derivative_pieces (xs : list RationalPiece) : list RationalPiece :=
  match xs with
  | [] => []
  | u :: rest =>
      {| piece_left := piece_left u;
         piece_right := piece_right u;
         piece_poly := qpoly_deriv (piece_poly u) |}
      :: derivative_pieces rest
  end.

Definition restrict_piece (a b : Q) (u : RationalPiece) : option RationalPiece :=
  let l := qmax a (piece_left u) in
  let r := qmin b (piece_right u) in
  if Qlt_le_dec l r then
    Some {| piece_left := l; piece_right := r; piece_poly := piece_poly u |}
  else None.

Fixpoint restrict_pieces (a b : Q) (xs : list RationalPiece) : list RationalPiece :=
  match xs with
  | [] => []
  | u :: rest =>
      match restrict_piece a b u with
      | Some c => c :: restrict_pieces a b rest
      | None => restrict_pieces a b rest
      end
  end.

Theorem common_add_is_finite : forall xs ys,
  exists zs : list RationalPiece, zs = common_add_pieces xs ys.
Proof. intros. eexists. reflexivity. Qed.
Theorem common_mul_is_finite : forall xs ys,
  exists zs : list RationalPiece, zs = common_mul_pieces xs ys.
Proof. intros. eexists. reflexivity. Qed.
Theorem common_scale_is_finite : forall a xs,
  exists zs : list RationalPiece, zs = common_scale_pieces a xs.
Proof. intros. eexists. reflexivity. Qed.
Theorem restriction_is_finite : forall a b xs,
  exists zs : list RationalPiece, zs = restrict_pieces a b xs.
Proof. intros. eexists. reflexivity. Qed.
Theorem derivative_is_finite : forall xs,
  exists zs : list RationalPiece, zs = derivative_pieces xs.
Proof. intros. eexists. reflexivity. Qed.

Lemma collect_against_length_le : forall op u ys,
  (length (collect_against op u ys) <= length ys)%nat.
Proof.
  intros op u ys. induction ys as [|v rest IH]; simpl.
  - lia.
  - unfold intersection_piece_with at 1.
    destruct (positive_overlapb u v); simpl; lia.
Qed.

Theorem common_refined_operation_length_le : forall op xs ys,
  (length (common_refined_operation op xs ys) <= length xs * length ys)%nat.
Proof.
  intros op xs. induction xs as [|u rest IH]; intro ys; simpl.
  - lia.
  - rewrite app_length.
    pose proof (collect_against_length_le op u ys).
    specialize (IH ys). nia.
Qed.

Corollary common_add_length_le : forall xs ys,
  (length (common_add_pieces xs ys) <= length xs * length ys)%nat.
Proof. apply common_refined_operation_length_le. Qed.
Corollary common_mul_length_le : forall xs ys,
  (length (common_mul_pieces xs ys) <= length xs * length ys)%nat.
Proof. apply common_refined_operation_length_le. Qed.

Lemma common_scale_length : forall a xs,
  length (common_scale_pieces a xs) = length xs.
Proof. intros a xs. induction xs; simpl; congruence. Qed.
Lemma derivative_pieces_length : forall xs,
  length (derivative_pieces xs) = length xs.
Proof. intro xs. induction xs; simpl; congruence. Qed.
Lemma restrict_pieces_length_le : forall a b xs,
  (length (restrict_pieces a b xs) <= length xs)%nat.
Proof.
  intros a b xs. induction xs as [|u rest IH]; simpl.
  - lia.
  - unfold restrict_piece at 1.
    destruct (Qlt_le_dec (qmax a (piece_left u)) (qmin b (piece_right u)));
      simpl; lia.
Qed.

Record ExactFiniteW12Arithmetic (u v : RationalPiecewiseCode) := {
  efwa_inner : Q;
  efwa_sqdist : Q;
  efwa_add : list RationalPiece;
  efwa_mul : list RationalPiece;
  efwa_scale_u : Q -> list RationalPiece;
  efwa_restrict_u : Q -> Q -> list RationalPiece;
  efwa_inner_eq : efwa_inner = arbitrary_mesh_inner u v;
  efwa_sqdist_eq : efwa_sqdist = arbitrary_mesh_sqdist u v;
  efwa_add_eq : efwa_add = common_add_pieces (rpc_pieces u) (rpc_pieces v);
  efwa_mul_eq : efwa_mul = common_mul_pieces (rpc_pieces u) (rpc_pieces v);
  efwa_scale_eq : forall a, efwa_scale_u a = common_scale_pieces a (rpc_pieces u);
  efwa_restrict_eq : forall a b, efwa_restrict_u a b = restrict_pieces a b (rpc_pieces u)
}.

Definition compute_exact_finite_w12
    (u v : RationalPiecewiseCode) : ExactFiniteW12Arithmetic u v :=
  {| efwa_inner := arbitrary_mesh_inner u v;
     efwa_sqdist := arbitrary_mesh_sqdist u v;
     efwa_add := common_add_pieces (rpc_pieces u) (rpc_pieces v);
     efwa_mul := common_mul_pieces (rpc_pieces u) (rpc_pieces v);
     efwa_scale_u := fun a => common_scale_pieces a (rpc_pieces u);
     efwa_restrict_u := fun a b => restrict_pieces a b (rpc_pieces u);
     efwa_inner_eq := eq_refl;
     efwa_sqdist_eq := eq_refl;
     efwa_add_eq := eq_refl;
     efwa_mul_eq := eq_refl;
     efwa_scale_eq := fun _ => eq_refl;
     efwa_restrict_eq := fun _ _ => eq_refl |}.

Theorem lemma_5_2_finite_arithmetic_is_executable : forall u v,
  exists A : ExactFiniteW12Arithmetic u v,
    efwa_inner A = arbitrary_mesh_inner u v
    /\ efwa_sqdist A = arbitrary_mesh_sqdist u v.
Proof.
  intros u v. exists (compute_exact_finite_w12 u v). split; reflexivity.
Qed.

End UELAT_V3_RationalFiniteOperations.
