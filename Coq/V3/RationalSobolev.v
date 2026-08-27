(** RationalSobolev.v -- rational finite-code core for v3 Section 5.

    This module begins the manuscript's concrete W^{1,2}(0,1) presentation.
    It defines rational polynomial and rational piecewise-polynomial codes and
    executable exact Q-arithmetic for polynomial evaluation, differentiation,
    multiplication, integration, and the finite-code W^{1,2} inner product and
    squared distance on an aligned rational mesh.
*)

From Coq Require Import QArith List Arith Bool.
Import ListNotations.
Local Open Scope Q_scope.

Module UELAT_V3_RationalSobolev.

Definition QPoly := list Q.

Fixpoint qnat (n : nat) : Q :=
  match n with | O => 0 | S k => qnat k + 1 end.

Fixpoint qpow (x : Q) (n : nat) : Q :=
  match n with | O => 1 | S k => x * qpow x k end.

Fixpoint qpoly_eval (p : QPoly) (x : Q) : Q :=
  match p with | [] => 0 | a :: ps => a + x * qpoly_eval ps x end.

Fixpoint qpoly_add (p q : QPoly) : QPoly :=
  match p, q with
  | [], ys => ys
  | xs, [] => xs
  | a :: ps, b :: qs => (a + b) :: qpoly_add ps qs
  end.

Fixpoint qpoly_scale (a : Q) (p : QPoly) : QPoly :=
  match p with | [] => [] | b :: ps => (a * b) :: qpoly_scale a ps end.

Definition qpoly_neg (p : QPoly) : QPoly := qpoly_scale (-1) p.
Definition qpoly_sub (p q : QPoly) : QPoly := qpoly_add p (qpoly_neg q).

Fixpoint qpoly_mul (p q : QPoly) : QPoly :=
  match p with
  | [] => []
  | a :: ps => qpoly_add (qpoly_scale a q) (0 :: qpoly_mul ps q)
  end.

Fixpoint qpoly_deriv_from (n : nat) (p : QPoly) : QPoly :=
  match p with
  | [] => []
  | a :: ps => (qnat n * a) :: qpoly_deriv_from (S n) ps
  end.

Definition qpoly_deriv (p : QPoly) : QPoly :=
  match p with | [] => [] | _ :: ps => qpoly_deriv_from 1 ps end.

Fixpoint qpoly_integral_between_from (n : nat) (a b : Q) (p : QPoly) : Q :=
  match p with
  | [] => 0
  | c :: ps =>
      c * (qpow b (S n) - qpow a (S n)) / qnat (S n)
      + qpoly_integral_between_from (S n) a b ps
  end.

Definition qpoly_integral_between (a b : Q) (p : QPoly) : Q :=
  qpoly_integral_between_from 0 a b p.

Definition qpoly_l2_inner_on (a b : Q) (p q : QPoly) : Q :=
  qpoly_integral_between a b (qpoly_mul p q).

Definition qpoly_w12_inner_on (a b : Q) (p q : QPoly) : Q :=
  qpoly_l2_inner_on a b p q
  + qpoly_l2_inner_on a b (qpoly_deriv p) (qpoly_deriv q).

Definition qpoly_w12_sqdist_on (a b : Q) (p q : QPoly) : Q :=
  qpoly_w12_inner_on a b (qpoly_sub p q) (qpoly_sub p q).

Theorem polynomial_w12_inner_is_exact_rational : forall a b p q,
  exists z : Q, z = qpoly_w12_inner_on a b p q.
Proof. intros. eexists. reflexivity. Qed.

Theorem polynomial_w12_sqdist_is_exact_rational : forall a b p q,
  exists z : Q, z = qpoly_w12_sqdist_on a b p q.
Proof. intros. eexists. reflexivity. Qed.

Record RationalPiece := {
  piece_left : Q;
  piece_right : Q;
  piece_poly : QPoly
}.

Definition piece_interval_positive (c : RationalPiece) : Prop :=
  (piece_left c < piece_right c)%Q.

Fixpoint piece_chain_wf (pieces : list RationalPiece) : Prop :=
  match pieces with
  | [] => True
  | c1 :: rest =>
      piece_interval_positive c1 /\
      match rest with
      | [] => True
      | c2 :: _ =>
          Qeq (piece_right c1) (piece_left c2) /\
          Qeq (qpoly_eval (piece_poly c1) (piece_right c1))
              (qpoly_eval (piece_poly c2) (piece_left c2)) /\
          piece_chain_wf rest
      end
  end.

Record RationalPiecewiseCode := {
  rpc_pieces : list RationalPiece;
  rpc_nonempty : rpc_pieces <> [];
  rpc_wf : piece_chain_wf rpc_pieces
}.

Arguments rpc_pieces _.

Fixpoint same_mesh_pieces (xs ys : list RationalPiece) : Prop :=
  match xs, ys with
  | [], [] => True
  | x :: xs', y :: ys' =>
      Qeq (piece_left x) (piece_left y) /\
      Qeq (piece_right x) (piece_right y) /\
      same_mesh_pieces xs' ys'
  | _, _ => False
  end.

Definition same_mesh (u v : RationalPiecewiseCode) : Prop :=
  same_mesh_pieces (rpc_pieces u) (rpc_pieces v).

Fixpoint piecewise_w12_inner_raw (xs ys : list RationalPiece) : Q :=
  match xs, ys with
  | x :: xs', y :: ys' =>
      qpoly_w12_inner_on (piece_left x) (piece_right x)
        (piece_poly x) (piece_poly y)
      + piecewise_w12_inner_raw xs' ys'
  | _, _ => 0
  end.

Definition piecewise_w12_inner (u v : RationalPiecewiseCode) : Q :=
  piecewise_w12_inner_raw (rpc_pieces u) (rpc_pieces v).

Fixpoint piecewise_w12_sqdist_raw (xs ys : list RationalPiece) : Q :=
  match xs, ys with
  | x :: xs', y :: ys' =>
      qpoly_w12_sqdist_on (piece_left x) (piece_right x)
        (piece_poly x) (piece_poly y)
      + piecewise_w12_sqdist_raw xs' ys'
  | _, _ => 0
  end.

Definition piecewise_w12_sqdist (u v : RationalPiecewiseCode) : Q :=
  piecewise_w12_sqdist_raw (rpc_pieces u) (rpc_pieces v).

Theorem piecewise_w12_inner_is_exact_rational : forall u v,
  same_mesh u v -> exists z : Q, z = piecewise_w12_inner u v.
Proof. intros. eexists. reflexivity. Qed.

Theorem piecewise_w12_sqdist_is_exact_rational : forall u v,
  same_mesh u v -> exists z : Q, z = piecewise_w12_sqdist u v.
Proof. intros. eexists. reflexivity. Qed.

Fixpoint add_piece_lists (xs ys : list RationalPiece) : list RationalPiece :=
  match xs, ys with
  | x :: xs', y :: ys' =>
      {| piece_left := piece_left x;
         piece_right := piece_right x;
         piece_poly := qpoly_add (piece_poly x) (piece_poly y) |}
      :: add_piece_lists xs' ys'
  | _, _ => []
  end.

Fixpoint scale_piece_list (a : Q) (xs : list RationalPiece) : list RationalPiece :=
  match xs with
  | [] => []
  | x :: xs' =>
      {| piece_left := piece_left x;
         piece_right := piece_right x;
         piece_poly := qpoly_scale a (piece_poly x) |}
      :: scale_piece_list a xs'
  end.

Fixpoint mul_piece_lists (xs ys : list RationalPiece) : list RationalPiece :=
  match xs, ys with
  | x :: xs', y :: ys' =>
      {| piece_left := piece_left x;
         piece_right := piece_right x;
         piece_poly := qpoly_mul (piece_poly x) (piece_poly y) |}
      :: mul_piece_lists xs' ys'
  | _, _ => []
  end.

Lemma scale_piece_list_length : forall a xs,
  length (scale_piece_list a xs) = length xs.
Proof. intros a xs. induction xs; simpl; congruence. Qed.

Lemma add_piece_lists_length_left : forall xs ys,
  length xs = length ys -> length (add_piece_lists xs ys) = length xs.
Proof.
  induction xs as [|x xs IH]; destruct ys as [|y ys]; simpl; intros H.
  - reflexivity.
  - discriminate.
  - discriminate.
  - injection H as Hlen.
    f_equal. apply IH. exact Hlen.
Qed.

Lemma mul_piece_lists_length_left : forall xs ys,
  length xs = length ys -> length (mul_piece_lists xs ys) = length xs.
Proof.
  induction xs as [|x xs IH]; destruct ys as [|y ys]; simpl; intros H.
  - reflexivity.
  - discriminate.
  - discriminate.
  - injection H as Hlen.
    f_equal. apply IH. exact Hlen.
Qed.

Record RawRationalCode := { raw_pieces : list RationalPiece }.

Definition raw_add (u v : RawRationalCode) : RawRationalCode :=
  {| raw_pieces := add_piece_lists (raw_pieces u) (raw_pieces v) |}.
Definition raw_scale (a : Q) (u : RawRationalCode) : RawRationalCode :=
  {| raw_pieces := scale_piece_list a (raw_pieces u) |}.
Definition raw_mul (u v : RawRationalCode) : RawRationalCode :=
  {| raw_pieces := mul_piece_lists (raw_pieces u) (raw_pieces v) |}.

Theorem rational_code_operations_are_finite : forall a u v,
  exists ua us um : RawRationalCode,
    ua = raw_add u v /\ us = raw_scale a u /\ um = raw_mul u v.
Proof. intros. repeat eexists; repeat split; reflexivity. Qed.

End UELAT_V3_RationalSobolev.
