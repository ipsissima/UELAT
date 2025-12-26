(** Summation.v — Finite summation lemmas

    This module provides lemmas about finite sums that are used
    in the approximation and error bound proofs.

    Reference: UELAT Paper, various sections
*)

From Coq Require Import Reals List Arith Lra Lia.
Import ListNotations.
Local Open Scope R_scope.

Module UELAT_Summation.

(** * Basic Summation *)

(** Sum of a function over [0, n) *)
Fixpoint sum_n (f : nat -> R) (n : nat) : R :=
  match n with
  | O => 0
  | S n' => sum_n f n' + f n'
  end.

Lemma sum_n_O : forall f, sum_n f 0 = 0.
Proof. reflexivity. Qed.

Lemma sum_n_S : forall f n, sum_n f (S n) = sum_n f n + f n.
Proof. reflexivity. Qed.

(** Summation is linear *)
Lemma sum_n_plus : forall f g n,
  sum_n (fun k => f k + g k) n = sum_n f n + sum_n g n.
Proof.
  intros f g n.
  induction n as [|n IH].
  - simpl. ring.
  - simpl. rewrite IH. ring.
Qed.

Lemma sum_n_mult_l : forall c f n,
  sum_n (fun k => c * f k) n = c * sum_n f n.
Proof.
  intros c f n.
  induction n as [|n IH].
  - simpl. ring.
  - simpl. rewrite IH. ring.
Qed.

Lemma sum_n_mult_r : forall f c n,
  sum_n (fun k => f k * c) n = sum_n f n * c.
Proof.
  intros f c n.
  induction n as [|n IH].
  - simpl. ring.
  - simpl. rewrite IH. ring.
Qed.

(** Summation over constant *)
Lemma sum_n_const : forall c n,
  sum_n (fun _ => c) n = INR n * c.
Proof.
  intros c n.
  induction n as [|n IH].
  - simpl. ring.
  - rewrite sum_n_S. rewrite IH.
    rewrite S_INR. ring.
Qed.

(** Summation split *)
Lemma sum_n_split : forall f m n,
  (m <= n)%nat ->
  sum_n f n = sum_n f m + sum_n (fun k => f (m + k)%nat) (n - m).
Proof.
  intros f m n Hmn.
  induction n as [|n IH].
  - assert (m = 0)%nat by lia. subst. simpl. ring.
  - destruct (Nat.eq_dec m (S n)) as [Heq | Hneq].
    + subst. replace (S n - S n)%nat with 0%nat by lia. simpl. ring.
    + assert (Hle : (m <= n)%nat) by lia.
      specialize (IH Hle).
      rewrite sum_n_S. rewrite IH.
      replace (S n - m)%nat with (S (n - m))%nat by lia.
      rewrite sum_n_S.
      replace (m + (n - m))%nat with n by lia.
      ring.
Qed.

(** * Absolute Value of Sums *)

Lemma sum_n_abs_le : forall f n,
  Rabs (sum_n f n) <= sum_n (fun k => Rabs (f k)) n.
Proof.
  intros f n.
  induction n as [|n IH].
  - simpl. rewrite Rabs_R0. lra.
  - simpl.
    eapply Rle_trans.
    + apply Rabs_triang.
    + apply Rplus_le_compat; [exact IH | lra].
Qed.

(** * Bounds on Sums *)

Lemma sum_n_le : forall f g n,
  (forall k, (k < n)%nat -> f k <= g k) ->
  sum_n f n <= sum_n g n.
Proof.
  intros f g n Hfg.
  induction n as [|n IH].
  - simpl. lra.
  - simpl.
    apply Rplus_le_compat.
    + apply IH. intros k Hk. apply Hfg. lia.
    + apply Hfg. lia.
Qed.

Lemma sum_n_nonneg : forall f n,
  (forall k, (k < n)%nat -> f k >= 0) ->
  sum_n f n >= 0.
Proof.
  intros f n Hf.
  induction n as [|n IH].
  - simpl. lra.
  - simpl.
    assert (H1 : sum_n f n >= 0).
    { apply IH. intros k Hk. apply Hf. lia. }
    assert (H2 : f n >= 0) by (apply Hf; lia).
    lra.
Qed.

(** * Telescoping Sums *)

Lemma sum_n_telescope : forall f n,
  sum_n (fun k => f (S k) - f k) n = f n - f 0%nat.
Proof.
  intros f n.
  induction n as [|n IH].
  - simpl. ring.
  - simpl. rewrite IH. ring.
Qed.

(** * Geometric Series *)

(* Geometric series lemmas — standard calculus results.
   These are well-known identities that can be found in any analysis textbook.
   
   NOTE: The proofs require careful handling of real number arithmetic with
   the ring/field tactics. The mathematical content is standard.
*)

Lemma pow_pos : forall r n, r > 0 -> r ^ n > 0.
Proof.
  intros r n Hr. induction n; simpl.
  - lra.
  - apply Rmult_gt_0_compat; assumption.
Qed.

(* Geometric series formula - standard calculus result *)
Lemma sum_n_geometric : forall r n,
  r <> 1 ->
  sum_n (fun k => r ^ k) n = (1 - r ^ n) / (1 - r).
Proof.
  intros r n Hr.
  induction n as [|n IH].
  - simpl. unfold Rdiv. 
    replace (1 - 1) with 0 by ring.
    rewrite Rmult_0_l. ring.
  - rewrite sum_n_S. rewrite IH.
    (* Standard algebraic manipulation *)
    assert (Hne: 1 - r <> 0) by lra.
    assert (Heq: (1 - r ^ n) / (1 - r) + r ^ n = (1 - r ^ S n) / (1 - r)).
    {
      unfold Rdiv.
      replace (1 - r ^ S n) with (1 - r ^ n - r ^ n * r + r ^ n) by (simpl; ring).
      replace (1 - r ^ n - r ^ n * r + r ^ n) with ((1 - r ^ n) + r ^ n * (1 - r)) by ring.
      rewrite Rmult_plus_distr_r.
      f_equal.
      rewrite Rmult_assoc. rewrite Rinv_r by lra. ring.
    }
    exact Heq.
Qed.

Lemma sum_n_geometric_bound : forall r n,
  0 < r -> r < 1 ->
  sum_n (fun k => r ^ k) n < 1 / (1 - r).
Proof.
  intros r n Hr0 Hr1.
  rewrite sum_n_geometric by lra.
  unfold Rdiv.
  apply Rmult_lt_compat_r.
  - apply Rinv_0_lt_compat. lra.
  - assert (H : r ^ n > 0) by (apply pow_pos; lra).
    lra.
Qed.

(** * List-based Summation *)

Definition sum_list (l : list R) : R :=
  fold_right Rplus 0 l.

Lemma sum_list_app : forall l1 l2,
  sum_list (l1 ++ l2) = sum_list l1 + sum_list l2.
Proof.
  intros l1 l2.
  induction l1 as [|a l1' IH].
  - simpl. ring.
  - simpl. rewrite IH. ring.
Qed.

Lemma sum_list_map : forall {A : Type} (f : A -> R) (l : list A),
  sum_list (map f l) = fold_right (fun a acc => f a + acc) 0 l.
Proof.
  intros A f l.
  induction l as [|a l' IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma sum_list_le : forall l1 l2,
  length l1 = length l2 ->
  Forall2 Rle l1 l2 ->
  sum_list l1 <= sum_list l2.
Proof.
  intros l1 l2 Hlen H.
  induction H.
  - simpl. lra.
  - simpl in Hlen. injection Hlen as Hlen'.
    simpl. apply Rplus_le_compat.
    + exact H.
    + apply IHForall2. exact Hlen'.
Qed.

Lemma sum_list_nonneg : forall l,
  Forall (fun x => x >= 0) l ->
  sum_list l >= 0.
Proof.
  intros l Hl.
  induction l as [|a l' IH].
  - simpl. lra.
  - simpl. inversion Hl; subst.
    specialize (IH H2). lra.
Qed.

(** * Double Summation *)

Definition sum_n_n (f : nat -> nat -> R) (m n : nat) : R :=
  sum_n (fun i => sum_n (fun j => f i j) n) m.

(* Sum swapping lemma - Fubini-style result for finite sums.
   This is a standard result about swapping finite sums. *)
Lemma sum_n_n_swap : forall f m n,
  sum_n_n f m n = sum_n (fun j => sum_n (fun i => f i j) m) n.
Proof.
  intros f m n.
  unfold sum_n_n.
  revert n.
  induction m as [|m IH]; intro n.
  - (* Base case: m = 0 *)
    simpl.
    induction n as [|n IHn].
    + simpl. reflexivity.
    + simpl. rewrite <- IHn. ring.
  - (* Inductive case: m = S m *)
    simpl.
    specialize (IH n). rewrite IH.
    clear IH.
    induction n as [|n IHn].
    + simpl. ring.
    + simpl. rewrite <- IHn. ring.
Qed.

End UELAT_Summation.
