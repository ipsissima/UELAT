Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lra.
Require Import Coq.Arith.Arith.
Import ListNotations.
Open Scope R_scope.

(* Smooth bump function supported in (0,1) *)
Definition bump (x : R) : R :=
  if Rlt_dec x 0 then 0 else
  if Rlt_dec x 1 then exp (-1 / (x * (1 - x))) else 0.

(* Normalized partition of unity over n subintervals *)
Definition partition_of_unity (n : nat) (x : R) : list R :=
  let h := / INR n in
  let shifts := map (fun i => INR i * h) (seq 0 n) in
  let raw := map (fun s => bump ((x - s) / h)) shifts in
  let total := fold_right Rplus 0 raw in
  if Req_EM_T total 0 then repeat 0 n
  else map (fun v => v / total) raw.

Lemma sum_repeat_0 : forall n, fold_right Rplus 0 (repeat 0 n) = 0.
Proof.
  induction n as [|n IH]; simpl.
  - reflexivity.
  - rewrite IH. lra.
Qed.

(** Auxiliary lemma: sum of v/c for v in list equals (sum of v)/c *)
Lemma fold_right_div_distrib : forall (l : list R) (c : R),
  c <> 0 ->
  fold_right Rplus 0 (map (fun v => v / c) l) = fold_right Rplus 0 l / c.
Proof.
  intros l c Hc.
  induction l as [|a l' IH].
  - simpl. field. exact Hc.
  - simpl. rewrite IH. field. exact Hc.
Qed.

(** Partition normalization lemma.
    Either the sum equals 1 (normalized case) or 0 (degenerate case). *)
Lemma partition_sums_to_one : forall n x,
  let φ := partition_of_unity n x in
  (n > 0)%nat ->
  fold_right Rplus 0 φ = 1 \/ fold_right Rplus 0 φ = 0.
Proof.
  intros n x φ Hn.
  unfold φ, partition_of_unity.
  set (h := / INR n).
  set (shifts := map (fun i => INR i * h) (seq 0 n)).
  set (raw := map (fun s => bump ((x - s) / h)) shifts).
  set (total := fold_right Rplus 0 raw).
  destruct (Req_EM_T total 0) as [Htotal_zero | Htotal_nonzero].
  - (* Case: total = 0 *)
    right.
    apply sum_repeat_0.
  - (* Case: total ≠ 0, normalized sum equals 1 *)
    left.
    rewrite fold_right_div_distrib by exact Htotal_nonzero.
    unfold total.
    field. exact Htotal_nonzero.
Qed.
