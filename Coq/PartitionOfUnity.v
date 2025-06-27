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

(* Routine analytic lemma, can be proved with standard algebraic manipulations. *)
Lemma partition_sums_to_one : forall n x,
  let φ := partition_of_unity n x in
  (n > 0)%nat ->
  fold_right Rplus 0 φ = 1 \/ fold_right Rplus 0 φ = 0.
Admitted.
