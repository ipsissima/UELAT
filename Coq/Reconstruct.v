Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qreals.
Import ListNotations.
Open Scope R_scope.

Definition inject_Q := Q2R.

Parameter basis : nat -> (R -> R).

Record LocalCertificate := {
  indices : list nat;
  coeffs  : list Q;
  coeffs_length : length coeffs = length indices
}.

Record GlobalCertificate := {
  subintervals : list (R * R);
  locals       : list LocalCertificate;
  local_match  : length subintervals = length locals
}.

Definition partition_of_unity (n : nat) (x : R) : list R := repeat 1 n.

Fixpoint map2 {A B C} (f : A -> B -> C) (l1 : list A) (l2 : list B) : list C :=
  match l1, l2 with
  | a::l1', b::l2' => f a b :: map2 f l1' l2'
  | _, _ => []
  end.

Definition eval_local (lc : LocalCertificate) (x : R) : R :=
  fold_right Rplus 0
    (map2 (fun idx aQ => (inject_Q aQ) * (basis idx x))
          lc.(indices) lc.(coeffs)).

Definition reconstruct_global (gc : GlobalCertificate) (x : R) : R :=
  let n := length gc.(subintervals) in
  let φ := partition_of_unity n x in
  fold_right Rplus 0
    (map2 (fun weight lc => weight * eval_local lc x) φ gc.(locals)).
