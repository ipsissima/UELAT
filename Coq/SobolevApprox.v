Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Coq.QArith.QArith.
Import ListNotations.
Open Scope R_scope.

(* Re-declaring necessary certificate structure for standalone compile *)

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

Definition epsilon : R := 0.001.

Parameter quadrature : (R -> R) -> R -> R -> R.

Definition inner_product (f : R -> R) (j : nat) (a b : R) : Q := 0%Q.

Definition build_local_certificate (f : R -> R) (a b : R) (J : list nat) : LocalCertificate :=
  let coeffs := map (fun j => inner_product f j a b) J in
  {| indices := J;
     coeffs := coeffs;
     coeffs_length := map_length (fun j => inner_product f j a b) J |}.

Fixpoint uniform_partition (a b : R) (n : nat) : list (R * R) :=
  match n with
  | O => []
  | S n' =>
    let h := (b - a) / INR n in
    let sub := (a, a + h) in
    sub :: uniform_partition (a + h) b n'
  end.

Definition example_index_set : list nat := [0;1;2;3;4;5;6;7;8;9]%nat.

Definition build_global_certificate (f : R -> R) (n : nat) : GlobalCertificate :=
  let intervals := uniform_partition 0 1 n in
  let locals := map (fun '(a,b) => build_local_certificate f a b example_index_set) intervals in
  {| subintervals := intervals;
     locals := locals;
     local_match := eq_sym (map_length (fun '(a,b) => build_local_certificate f a b example_index_set) intervals) |}.
