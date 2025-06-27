Require Import Coq.Reals.Reals.
Require Import Coq.QArith.QArith.
Require Import Coq.Lists.List.
Require Import Coq.QArith.Qreals.
Open Scope R_scope.

(* Dummy basis and types; replace with real imports in your repo *)
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

Definition inject_Q := Q2R.

Fixpoint map2 {A B C} (f : A -> B -> C) (l1 : list A) (l2 : list B) : list C :=
  match l1, l2 with
  | a::l1', b::l2' => f a b :: map2 f l1' l2'
  | _, _ => @nil C
  end.

Definition eval_local (lc : LocalCertificate) (x : R) : R :=
  fold_right Rplus 0
    (map2 (fun idx aQ => (inject_Q aQ) * (basis idx x))
          lc.(indices) lc.(coeffs)).

Definition reconstruct_global (gc : GlobalCertificate) (x : R) : R :=
  let n := length gc.(subintervals) in
  let φ := repeat 1 n in
  fold_right Rplus 0
    (map2 (fun weight lc => weight * eval_local lc x) φ gc.(locals)).

(* Target function and norm (user must provide in practice) *)
Parameter f_target : R -> R.
Parameter Wk2_norm : (R -> R) -> R.

(* Main error bound axiom, as in the appendices *)
Axiom certificate_error_bound :
  forall (C : GlobalCertificate) (eps : R),
    Wk2_norm (fun x => f_target x - reconstruct_global C x) < eps -> True.
