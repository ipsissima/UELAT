Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Coq.QArith.QArith.
Import ListNotations.
Open Scope R_scope.

(* Abstract basis functions indexed by ℕ *)
Parameter basis : nat -> (R -> R).

(* Local approximation certificate over a subinterval *)
Record LocalCertificate := {
  indices : list nat;
  coeffs  : list Q;
  coeffs_length : length coeffs = length indices
}.

(* Full certificate covering domain [0,1] by subintervals *)
Record GlobalCertificate := {
  subintervals : list (R * R); (* open intervals (a,b) *)
  locals       : list LocalCertificate;
  local_match  : length subintervals = length locals
}.

(* Placeholder for Sobolev norm and reconstruction *)
Parameter Wk2_norm : (R -> R) -> R.
Parameter reconstruct : GlobalCertificate -> (R -> R).
Parameter f_target : R -> R.

(* Formal certificate bound assertion *)
Axiom norm_bound : forall (C : GlobalCertificate) (ε : R),
  Wk2_norm (fun x => f_target x - reconstruct C x) < ε -> True.
