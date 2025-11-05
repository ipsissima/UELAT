From Coq Require Import Reals.
From UELAT.Util   Require Import Modulus.
From UELAT.Approx Require Import Certificate Bernstein.
Local Open Scope R_scope.

Module UELAT_Spec.

(* A constructive modulus-based continuity interface on [0,1] *)
Record cont01_with_modulus := {
  f     : R -> R;
  M     : UELAT_Modulus.modulus;
  mod_ok : forall eps, eps>0 -> forall x y,
            0 <= x <= 1 -> 0 <= y <= 1 ->
            Rabs (x - y) <= UELAT_Modulus.mu M eps ->
            Rabs (f x - f y) <= eps
}.

(* What the eventual theorem will produce: a certificate achieving ≤ eps *)
Record bernstein_goal (cm:cont01_with_modulus) := {
  eps    : R;
  eps_pos : eps > 0;
  cert   : UELAT_Certificate.cert;
  sound  : forall x, 0 <= x <= 1 ->
            Rabs (cm.(f) x - UELAT_Certificate.eval_cert cert x) <= cert.(UELAT_Certificate.bound);
  within : cert.(UELAT_Certificate.bound) <= eps
}.

(* Problem statement packaged without asserting existence (no axioms): *)
Definition Problem (cm:cont01_with_modulus) : Type := bernstein_goal cm.

(* We will later *construct* a function that takes (cm, ε>0) and returns a goal.
   For now we only state the TYPE we intend to inhabit; no admits, no axioms. *)
Definition TargetType (cm:cont01_with_modulus) : Type := { bg : bernstein_goal cm | True }.

End UELAT_Spec.
