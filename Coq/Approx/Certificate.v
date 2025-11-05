From Coq Require Import Reals List Arith Binomial Psatz.
Import ListNotations.
Local Open Scope R_scope.

Module UELAT_Certificate.

(* Finite certificate for approximating f : [0,1]→R by a Bernstein polynomial *)
Record cert := {
  deg    : nat;     (* N *)
  coeffs : list R;  (* a_0,...,a_N = f(k/N) typically *)
  bound  : R;       (* claimed sup-norm error bound ≥ 0 *)
  bound_pos : 0 <= bound;
  coeffs_len : length coeffs = S deg
}.

(* Standard Bernstein basis on [0,1] using nat binomial *)
Definition bernstein (N k:nat) (x:R) : R :=
  IZR (binomial N k) * (x ^ k) * ((1 - x) ^ (N - k)).

Fixpoint nth_default (d:R) (l:list R) (k:nat) : R :=
  match l, k with
  | [], _ => d
  | a::_, 0 => a
  | _::t, S k' => nth_default d t k'
  end.

Definition eval_cert (c:cert) (x:R) : R :=
  let N := c.(deg) in
  let a := c.(coeffs) in
  let fix sum k :=
      match k with
      | O => nth_default 0 a 0 * bernstein N 0 x
      | S k' => sum k' + nth_default 0 a (S k') * bernstein N (S k') x
      end
  in sum N.

End UELAT_Certificate.
