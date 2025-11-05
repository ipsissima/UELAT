From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.analysis Require Import reals normedtype.
Require Import Coq.Reals.Reals Coq.micromega.Lra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Certificate.

Record cert := {
  deg          : nat;      (* N *)
  coeffs       : seq R;    (* a_0..a_N = f(k/N) *)
  bound        : R;        (* claimed sup-norm error bound *)
  bound_nonneg : 0 <= bound
}.

Definition C (n k:nat) : R := IZR (Z.of_nat (binom n k)).

Definition bernstein (N k:nat) (x:R) : R :=
  C N k * (x ^ k) * ((1 - x) ^ (N - k)).

Definition eval_cert (c:cert) (x:R) : R :=
  \sum_(k < c.(deg).+1) (nth 0%R c.(coeffs) k) * bernstein c.(deg) k x.

Definition sound_on (f:R->R) (c:cert) : Prop :=
  forall x, 0 <= x <= 1 -> Rabs (f x - eval_cert c x) <= c.(bound).

End Certificate.
