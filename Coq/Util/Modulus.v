From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.analysis Require Import boolp reals topology normedtype.
Require Import Coq.Reals.Reals Coq.micromega.Lra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Modulus.

Record modulus := {
  mu      : R -> R;                        (* ε ↦ δ(ε) *)
  mu_pos  : forall e, 0 < e -> 0 < mu e;
  mu_mono : forall e1 e2, 0 < e1 <= e2 -> mu e1 <= mu e2
}.

Program Definition lipschitz (L:R) (HL:0 <= L) : modulus :=
  {| mu := fun e => e / (1 + L) |}.
Next Obligation. intros e He; apply Rdiv_lt_0_compat; [assumption|]; lra. Qed.
Next Obligation.
  move=> e1 e2 [He1 Hle]; unfold mu.
  apply Rmult_le_reg_r with (r := (1+L)); try lra.
  field_simplify; try lra. exact Hle.
Qed.

End Modulus.
