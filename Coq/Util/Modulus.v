From Stdlib Require Import Reals Psatz.
Set Implicit Arguments.
Local Open Scope R_scope.

Module UELAT_Modulus.

Record modulus := {
  mu      : R -> R;
  mu_pos  : forall eps, 0 < eps -> 0 < mu eps;
  mu_mono : forall e1 e2, 0 < e1 -> e1 <= e2 -> mu e1 <= mu e2
}.

(* A simple Lipschitz → modulus witness: mu(eps) = eps/(1+L), L≥0 *)
Lemma lipschitz_modulus :
  forall (L:R), 0 <= L ->
  exists (M:modulus),
    (forall eps, 0 < eps -> mu M eps = eps / (1 + L)).
Proof.
  intros L HL.
  assert (Hden : 0 < 1 + L) by lra.
  pose (f := fun eps : R => eps / (1 + L)).
  assert (Hpos : forall eps, 0 < eps -> 0 < f eps).
  { intros eps Heps. unfold f, Rdiv.
    apply Rmult_lt_0_compat; [exact Heps|].
    apply Rinv_0_lt_compat; exact Hden. }
  assert (Hmono : forall e1 e2, 0 < e1 -> e1 <= e2 -> f e1 <= f e2).
  { intros e1 e2 He1 Hle. unfold f, Rdiv.
    apply Rmult_le_compat_r; [apply Rlt_le; apply Rinv_0_lt_compat; exact Hden|].
    exact Hle. }
  exists {| mu := f; mu_pos := Hpos; mu_mono := Hmono |}.
  intros eps Heps; unfold f; reflexivity.
Qed.

End UELAT_Modulus.
