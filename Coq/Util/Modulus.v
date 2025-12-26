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
  refine (ex_intro _ {| mu := fun eps => eps / (1 + L) |} _).
  split.
  - intros eps Heps.
    assert (Hden: 0 < 1 + L) by lra.
    unfold Rdiv.
    apply Rmult_lt_0_compat; [exact Heps|].
    apply Rinv_0_lt_compat; exact Hden.
  split.
  - intros e1 e2 He1 Hle.
    assert (Hden: 0 < 1 + L) by lra.
    unfold Rdiv.
    apply Rmult_le_compat_r; [apply Rlt_le; apply Rinv_0_lt_compat; exact Hden|].
    exact Hle.
  - intros eps Heps; reflexivity.
Qed.

End UELAT_Modulus.
