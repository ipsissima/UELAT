From Coq.Reals Require Import Reals.
From UELAT.Approx Require Import Certificate Bernstein_Lipschitz.
Local Open Scope R_scope.

Definition fexp (x:R) := exp x.

Lemma fexp_lipschitz_on_I01 :
  forall x y, 0<=x<=1 -> 0<=y<=1 -> Rabs (fexp x - fexp y) <= (exp 1) * Rabs (x - y).
Proof.
intros x y Hx Hy.
(* Mean value theorem on [0,1], exp' = exp ≤ exp 1 *)
set φ := fun t => exp t.
assert (Hdiff: forall t, derivable_pt φ t).
{ intro t; apply derivable_pt_exp. }
eapply (MVT_cor1 φ φ); try (intros; apply derivable_pt_exp).
- intros t Ht; replace (Rmax (exp 0) (exp 1)) with (exp 1) by (simpl; rewrite Rmax_right; try (apply Rlt_le, exp_pos); lra); lra.
- unfold φ, fexp; lra.
Qed.

Example exp_certificate :
  forall eps (Heps : 0 < eps),
  let c := Bernstein.mk_cert fexp (exp 1) eps (Rlt_le _ _ (exp_pos 1)) Heps in
  Certificate.sound_on fexp c.
Proof.
intros eps Heps.
set c := Bernstein.mk_cert fexp (exp 1) eps (Rlt_le _ _ (exp_pos 1)) Heps.
apply (Bernstein.sound_on_lipschitz fexp (exp 1) eps); try lra.
apply fexp_lipschitz_on_I01.
Qed.
