From Coq.Reals Require Import Reals.
From UELAT.Approx Require Import Certificate.
From UELAT.Approx Require Import Bernstein_Lipschitz.

Module Weierstrass.

Theorem UELAT_C01_Bernstein_Lipschitz :
  forall f L eps, 0 <= L -> 0 < eps ->
   (forall x y, 0<=x<=1 -> 0<=y<=1 -> Rabs (f x - f y) <= L * Rabs (x - y)) ->
   exists c, Certificate.sound_on f c /\ c.(Certificate.bound) <= eps.
Proof.
move=> f L eps HL Heps Hlip.
exists (Bernstein.mk_cert f L eps HL Heps); split.
- apply Bernstein.sound_on_lipschitz; auto.
- simpl; lra.
Qed.

End Weierstrass.
