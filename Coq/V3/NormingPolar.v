(** NormingPolar.v -- elementary polar computation behind manuscript
    Theorem 3.2, Step 3. *)

From Coq Require Import Reals Lra.
Local Open Scope R_scope.

Module UELAT_V3_NormingPolar.
Section Polar.
  Context {Index X : Type}.
  Variable norm : X -> R.
  Variable coord : Index -> X -> R.

  Hypothesis norm_nonnegative : forall x, 0 <= norm x.
  Hypothesis coord_contracting : forall j x,
    Rabs (coord j x) <= norm x.
  Hypothesis one_norming : forall x eps,
    0 < eps -> exists j,
      norm x - eps < Rabs (coord j x).

  Definition norming_polar (x : X) : Prop :=
    forall j, Rabs (coord j x) <= 1.
  Definition closed_unit_ball (x : X) : Prop := norm x <= 1.

  Theorem unit_ball_inside_norming_polar : forall x,
    closed_unit_ball x -> norming_polar x.
  Proof.
    intros x Hunit j. unfold closed_unit_ball in Hunit.
    eapply Rle_trans; [apply coord_contracting|exact Hunit].
  Qed.

  Theorem norming_polar_inside_unit_ball : forall x,
    norming_polar x -> closed_unit_ball x.
  Proof.
    intros x Hpolar. unfold norming_polar in Hpolar. unfold closed_unit_ball.
    destruct (Rle_dec (norm x) 1) as [Hle|Hnle]; [exact Hle|].
    assert (Hgt : 1 < norm x) by lra.
    set (eps := (norm x - 1) / 2).
    assert (Heps : 0 < eps) by (unfold eps; lra).
    destruct (one_norming x eps Heps) as [j Hj].
    specialize (Hpolar j). unfold eps in Hj. lra.
  Qed.

  Theorem norming_polar_eq_closed_unit_ball : forall x,
    norming_polar x <-> closed_unit_ball x.
  Proof.
    intro x. split.
    - apply norming_polar_inside_unit_ball.
    - apply unit_ball_inside_norming_polar.
  Qed.
End Polar.

End UELAT_V3_NormingPolar.
