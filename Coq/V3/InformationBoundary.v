(** InformationBoundary.v -- authoritative Proposition 9.1 in abstract norm form.

    A verifier restricted to a noninjective information map cannot soundly
    certify a finite bound on a fibre containing an unbounded affine line.
*)

From Coq Require Import Reals Lra.

Module UELAT_V3_InformationBoundary.

Section Fibre.
  Context {X : Type}.
  Variable norm : X -> R.
  Variable add : X -> X -> X.
  Variable smul : R -> X -> X.
  Variable info : X -> R.
  Variable x0 z : X.
  Hypothesis same_fibre_line : forall a,
      info (add x0 (smul a z)) = info x0.
  Hypothesis line_unbounded : forall B : R,
      exists a : R, B < norm (add x0 (smul a z)).
  Variable Accepted : R -> R -> Prop.
  Hypothesis verifier_sound : forall i B x,
      info x = i -> Accepted i B -> norm x <= B.

  Theorem no_finite_bound_on_unbounded_fibre : forall B,
      ~ Accepted (info x0) B.
  Proof.
    intros B Hacc.
    destruct (line_unbounded B) as [a Ha].
    pose proof (verifier_sound (info x0) B
                  (add x0 (smul a z))
                  (same_fibre_line a) Hacc) as Hbound.
    lra.
  Qed.
End Fibre.

End UELAT_V3_InformationBoundary.
