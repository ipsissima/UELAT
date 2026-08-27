(** RationalSobolevCheckers.v -- finite-stage slack checker core for authoritative Proposition 5.3.

    A strict finite-stage squared-distance inequality plus the fast-Cauchy tail
    implies the requested semantic approximation/distance bound.
*)

From Coq Require Import Reals Lra Nra Arith.
From UELAT.V3 Require Import CertificateEnrichment RepresentedSpace.

Module UELAT_V3_RationalSobolevCheckers.
Import UELAT_V3_CertificateEnrichment.
Import UELAT_V3_RepresentedSpace.

Section CheckerSoundness.
  Context {X : MetricPresentation}.
  Variables x : carrier X.
  Variable stages : nat -> carrier X.
  Hypothesis stage_tail : forall n, distance x (stages n) <= dyadic n.

  Definition ApproxStageWitness (p : carrier X) (q : R) (n : nat) : Prop :=
    dyadic n < q /\ distance (stages n) p ^ 2 < (q - dyadic n) ^ 2.

  Theorem approximation_stage_witness_sound : forall p q n,
    ApproxStageWitness p q n -> distance x p < q.
  Proof.
    intros p q n [Hq Hsq].
    pose proof (distance_nonnegative X (stages n) p) as Hd0.
    assert (Hfinite : distance (stages n) p < q - dyadic n) by nra.
    eapply Rle_lt_trans.
    - apply distance_triangle with (y := stages n).
    - specialize (stage_tail n). lra.
  Qed.
End CheckerSoundness.

Section DistanceCheckerSoundness.
  Context {X : MetricPresentation}.
  Variables x y : carrier X.
  Variables xs ys : nat -> carrier X.
  Hypothesis x_tail : forall n, distance x (xs n) <= dyadic n.
  Hypothesis y_tail : forall n, distance y (ys n) <= dyadic n.

  Definition DistanceStageWitness (q : R) (n : nat) : Prop :=
    2 * dyadic n < q /\
    distance (xs n) (ys n) ^ 2 < (q - 2 * dyadic n) ^ 2.

  Theorem distance_stage_witness_sound : forall q n,
    DistanceStageWitness q n -> distance x y < q.
  Proof.
    intros q n [Hq Hsq].
    pose proof (distance_nonnegative X (xs n) (ys n)) as Hd0.
    assert (Hfinite : distance (xs n) (ys n) < q - 2 * dyadic n) by nra.
    eapply Rle_lt_trans.
    - apply distance_triangle with (y := xs n).
    - eapply Rlt_le_trans.
      + specialize (x_tail n). lra.
      + eapply Rle_trans.
        * apply Rplus_le_compat_l. apply distance_triangle with (y := ys n).
        * specialize (y_tail n). lra.
  Qed.

  Theorem distance_stage_witness_complete_from_stage : forall q,
    (exists n, DistanceStageWitness q n) -> exists n, distance x y < q.
  Proof. intros q [n Hn]. exists n. now apply distance_stage_witness_sound. Qed.
End DistanceCheckerSoundness.

End UELAT_V3_RationalSobolevCheckers.
