(** RationalSobolevCheckers.v -- finite-stage slack checker core for v3 Proposition 5.3.

    The rational code module computes exact squared finite-stage distances.
    This module proves the metric soundness pattern used by the manuscript's
    approximation and distance checkers: a strict finite-stage squared-distance
    inequality plus the fast-Cauchy tail implies the requested semantic bound.

    The remaining completeness obligation is effective search for a sufficiently
    late stage once semantic strict slack is known.
*)

From Coq Require Import Reals Lra Arith.
Local Open Scope R_scope.
From UELAT.V3 Require Import CertificateEnrichment RepresentedSpace.

Module UELAT_V3_RationalSobolevCheckers.
Import UELAT_V3_CertificateEnrichment.
Import UELAT_V3_RepresentedSpace.

Section CheckerSoundness.

  Context {X : MetricPresentation}.

  Variables x : carrier X.
  Variable stages : nat -> carrier X.
  Hypothesis stage_tail : forall n,
      distance x (stages n) <= dyadic n.

  Definition ApproxStageWitness
      (p : carrier X) (q : R) (n : nat) : Prop :=
    dyadic n < q /\
    distance (stages n) p ^ 2 < (q - dyadic n) ^ 2.

  Theorem approximation_stage_witness_sound : forall p q n,
    ApproxStageWitness p q n ->
    distance x p < q.
  Proof.
    intros p q n [Hq Hsq].
    pose proof (distance_nonnegative X (stages n) p) as Hd0.
    assert (Hfinite : distance (stages n) p < q - dyadic n) by nra.
    pose proof (stage_tail n) as Htail.
    pose proof (distance_triangle X x (stages n) p) as Htri.
    lra.
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
    DistanceStageWitness q n ->
    distance x y < q.
  Proof.
    intros q n [Hq Hsq].
    pose proof (distance_nonnegative X (xs n) (ys n)) as Hd0.
    assert (Hfinite : distance (xs n) (ys n) < q - 2 * dyadic n) by nra.
    pose proof (x_tail n) as Hxtail.
    pose proof (y_tail n) as Hytail.
    assert (Hytail_rev : distance (ys n) y <= dyadic n).
    { rewrite distance_symmetric. exact Hytail. }
    pose proof (distance_triangle X x (xs n) y) as Htri1.
    pose proof (distance_triangle X (xs n) (ys n) y) as Htri2.
    lra.
  Qed.

  (** Strict-slack completeness reduces to finding a finite stage whose tails
      fit inside the semantic slack.  The effective search procedure will be
      supplied by the computable-Banach/name layer. *)
  Theorem distance_stage_witness_complete_from_stage : forall q,
    (exists n, DistanceStageWitness q n) ->
    exists n, distance x y < q.
  Proof.
    intros q [n Hn].
    exists n. now apply distance_stage_witness_sound.
  Qed.

End DistanceCheckerSoundness.

End UELAT_V3_RationalSobolevCheckers.
