(** RationalSobolevPresentation.v -- manuscript Definition 5.1.

    RationalSobolev.v fixes the concrete finite code language.  This file
    connects that language to a represented W^{1,2} carrier and states the
    finite witness grammar exactly in the form used by the manuscript:
    fast-Cauchy code names, exact finite-stage squared distances, an exact
    self-witness for canonical constant names, and positive approximation /
    two-name distance witnesses with the prescribed Cauchy-tail slack.

    The semantic W^{1,2} carrier is a parameter because the repository does not
    re-found Sobolev analysis from first principles.  Proposition 5.3 is the
    separate theorem asserting soundness/completeness of these checkers.
*)

From Coq Require Import Reals QArith Qreals.
Local Open Scope R_scope.
From UELAT.V3 Require Import CertificateEnrichment RepresentedSpace RationalSobolev.

Module UELAT_V3_RationalSobolevPresentation.
Import UELAT_V3_CertificateEnrichment.
Import UELAT_V3_RepresentedSpace.
Import UELAT_V3_RationalSobolev.

Record RationalW12Presentation := {
  w12_metric : MetricPresentation;
  w12_decode : RationalPiecewiseCode -> carrier w12_metric;
  w12_sqdist : RationalPiecewiseCode -> RationalPiecewiseCode -> Q;
  w12_sqdist_sound : forall p q,
      Q2R (w12_sqdist p q) = distance (w12_decode p) (w12_decode q) ^ 2;
  w12_name : Type;
  w12_name_value : w12_name -> carrier w12_metric;
  w12_stage : w12_name -> nat -> RationalPiecewiseCode;
  w12_stage_tail : forall nu n,
      distance (w12_name_value nu) (w12_decode (w12_stage nu n)) <= dyadic n;
  w12_stage_fast : forall nu m n,
      (n <= m)%nat ->
      distance (w12_decode (w12_stage nu m))
               (w12_decode (w12_stage nu n)) <= dyadic n;
  w12_constant_name : RationalPiecewiseCode -> w12_name;
  w12_constant_value : forall p,
      w12_name_value (w12_constant_name p) = w12_decode p;
  w12_constant_stage : forall p n,
      w12_stage (w12_constant_name p) n = p
}.

Arguments w12_decode {P} _.
Arguments w12_sqdist {P} _ _.
Arguments w12_name_value {P} _.
Arguments w12_stage {P} _ _.
Arguments w12_constant_name {P} _.

Inductive ApproxWitness (P : RationalW12Presentation) : Type :=
| ExactSelf : RationalPiecewiseCode -> ApproxWitness P
| PositiveApprox : nat -> Q -> ApproxWitness P.

Inductive DistanceWitness (P : RationalW12Presentation) : Type :=
| PositiveDistance : nat -> Q -> DistanceWitness P.

Arguments ExactSelf {P} _.
Arguments PositiveApprox {P} _ _.
Arguments PositiveDistance {P} _ _.

Definition approx_accept
    (P : RationalW12Presentation)
    (nu : w12_name P) (p : RationalPiecewiseCode)
    (q : R) (w : ApproxWitness P) : Prop :=
  match w with
  | ExactSelf p0 =>
      p0 = p /\ nu = w12_constant_name p /\ q = 0
  | PositiveApprox n sigma =>
      dyadic n < q /\
      sigma = w12_sqdist (w12_stage nu n) p /\
      Q2R sigma < (q - dyadic n)^2
  end.

Definition distance_accept
    (P : RationalW12Presentation)
    (nu mu : w12_name P) (q : R)
    (w : DistanceWitness P) : Prop :=
  match w with
  | PositiveDistance n sigma =>
      2 * dyadic n < q /\
      sigma = w12_sqdist (w12_stage nu n) (w12_stage mu n) /\
      Q2R sigma < (q - 2 * dyadic n)^2
  end.

Theorem canonical_self_witness_is_exact : forall P p,
  approx_accept P (w12_constant_name p) p 0 (ExactSelf p).
Proof.
  intros P p. simpl. repeat split; reflexivity.
Qed.

Definition name_as_fast_cauchy
    (P : RationalW12Presentation) (nu : w12_name P) :
    FastCauchyName (w12_metric P).
Proof.
  refine {| approximant := fun n => w12_decode (w12_stage nu n) |}.
  intros m n Hmn. apply w12_stage_fast. exact Hmn.
Defined.

Definition name_as_represented_point
    (P : RationalW12Presentation) (nu : w12_name P) :
    RepresentedPoint (w12_metric P).
Proof.
  refine {| represented_value := w12_name_value nu;
            represented_name := name_as_fast_cauchy P nu;
            represented_tail := _ |}.
  intro n. apply w12_stage_tail.
Defined.

End UELAT_V3_RationalSobolevPresentation.
