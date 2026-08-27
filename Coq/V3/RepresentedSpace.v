(** RepresentedSpace.v -- fast Cauchy representation core for v3 Section 2.

    This module supplies the metric/Cauchy part of manuscript Definition 2.1.
*)

From Coq Require Import Reals Lia Lra.
Local Open Scope R_scope.
From UELAT.V3 Require Import CertificateEnrichment.

Module UELAT_V3_RepresentedSpace.
Import UELAT_V3_CertificateEnrichment.

Fixpoint dyadic (n : nat) : R :=
  match n with
  | O => 1
  | S k => dyadic k / 2
  end.

Lemma dyadic_pos : forall n, 0 < dyadic n.
Proof.
  induction n; simpl.
  - lra.
  - nra.
Qed.

Lemma dyadic_nonnegative : forall n, 0 <= dyadic n.
Proof.
  intro n. left. apply dyadic_pos.
Qed.

Record FastCauchyName (X : MetricPresentation) := {
  approximant : nat -> carrier X;
  fast_cauchy : forall (m n : nat),
      (n <= m)%nat ->
      distance (approximant m) (approximant n) <= dyadic n
}.

Arguments approximant {X} _ _.
Arguments fast_cauchy {X} _ _ _ _.

Record RepresentedPoint (X : MetricPresentation) := {
  represented_value : carrier X;
  represented_name : FastCauchyName X;
  represented_tail : forall n : nat,
      distance represented_value (approximant represented_name n) <= dyadic n
}.

Arguments represented_value {X} _.
Arguments represented_name {X} _.
Arguments represented_tail {X} _ _.

Lemma tail_reverse {X : MetricPresentation} (x : RepresentedPoint X) :
  forall n : nat,
    distance (approximant (represented_name x) n) (represented_value x)
      <= dyadic n.
Proof.
  intro n.
  rewrite distance_symmetric.
  apply represented_tail.
Qed.

Lemma approximants_compare_through_limit
    {X : MetricPresentation} (x y : RepresentedPoint X) :
  forall n : nat,
    distance (approximant (represented_name x) n)
             (approximant (represented_name y) n)
    <= dyadic n + distance (represented_value x) (represented_value y) + dyadic n.
Proof.
  intro n.
  eapply Rle_trans.
  - apply distance_triangle with (y := represented_value x).
  - eapply Rle_trans.
    + apply Rplus_le_compat_l.
      apply distance_triangle with (y := represented_value y).
    + pose proof (tail_reverse x n) as Hx.
      pose proof (represented_tail y n) as Hy.
      nra.
Qed.

Lemma represented_points_same_value_zero_distance
    {X : MetricPresentation} (x y : RepresentedPoint X) :
  represented_value x = represented_value y ->
  distance (represented_value x) (represented_value y) = 0.
Proof.
  intro H. subst.
  apply distance_reflexive.
Qed.

End UELAT_V3_RepresentedSpace.
