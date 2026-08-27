(** GeometricPrecisionSchedule.v -- derive the descent name schedule from H4. *)

From Coq Require Import Reals Arith PeanoNat Lia Lia Lra Lra.
From UELAT.V3 Require Import CertificateEnrichment RepresentedSpace DescentAssembly.

Module UELAT_V3_GeometricPrecisionSchedule.
Import UELAT_V3_CertificateEnrichment.
Import UELAT_V3_RepresentedSpace.
Import UELAT_V3_DescentAssembly.

Lemma dyadic_succ : forall n, dyadic (S n) = dyadic n / 2.
Proof. reflexivity. Qed.

Lemma dyadic_add : forall a b,
  dyadic (a + b) = dyadic a * dyadic b.
Proof.
  induction a as [|a IHa]; intro b.
  - simpl. ring.
  - simpl. rewrite IHa. ring.
Qed.

Definition geometric_precision_schedule
    (alpha offset s : nat) : nat :=
  S ((s + 1 + offset) / alpha).

Lemma geometric_precision_exponent_dominates : forall alpha offset s,
  0 < alpha ->
  s + 1 + offset <= alpha * geometric_precision_schedule alpha offset s.
Proof.
  intros alpha offset s Halpha.
  unfold geometric_precision_schedule.
  pose proof (Nat.mul_succ_div_gt (s + 1 + offset) alpha) as Hdiv.
  specialize (Hdiv ltac:(lia)).
  lia.
Qed.

Section Schedule.
  Context {X : MetricPresentation}.
  Variable f : carrier X.
  Variable p : nat -> carrier X.
  Variables alpha offset : nat.
  Variable K : R.

  Hypothesis alpha_positive : 0 < alpha.
  Hypothesis K_nonnegative : 0 <= K.
  Hypothesis offset_absorbs_constant : K * dyadic offset <= 1.
  Hypothesis geometric_level_error : forall n,
    distance f (p n) <= K * dyadic (alpha * n).

  Definition mu (s : nat) : nat :=
    geometric_precision_schedule alpha offset s.

  Theorem scheduled_geometric_error : forall s,
    distance f (p (mu s)) <= dyadic s / 2.
  Proof.
    intro s.
    pose proof (geometric_level_error (mu s)) as Herr.
    pose proof (geometric_precision_exponent_dominates alpha offset s
                  alpha_positive) as Hexp.
    pose proof (dyadic_antitone (s + 1 + offset) (alpha * mu s) Hexp) as Hdy.
    rewrite Nat.add_assoc in Hdy.
    rewrite dyadic_add in Hdy.
    rewrite dyadic_succ in Hdy.
    pose proof (dyadic_nonnegative (S s)) as Hds.
    pose proof (dyadic_nonnegative offset) as Hdo.
    assert (HKdy : K * dyadic (S s + offset) <= dyadic (S s)).
    { rewrite dyadic_add. nra. }
    eapply Rle_trans; [exact Herr|].
    eapply Rle_trans.
    - apply Rmult_le_compat_l; [exact K_nonnegative|exact Hdy].
    - rewrite dyadic_succ. exact HKdy.
  Qed.

  Definition represented_point_from_geometric_rate : RepresentedPoint X :=
    descent_represented_point f p mu scheduled_geometric_error.

  Theorem represented_point_from_geometric_rate_value :
    represented_value represented_point_from_geometric_rate = f.
  Proof. reflexivity. Qed.

  Theorem represented_point_from_geometric_rate_stage : forall s,
    approximant (represented_name represented_point_from_geometric_rate) s
      = p (mu s).
  Proof. reflexivity. Qed.
End Schedule.

End UELAT_V3_GeometricPrecisionSchedule.
