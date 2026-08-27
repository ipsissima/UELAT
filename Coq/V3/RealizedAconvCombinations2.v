(** RealizedAconvCombinations2.v -- effective finite absolutely convex hull of
    the strong 1-norming family. *)

From Coq Require Import Reals QArith Qreals List Lra Nra Ring.
Import ListNotations.
Local Open Scope Q_scope.
From UELAT.V3 Require Import
  CertificateEnrichment RepresentedSpace ComputableBanach
  RealizedBoundedFunctional ApproximateHahnBanachStrongInterface
  EffectiveNormingFamilyStrong RealizedFunctionalCoordinates2.

Module UELAT_V3_RealizedAconvCombinations2.
Import UELAT_V3_CertificateEnrichment.
Import UELAT_V3_RepresentedSpace.
Import UELAT_V3_ComputableBanach.
Import UELAT_V3_RealizedBoundedFunctional.
Import UELAT_V3_ApproximateHahnBanachStrongInterface.
Import UELAT_V3_EffectiveNormingFamilyStrong.
Import UELAT_V3_RealizedFunctionalCoordinates2.

Definition qabs_weight (q : Q) : R := Rabs (Q2R q).

Section Combinations.
  Variable B : RealComputableBanachPresentation.
  Variable A : EffectiveApproxHahnBanachStrong B.

  Definition CandidateIndex := ((nat * nat) * nat)%type.
  Definition WeightedCandidate := (Q * CandidateIndex)%type.

  Definition candidate (j : CandidateIndex) : RealizedBoundedFunctional B :=
    match j with
    | ((i,n),k) => strong_indexed_candidate B A i n k
    end.

  Fixpoint aconv_weight (ws : list WeightedCandidate) : R :=
    match ws with
    | [] => 0
    | (q,_) :: rest => qabs_weight q + aconv_weight rest
    end.

  Fixpoint aconv_apply
      (ws : list WeightedCandidate) (x : carrier (cb_metric B)) : R :=
    match ws with
    | [] => 0
    | (q,j) :: rest => Q2R q * rbf_apply (candidate j) x + aconv_apply rest x
    end.

  Fixpoint aconv_realize
      (ws : list WeightedCandidate) (nu : CoreFastName B) (n : nat) : Q :=
    match ws with
    | [] => 0
    | (q,j) :: rest => q * rbf_realize (candidate j) nu n + aconv_realize rest nu n
    end.

  Lemma aconv_apply_add : forall ws x y,
    aconv_apply ws (cb_add B x y) = aconv_apply ws x + aconv_apply ws y.
  Proof.
    induction ws as [|w rest IH]; intros x y; simpl.
    - ring.
    - destruct w as [q [[i n] k]]. simpl. rewrite rbf_add, IH. ring.
  Qed.

  Lemma aconv_apply_scale : forall ws c x,
    aconv_apply ws (cb_scale B c x) = c * aconv_apply ws x.
  Proof.
    induction ws as [|w rest IH]; intros c x; simpl.
    - ring.
    - destruct w as [q [[i n] k]]. simpl. rewrite rbf_scale, IH. ring.
  Qed.

  Lemma aconv_apply_abs_bound : forall ws x,
    Rabs (aconv_apply ws x) <= aconv_weight ws * cb_norm B x.
  Proof.
    induction ws as [|w rest IH]; intro x; simpl.
    - rewrite Rabs_R0. nra.
    - destruct w as [q [[i n] k]]. simpl.
      eapply Rle_trans; [apply Rabs_triang|].
      rewrite Rabs_mult.
      pose proof (strong_indexed_candidate_contracting B A i n k x) as Hj.
      pose proof (IH x) as Hr.
      pose proof (cb_norm_nonnegative B x) as Hx.
      unfold qabs_weight. nra.
  Qed.

  Lemma aconv_realize_error : forall ws (x : CoreNamedPoint B) n,
    Rabs
      (Q2R (aconv_realize ws (core_named_name x) n)
       - aconv_apply ws (core_named_value x))
      <= aconv_weight ws * dyadic n.
  Proof.
    induction ws as [|w rest IH]; intros x n; simpl.
    - rewrite Rabs_R0. nra.
    - destruct w as [q [[i s] k]]. simpl.
      rewrite Q2R_plus, Q2R_mult.
      replace
        (Q2R q
           * Q2R (rbf_realize (strong_indexed_candidate B A i s k)
                    (core_named_name x) n)
         + Q2R (aconv_realize rest (core_named_name x) n)
         - (Q2R q
              * rbf_apply (strong_indexed_candidate B A i s k)
                  (core_named_value x)
            + aconv_apply rest (core_named_value x)))
        with
        (Q2R q
           * (Q2R (rbf_realize (strong_indexed_candidate B A i s k)
                       (core_named_name x) n)
              - rbf_apply (strong_indexed_candidate B A i s k)
                  (core_named_value x))
         + (Q2R (aconv_realize rest (core_named_name x) n)
            - aconv_apply rest (core_named_value x))) by ring.
      eapply Rle_trans; [apply Rabs_triang|].
      rewrite Rabs_mult.
      pose proof (rbf_realize_correct
        (strong_indexed_candidate B A i s k) x n) as Hj.
      pose proof (IH x n) as Hr.
      unfold qabs_weight. nra.
  Qed.

  Variable ws : list WeightedCandidate.
  Hypothesis Hweights : aconv_weight ws <= 1.

  Definition realized_aconv_functional : RealizedBoundedFunctional B.
  Proof.
    refine {| rbf_apply := aconv_apply ws;
              rbf_norm_bound := 1;
              rbf_realize := aconv_realize ws |}.
    - apply aconv_apply_add.
    - apply aconv_apply_scale.
    - lra.
    - intro x.
      pose proof (aconv_apply_abs_bound ws x) as Hbound.
      pose proof (cb_norm_nonnegative B x) as Hx. nra.
    - intros x n.
      pose proof (aconv_realize_error ws x n) as Herr.
      pose proof (dyadic_nonnegative n) as Hd. nra.
  Defined.

  Theorem realized_aconv_contracting : forall x,
    Rabs (rbf_apply realized_aconv_functional x) <= cb_norm B x.
  Proof.
    intro x. pose proof (rbf_bounded realized_aconv_functional x) as H.
    simpl in H. nra.
  Qed.

  Definition realized_aconv_effective_dual_point :=
    realized_effective_ball_point B realized_aconv_functional
      realized_aconv_contracting.

  Theorem finite_aconv_is_effective_dual_ball_point :
    exists a, a = realized_aconv_effective_dual_point.
  Proof. eexists. reflexivity. Qed.
End Combinations.

End UELAT_V3_RealizedAconvCombinations2.
