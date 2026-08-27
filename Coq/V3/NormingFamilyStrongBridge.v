(** NormingFamilyStrongBridge.v -- effective Step 1 bridge for authoritative Theorem 3.2.

    Every coordinate functional is Type-2 realized, contracting and part of a
    1-norming family. Thus the evaluation map is isometric in the supremum
    characterization and has a uniform rational realizer coordinatewise.
*)

From Coq Require Import Reals.
From UELAT.V3 Require Import
  CertificateEnrichment ComputableBanach
  RealizedBoundedFunctional ApproximateHahnBanachStrongInterface
  EffectiveNormingCandidatesStrong LinearUniversality.

Module UELAT_V3_NormingFamilyStrongBridge.
Import UELAT_V3_CertificateEnrichment.
Import UELAT_V3_ComputableBanach.
Import UELAT_V3_RealizedBoundedFunctional.
Import UELAT_V3_ApproximateHahnBanachStrongInterface.
Import UELAT_V3_EffectiveNormingCandidatesStrong.
Import UELAT_V3_LinearUniversality.

Section Bridge.
  Variable B : RealComputableBanachPresentation.
  Let X := carrier (cb_metric B).
  Variable A : EffectiveApproxHahnBanachStrong B.
  Definition CandidateIndex := (nat * nat * nat)%type.

  Definition strong_candidate (j : CandidateIndex) : RealizedBoundedFunctional B :=
    match j with ((i,n),k) => strong_indexed_candidate B A i n k end.
  Definition strong_coord (j : CandidateIndex) (x : X) : R :=
    rbf_apply (strong_candidate j) x.

  Theorem strong_coord_add : forall j x y,
    strong_coord j (cb_add B x y) = strong_coord j x + strong_coord j y.
  Proof. intros. unfold strong_coord. apply rbf_add. Qed.

  Theorem strong_coord_scale : forall j a x,
    strong_coord j (cb_scale B a x) = a * strong_coord j x.
  Proof. intros. unfold strong_coord. apply rbf_scale. Qed.

  Theorem strong_coord_contracting : forall j x,
    Rabs (strong_coord j x) <= cb_norm B x.
  Proof.
    intros [[i n] k] x. unfold strong_coord, strong_candidate. simpl.
    apply strong_indexed_candidate_contracting.
  Qed.

  Theorem strong_coord_one_norming : forall x eps,
    0 < eps -> exists j : CandidateIndex,
      cb_norm B x - eps < Rabs (strong_coord j x).
  Proof.
    intros x eps Heps.
    destruct (strong_candidates_are_one_norming B A x eps Heps)
      as [i [n [k H]]].
    exists ((i,n),k). exact H.
  Qed.

  Definition strong_evaluation (x : X) : CandidateIndex -> R := fun j => strong_coord j x.

  Theorem strong_evaluation_isometric_sup_characterization : forall x,
    (forall j, Rabs (strong_evaluation x j) <= cb_norm B x)
    /\ (forall eps, 0 < eps ->
      exists j, cb_norm B x - eps < Rabs (strong_evaluation x j)).
  Proof.
    intro x. split.
    - intro j. unfold strong_evaluation. apply strong_coord_contracting.
    - intros eps Heps. unfold strong_evaluation. now apply strong_coord_one_norming.
  Qed.

  Definition strong_coord_realizer
      (j : CandidateIndex) : CoreFastName B -> nat -> Q :=
    rbf_realize (strong_candidate j).

  Theorem strong_coord_realizer_correct : forall j x n,
    Rabs
      (Q2R (strong_coord_realizer j (core_named_name x) n)
       - strong_coord j (core_named_value x)) <= dyadic n.
  Proof. intros. unfold strong_coord_realizer, strong_coord. apply rbf_realize_correct. Qed.

  Record StrongEffectiveNormingFamily := {
    senf_functional : CandidateIndex -> RealizedBoundedFunctional B;
    senf_contracting : forall j x,
      Rabs (rbf_apply (senf_functional j) x) <= cb_norm B x;
    senf_one_norming : forall x eps,
      0 < eps -> exists j,
        cb_norm B x - eps < Rabs (rbf_apply (senf_functional j) x)
  }.

  Definition constructed_strong_norming_family : StrongEffectiveNormingFamily :=
    {| senf_functional := strong_candidate;
       senf_contracting := strong_coord_contracting;
       senf_one_norming := strong_coord_one_norming |}.
End Bridge.

End UELAT_V3_NormingFamilyStrongBridge.
