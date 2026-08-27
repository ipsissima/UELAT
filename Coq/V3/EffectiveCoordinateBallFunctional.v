(** EffectiveCoordinateBallFunctional.v -- close the representation seam from
    effective ambient coordinates plus admissibility to a represented dual
    functional. *)

From Coq Require Import Reals QArith Qreals.
From UELAT.V3 Require Import
  CertificateEnrichment RepresentedSpace ComputableBanach SearchableCore
  EffectiveCoordinateSequence EffectiveCoordinateFunctional2
  EffectiveCoordinateFunctionalExtensional RepresentedDualFunctional2.

Module UELAT_V3_EffectiveCoordinateBallFunctional.
Import UELAT_V3_CertificateEnrichment.
Import UELAT_V3_RepresentedSpace.
Import UELAT_V3_ComputableBanach.
Import UELAT_V3_SearchableCore.
Import UELAT_V3_EffectiveCoordinateSequence.
Import UELAT_V3_EffectiveCoordinateFunctional2.
Import UELAT_V3_EffectiveCoordinateFunctionalExtensional.
Import UELAT_V3_RepresentedDualFunctional2.

Section Bridge.
  Variable S : SearchableCorePresentation.
  Let B := sc_banach S.
  Variable a : EffectiveCoordinateBallPoint B.

  Definition as_effective_coordinate_point : EffectiveCoordinatePoint S :=
    {| ecp_point := effective_ball_coordinate_point B a;
       ecp_approx := effective_ball_approx B a;
       ecp_approx_sound := effective_ball_approx_sound B a |}.

  Definition ball_coordinate_functional_name
      (nu : CoreFastName B) : RationalRealName :=
    represented_functional_name S as_effective_coordinate_point nu.

  Theorem ball_coordinate_functional_name_fast : forall nu m n,
      n <= m ->
      Rabs
        (Q2R (rrn_stage (ball_coordinate_functional_name nu) m)
         - Q2R (rrn_stage (ball_coordinate_functional_name nu) n))
      <= dyadic n.
  Proof. intros nu m n Hnm. apply rrn_fast. exact Hnm. Qed.

  Theorem ball_coordinate_functional_extensional :
    forall (x y : CoreNamedPoint B),
      core_named_value x = core_named_value y ->
      real_names_equivalent
        (ball_coordinate_functional_name (core_named_name x))
        (ball_coordinate_functional_name (core_named_name y)).
  Proof.
    intros x y Hxy n.
    exact (represented_functional_name_extensional
      S as_effective_coordinate_point x y Hxy n).
  Qed.

  Definition effective_ball_represented_functional :
      RepresentedRealFunctional S.
  Proof.
    refine {| rrf_realize := ball_coordinate_functional_name |}.
    intros x y Hxy.
    now apply ball_coordinate_functional_extensional.
  Defined.

  Theorem admissible_effective_coordinate_sequence_yields_functional :
    exists F : RepresentedRealFunctional S,
      forall nu, rrf_realize F nu = ball_coordinate_functional_name nu.
  Proof.
    exists effective_ball_represented_functional.
    intro nu. reflexivity.
  Qed.
End Bridge.

End UELAT_V3_EffectiveCoordinateBallFunctional.
