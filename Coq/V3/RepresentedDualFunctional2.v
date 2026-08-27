(** RepresentedDualFunctional2.v -- package an effective coordinate point as a
    represented real functional. *)

From Coq Require Import Reals QArith Qreals.
From UELAT.V3 Require Import
  CertificateEnrichment RepresentedSpace ComputableBanach SearchableCore
  EffectiveCoordinateFunctional2 EffectiveCoordinateFunctionalExtensional.

Module UELAT_V3_RepresentedDualFunctional2.
Import UELAT_V3_CertificateEnrichment.
Import UELAT_V3_RepresentedSpace.
Import UELAT_V3_ComputableBanach.
Import UELAT_V3_SearchableCore.
Import UELAT_V3_EffectiveCoordinateFunctional2.
Import UELAT_V3_EffectiveCoordinateFunctionalExtensional.

Definition real_names_equivalent
    (u v : RationalRealName) : Prop :=
  forall n,
    Rabs (Q2R (rrn_stage u n) - Q2R (rrn_stage v n)) <= dyadic n.

Section RepresentedFunctional.
  Variable S : SearchableCorePresentation.
  Let B := sc_banach S.

  Record RepresentedRealFunctional := {
    rrf_realize : CoreFastName B -> RationalRealName;
    rrf_extensional : forall (x y : CoreNamedPoint B),
      core_named_value x = core_named_value y ->
      real_names_equivalent
        (rrf_realize (core_named_name x))
        (rrf_realize (core_named_name y))
  }.

  Variable a : EffectiveCoordinatePoint S.

  Definition coordinate_represented_functional : RepresentedRealFunctional.
  Proof.
    refine {| rrf_realize := represented_functional_name S a |}.
    intros x y Hxy n.
    exact (represented_functional_name_extensional S a x y Hxy n).
  Defined.

  Theorem coordinate_functional_realizer_is_extensional :
    forall (x y : CoreNamedPoint B),
      core_named_value x = core_named_value y ->
      real_names_equivalent
        (rrf_realize coordinate_represented_functional (core_named_name x))
        (rrf_realize coordinate_represented_functional (core_named_name y)).
  Proof. intros. now apply rrf_extensional. Qed.
End RepresentedFunctional.

End UELAT_V3_RepresentedDualFunctional2.
