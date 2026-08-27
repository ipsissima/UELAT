(** RepresentedDualFunctional2.v -- represented real-valued functional induced by an effective coordinate-ball point.

    Keeps semantic uniqueness separate from the rational Type-2 approximation
    procedure. Core values already satisfy the dense rational span graph; this
    module packages their approximants into a represented operation interface.
*)

From Coq Require Import Reals QArith Qreals Lra.
From UELAT.V3 Require Import
  CertificateEnrichment RepresentedSpace ComputableBanach SearchableCore
  CoordinateDualBall SearchableCoordinateCoreFunctional2
  EffectiveCoordinateFunctional2 EffectiveCoordinateFunctionalExtensional.

Module UELAT_V3_RepresentedDualFunctional2.
Import UELAT_V3_CertificateEnrichment.
Import UELAT_V3_RepresentedSpace.
Import UELAT_V3_ComputableBanach.
Import UELAT_V3_SearchableCore.
Import UELAT_V3_CoordinateDualBall.
Import UELAT_V3_SearchableCoordinateCoreFunctional2.
Import UELAT_V3_EffectiveCoordinateFunctional2.
Import UELAT_V3_EffectiveCoordinateFunctionalExtensional.

Section RepresentedFunctional.
  Variable S : SearchableCorePresentation.
  Let B := sc_banach S.
  Variable a : EffectiveCoordinatePoint S.

  Record RepresentedRealOperation := {
    rro_name_map : CoreFastName B -> RationalRealName;
    rro_extensional : forall (x y : CoreNamedPoint B),
      core_named_value x = core_named_value y -> forall n,
      Rabs
        (Q2R (rrn_stage (rro_name_map (core_named_name x)) n)
         - Q2R (rrn_stage (rro_name_map (core_named_name y)) n))
      <= dyadic n
  }.

  Definition coordinate_represented_operation : RepresentedRealOperation :=
    {| rro_name_map := represented_functional_name S a;
       rro_extensional := represented_functional_stages_extensional_fast S a |}.

  Theorem coordinate_represented_operation_stage : forall nu n,
    rrn_stage (rro_name_map coordinate_represented_operation nu) n
      = represented_functional_qstage S a nu n.
  Proof. reflexivity. Qed.

  Theorem coordinate_represented_operation_fast : forall nu m n,
    n <= m ->
    Rabs
      (Q2R (rrn_stage (rro_name_map coordinate_represented_operation nu) m)
       - Q2R (rrn_stage (rro_name_map coordinate_represented_operation nu) n))
    <= dyadic n.
  Proof.
    intros nu m n Hmn.
    apply rrn_fast. exact Hmn.
  Qed.

  Theorem coordinate_operation_matches_core_functional_approximately :
    forall (p : core_code B) (nu : CoreFastName B) n,
      core_stage nu (S (S n)) = p ->
      Rabs
        (Q2R (rrn_stage (rro_name_map coordinate_represented_operation nu) n)
         - direct_core_value S (ecp_point a) p)
      < dyadic (S (S n)).
  Proof.
    intros p nu n Hstage.
    rewrite coordinate_represented_operation_stage.
    unfold represented_functional_qstage.
    rewrite Hstage.
    apply core_value_rational_approx_sound.
  Qed.
End RepresentedFunctional.

End UELAT_V3_RepresentedDualFunctional2.
