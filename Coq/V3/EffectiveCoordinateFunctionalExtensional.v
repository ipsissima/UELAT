(** EffectiveCoordinateFunctionalExtensional.v -- source-name extensionality for the effective coordinate functional.

    If two CoreNamedPoints have the same represented value, the rational
    functional approximants produced from their names are uniformly close. This
    is the Type-2 extensionality check needed before calling the coordinate
    functional a represented operation on the Banach space rather than on raw
    name syntax.
*)

From Coq Require Import Reals Lra Ring.
From UELAT.V3 Require Import
  CertificateEnrichment RepresentedSpace ComputableBanach
  SearchableCore CoordinateDualBall CoordinateCoreCauchy2
  EffectiveCoordinateFunctional2.

Module UELAT_V3_EffectiveCoordinateFunctionalExtensional.
Import UELAT_V3_CertificateEnrichment.
Import UELAT_V3_RepresentedSpace.
Import UELAT_V3_ComputableBanach.
Import UELAT_V3_SearchableCore.
Import UELAT_V3_CoordinateDualBall.
Import UELAT_V3_CoordinateCoreCauchy2.
Import UELAT_V3_EffectiveCoordinateFunctional2.

Section Extensionality.
  Variable S : SearchableCorePresentation.
  Let B := sc_banach S.
  Variable a : EffectiveCoordinatePoint S.

  Theorem represented_functional_stages_close_on_equal_points :
    forall (x y : CoreNamedPoint B),
      core_named_value x = core_named_value y ->
      forall n,
      Rabs
        (Q2R (represented_functional_qstage S a (core_named_name x) n)
         - Q2R (represented_functional_qstage S a (core_named_name y) n))
      <= 4 * dyadic (S (S n)).
  Proof.
    intros x y Hxy n.
    unfold represented_functional_qstage.
    set (s := S (S n)).
    set (px := core_stage (core_named_name x) s).
    set (py := core_stage (core_named_name y) s).
    set (Fx := direct_core_value S (ecp_point a) px).
    set (Fy := direct_core_value S (ecp_point a) py).
    pose proof (core_value_rational_approx_sound S a px s) as Hax.
    pose proof (core_value_rational_approx_sound S a py s) as Hay.
    assert (Hay' :
      Rabs (Fy - Q2R (core_value_rational_approx S a py s)) < dyadic s).
    { replace (Fy - Q2R (core_value_rational_approx S a py s))
        with (-(Q2R (core_value_rational_approx S a py s)-Fy)) by ring.
      rewrite Rabs_Ropp. exact Hay. }
    pose proof (direct_core_value_lipschitz S (ecp_point a) px py) as Hlip.
    pose proof (core_named_tail x s) as Hx.
    pose proof (core_named_tail y s) as Hy.
    rewrite Hxy in Hx.
    rewrite (distance_symmetric (core_named_value y) (core_decode px)) in Hx.
    assert (Hdist : distance (core_decode px) (core_decode py) <= 2*dyadic s).
    { eapply Rle_trans.
      - apply distance_triangle with (y := core_named_value y).
      - unfold px, py in *. lra. }
    assert (Hcore : Rabs (Fx-Fy) <= 2*dyadic s).
    { unfold Fx, Fy. eapply Rle_trans; [exact Hlip|exact Hdist]. }
    assert (Htri :
      Rabs
        (Q2R (core_value_rational_approx S a px s)
         - Q2R (core_value_rational_approx S a py s))
      <= Rabs (Q2R (core_value_rational_approx S a px s)-Fx)
        + Rabs (Fx-Fy)
        + Rabs (Fy-Q2R (core_value_rational_approx S a py s))).
    { replace
        (Q2R (core_value_rational_approx S a px s)
         - Q2R (core_value_rational_approx S a py s))
        with ((Q2R (core_value_rational_approx S a px s)-Fx)
          + ((Fx-Fy)+(Fy-Q2R (core_value_rational_approx S a py s)))) by ring.
      eapply Rle_trans; [apply Rabs_triang|].
      apply Rplus_le_compat_l. apply Rabs_triang. }
    unfold s in *. lra.
  Qed.

  Corollary represented_functional_stages_extensional_fast :
    forall (x y : CoreNamedPoint B),
      core_named_value x = core_named_value y ->
      forall n,
      Rabs
        (Q2R (rrn_stage (represented_functional_name S a (core_named_name x)) n)
         - Q2R (rrn_stage (represented_functional_name S a (core_named_name y)) n))
      <= dyadic n.
  Proof.
    intros x y Hxy n. simpl.
    pose proof (represented_functional_stages_close_on_equal_points x y Hxy n) as H.
    simpl dyadic in H. nra.
  Qed.
End Extensionality.

End UELAT_V3_EffectiveCoordinateFunctionalExtensional.
