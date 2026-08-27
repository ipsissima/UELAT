(** EffectiveCoordinateFunctionalExtensional.v -- Type-2 extensionality of
    the coordinate-to-functional construction. *)

From Coq Require Import Reals Lia Lra Ring.
From UELAT.V3 Require Import
  CertificateEnrichment RepresentedSpace ComputableBanach
  SearchableCore CoordinateDualBall SearchableCoordinateCoreFunctional2
  EffectiveCoordinateFunctional2.

Module UELAT_V3_EffectiveCoordinateFunctionalExtensional.
Import UELAT_V3_CertificateEnrichment.
Import UELAT_V3_RepresentedSpace.
Import UELAT_V3_ComputableBanach.
Import UELAT_V3_SearchableCore.
Import UELAT_V3_CoordinateDualBall.
Import UELAT_V3_SearchableCoordinateCoreFunctional2.
Import UELAT_V3_EffectiveCoordinateFunctional2.

Section Extensionality.
  Variable S : SearchableCorePresentation.
  Let B := sc_banach S.
  Variable a : EffectiveCoordinatePoint S.

  Lemma four_shifted_dyadics_eq : forall n,
    4 * dyadic (S (S n)) = dyadic n.
  Proof. intro n. simpl. ring. Qed.

  Theorem equal_source_points_give_close_output_stages :
    forall (x y : CoreNamedPoint B),
      core_named_value x = core_named_value y ->
      forall n,
        Rabs
          (Q2R (represented_functional_qstage S a (core_named_name x) n)
           - Q2R (represented_functional_qstage S a (core_named_name y) n))
        <= dyadic n.
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
        with (-(Q2R (core_value_rational_approx S a py s) - Fy)) by ring.
      rewrite Rabs_Ropp. exact Hay. }
    pose proof
      (direct_core_value_lipschitz S (ecp_point a) px py) as Hlip.
    assert (Hdist : distance (core_decode px) (core_decode py) <= 2 * dyadic s).
    { pose proof (core_named_tail x s) as Hx.
      pose proof (core_named_tail y s) as Hy.
      rewrite Hxy in Hx.
      rewrite (distance_symmetric
        (core_named_value y) (core_decode px)) in Hx.
      unfold px, py.
      eapply Rle_trans.
      - apply distance_triangle with (y := core_named_value y).
      - lra. }
    assert (HF : Rabs (Fx-Fy) <= 2 * dyadic s).
    { unfold Fx, Fy. eapply Rle_trans; eauto. }
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
        with
        ((Q2R (core_value_rational_approx S a px s)-Fx)
         + ((Fx-Fy)
            + (Fy-Q2R (core_value_rational_approx S a py s)))) by ring.
      eapply Rle_trans; [apply Rabs_triang|].
      apply Rplus_le_compat_l. apply Rabs_triang. }
    eapply Rle_trans; [exact Htri|].
    pose proof (four_shifted_dyadics_eq n) as H4.
    unfold s in *. lra.
  Qed.

  Theorem represented_functional_name_extensional :
    forall (x y : CoreNamedPoint B),
      core_named_value x = core_named_value y ->
      forall n,
        Rabs
          (Q2R (rrn_stage S a
            (represented_functional_name S a (core_named_name x)) n)
           - Q2R (rrn_stage S a
            (represented_functional_name S a (core_named_name y)) n))
        <= dyadic n.
  Proof.
    intros. simpl. now apply equal_source_points_give_close_output_stages.
  Qed.
End Extensionality.

End UELAT_V3_EffectiveCoordinateFunctionalExtensional.
