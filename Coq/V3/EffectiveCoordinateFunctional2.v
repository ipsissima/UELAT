(** EffectiveCoordinateFunctional2.v -- effective completion of an admissible
    coordinate point to a rational real-name procedure. *)

From Coq Require Import Reals QArith Qreals Bool Arith Lia Lra Nra Ring Field.
Import ListNotations.
Local Open Scope Q_scope.
From UELAT.V3 Require Import
  CertificateEnrichment RepresentedSpace ComputableBanach
  StrictSlackSearch DyadicVanishing GenericSlackCertification
  SearchableCore NormalizedCoreCoordinates CoordinateDualBall
  SearchableCoordinateCoreFunctional2 CoordinateCoreCauchy2.

Module UELAT_V3_EffectiveCoordinateFunctional2.
Import UELAT_V3_CertificateEnrichment.
Import UELAT_V3_RepresentedSpace.
Import UELAT_V3_ComputableBanach.
Import UELAT_V3_StrictSlackSearch.
Import UELAT_V3_DyadicVanishing.
Import UELAT_V3_GenericSlackCertification.
Import UELAT_V3_SearchableCore.
Import UELAT_V3_NormalizedCoreCoordinates.
Import UELAT_V3_CoordinateDualBall.
Import UELAT_V3_SearchableCoordinateCoreFunctional2.
Import UELAT_V3_CoordinateCoreCauchy2.

Section EffectiveCoordinates.
  Variable S : SearchableCorePresentation.
  Let B := sc_banach S.

  Record EffectiveCoordinatePoint := {
    ecp_point : CoordinateDualBallPoint B;
    ecp_approx : nat -> nat -> Q;
    ecp_approx_sound : forall i n,
      Rabs
        (Q2R (ecp_approx i n) - cdb_coordinates ecp_point i)
      <= dyadic n
  }.

  Variable a : EffectiveCoordinatePoint.

  Definition scale_precision_test
      (p : core_code B) (n k : nat) : bool :=
    qltb (core_scale_factor B p * qdyadic k) (qdyadic n).

  Lemma scale_precision_eventually : forall p n,
    exists k, scale_precision_test p n k = true.
  Proof.
    intros p n.
    pose proof (core_scale_factor_real_positive B p) as Hc.
    pose proof (dyadic_pos n) as Hdn.
    destruct (dyadic_eventually_below
      (dyadic n / Q2R (core_scale_factor B p))
      ltac:(apply Rdiv_lt_0_compat; assumption)) as [k Hk].
    exists k. unfold scale_precision_test.
    apply qltb_true_iff. apply Rlt_Qlt.
    rewrite Q2R_mult, !qdyadic_real.
    apply (Rmult_lt_reg_r (/ Q2R (core_scale_factor B p))).
    - apply Rinv_0_lt_compat. exact Hc.
    - replace
        ((Q2R (core_scale_factor B p) * dyadic k)
         * / Q2R (core_scale_factor B p))
        with (dyadic k) by (field; lra).
      replace
        (dyadic n * / Q2R (core_scale_factor B p))
        with (dyadic n / Q2R (core_scale_factor B p)) by reflexivity.
      exact Hk.
  Qed.

  Definition scale_precision
      (p : core_code B) (n : nat) : nat :=
    first_true_index (scale_precision_test p n)
      (scale_precision_eventually p n).

  Lemma scale_precision_valid : forall p n,
    Q2R (core_scale_factor B p) * dyadic (scale_precision p n) < dyadic n.
  Proof.
    intros p n.
    pose proof (first_true_valid
      (scale_precision_test p n) (scale_precision_eventually p n)) as Htest.
    apply qltb_true_iff in Htest.
    pose proof (Qlt_Rlt _ _ Htest) as Hreal.
    rewrite Q2R_mult, !qdyadic_real in Hreal. exact Hreal.
  Qed.

  Definition core_value_rational_approx
      (p : core_code B) (n : nat) : Q :=
    core_scale_factor B p
      * ecp_approx a (core_index S p) (scale_precision p n).

  Theorem core_value_rational_approx_sound : forall p n,
    Rabs
      (Q2R (core_value_rational_approx p n)
       - direct_core_value S (ecp_point a) p)
      < dyadic n.
  Proof.
    intros p n.
    unfold core_value_rational_approx, direct_core_value.
    rewrite Q2R_mult.
    set (c := Q2R (core_scale_factor B p)).
    set (z := Q2R (ecp_approx a (core_index S p) (scale_precision p n))).
    set (v := cdb_coordinates (ecp_point a) (core_index S p)).
    replace (c*z - c*v) with (c*(z-v)) by ring.
    rewrite Rabs_mult.
    assert (Hc : 0 < c).
    { unfold c. apply core_scale_factor_real_positive. }
    rewrite Rabs_pos_eq by lra.
    pose proof (ecp_approx_sound a (core_index S p) (scale_precision p n)) as Hz.
    fold z v in Hz.
    pose proof (scale_precision_valid p n) as Hscale.
    fold c in Hscale.
    eapply Rle_lt_trans.
    - apply Rmult_le_compat_l; [lra|exact Hz].
    - exact Hscale.
  Qed.

  Definition represented_functional_qstage
      (nu : CoreFastName B) (n : nat) : Q :=
    let s := S (S n) in
    core_value_rational_approx (core_stage nu s) s.

  Lemma three_shifted_dyadics_le : forall n,
    3 * dyadic (S (S n)) <= dyadic n.
  Proof.
    intro n. simpl. pose proof (dyadic_nonnegative n). nra.
  Qed.

  Theorem represented_functional_qstage_fast : forall nu m n,
    n <= m ->
    Rabs
      (Q2R (represented_functional_qstage nu m)
       - Q2R (represented_functional_qstage nu n))
      <= dyadic n.
  Proof.
    intros nu m n Hnm.
    unfold represented_functional_qstage.
    set (sm := S (S m)); set (sn := S (S n)).
    set (pm := core_stage nu sm); set (pn := core_stage nu sn).
    set (Fm := direct_core_value S (ecp_point a) pm).
    set (Fn := direct_core_value S (ecp_point a) pn).
    pose proof (core_value_rational_approx_sound pm sm) as Ham.
    pose proof (core_value_rational_approx_sound pn sn) as Han.
    assert (Han' :
      Rabs (Fn - Q2R (core_value_rational_approx pn sn)) < dyadic sn).
    { replace (Fn - Q2R (core_value_rational_approx pn sn))
        with (-(Q2R (core_value_rational_approx pn sn) - Fn)) by ring.
      rewrite Rabs_Ropp. exact Han. }
    pose proof (direct_core_value_lipschitz S (ecp_point a) pm pn) as Hlip.
    assert (Hstage : distance (core_decode pm) (core_decode pn) <= dyadic sn).
    { unfold pm, pn, sm, sn. apply core_stage_fast. lia. }
    assert (Hcore : Rabs (Fm-Fn) <= dyadic sn).
    { unfold Fm, Fn. eapply Rle_trans; eauto. }
    assert (Hmono : dyadic sm <= dyadic sn).
    { apply dyadic_antitone. unfold sm, sn. lia. }
    assert (Htri :
      Rabs
        (Q2R (core_value_rational_approx pm sm)
         - Q2R (core_value_rational_approx pn sn))
      <= Rabs (Q2R (core_value_rational_approx pm sm)-Fm)
         + Rabs (Fm-Fn)
         + Rabs (Fn-Q2R (core_value_rational_approx pn sn))).
    { replace
        (Q2R (core_value_rational_approx pm sm)
         - Q2R (core_value_rational_approx pn sn))
        with
        ((Q2R (core_value_rational_approx pm sm)-Fm)
         + ((Fm-Fn) + (Fn-Q2R (core_value_rational_approx pn sn)))) by ring.
      eapply Rle_trans; [apply Rabs_triang|].
      apply Rplus_le_compat_l. apply Rabs_triang. }
    eapply Rle_trans; [exact Htri|].
    pose proof (three_shifted_dyadics_le n) as Hthree.
    unfold sn in *. lra.
  Qed.

  Record RationalRealName := {
    rrn_stage : nat -> Q;
    rrn_fast : forall m n,
      n <= m ->
      Rabs (Q2R (rrn_stage m) - Q2R (rrn_stage n)) <= dyadic n
  }.

  Definition represented_functional_name
      (nu : CoreFastName B) : RationalRealName :=
    {| rrn_stage := represented_functional_qstage nu;
       rrn_fast := represented_functional_qstage_fast nu |}.
End EffectiveCoordinates.

End UELAT_V3_EffectiveCoordinateFunctional2.
