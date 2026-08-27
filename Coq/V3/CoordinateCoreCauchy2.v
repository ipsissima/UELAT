(** CoordinateCoreCauchy2.v -- completion step for admissible dual coordinates.

    The dense-core coordinate functional is 1-Lipschitz and maps every fast
    core name to a fast Cauchy real-value sequence; extensionality is explicit.
*)

From Coq Require Import Reals QArith Qreals Lra Ring.
From UELAT.V3 Require Import
  CertificateEnrichment RepresentedSpace ComputableBanach BanachNormLemmas
  SearchableCore CoordinateDualBall SearchableCoordinateCoreFunctional2.

Module UELAT_V3_CoordinateCoreCauchy2.
Import UELAT_V3_CertificateEnrichment.
Import UELAT_V3_RepresentedSpace.
Import UELAT_V3_ComputableBanach.
Import UELAT_V3_BanachNormLemmas.
Import UELAT_V3_SearchableCore.
Import UELAT_V3_CoordinateDualBall.
Import UELAT_V3_SearchableCoordinateCoreFunctional2.

Section Completion.
  Variable S : SearchableCorePresentation.
  Let B := sc_banach S.
  Variable a : CoordinateDualBallPoint B.

  Definition core_neg_code (p : core_code B) : core_code B := core_scale B (-1) p.
  Definition core_sub_code (p q : core_code B) : core_code B := core_add B p (core_neg_code q).

  Lemma core_neg_code_sound : forall p,
    core_decode (core_neg_code p) = cb_neg B (core_decode p).
  Proof.
    intro p. unfold core_neg_code, cb_neg.
    rewrite core_scale_sound, Q2R_opp.
    change (Q2R (1 : Q)) with 1%R. ring_simplify. reflexivity.
  Qed.

  Lemma core_sub_code_sound : forall p q,
    core_decode (core_sub_code p q) = cb_sub B (core_decode p) (core_decode q).
  Proof.
    intros p q. unfold core_sub_code, cb_sub.
    rewrite core_add_sound, core_neg_code_sound. reflexivity.
  Qed.

  Lemma direct_core_value_neg : forall p,
    direct_core_value S a (core_neg_code p) = - direct_core_value S a p.
  Proof.
    intro p. unfold core_neg_code.
    rewrite direct_core_value_scale, Q2R_opp.
    change (Q2R (1 : Q)) with 1%R. ring.
  Qed.

  Lemma direct_core_value_sub : forall p q,
    direct_core_value S a (core_sub_code p q)
      = direct_core_value S a p - direct_core_value S a q.
  Proof.
    intros p q. unfold core_sub_code.
    rewrite direct_core_value_add, direct_core_value_neg. ring.
  Qed.

  Theorem direct_core_value_lipschitz : forall p q,
    Rabs (direct_core_value S a p - direct_core_value S a q)
      <= distance (core_decode p) (core_decode q).
  Proof.
    intros p q. rewrite <- direct_core_value_sub.
    eapply Rle_trans.
    - apply direct_core_value_bounded.
    - rewrite core_sub_code_sound, cb_norm_sub_is_distance. apply Rle_refl.
  Qed.

  Definition coordinate_value_stage (nu : CoreFastName B) (n : nat) : R :=
    direct_core_value S a (core_stage nu n).

  Theorem coordinate_value_stage_fast : forall nu m n,
    n <= m -> Rabs (coordinate_value_stage nu m - coordinate_value_stage nu n) <= dyadic n.
  Proof.
    intros nu m n Hnm. unfold coordinate_value_stage.
    eapply Rle_trans; [apply direct_core_value_lipschitz|apply core_stage_fast; exact Hnm].
  Qed.

  Record RealCauchyValueName := {
    rcv_stage : nat -> R;
    rcv_fast : forall m n, n <= m -> Rabs (rcv_stage m - rcv_stage n) <= dyadic n
  }.

  Definition coordinate_value_name (nu : CoreFastName B) : RealCauchyValueName :=
    {| rcv_stage := coordinate_value_stage nu;
       rcv_fast := coordinate_value_stage_fast nu |}.

  Theorem equal_point_value_stages_close :
    forall (x y : CoreNamedPoint B),
      core_named_value x = core_named_value y -> forall n,
        Rabs
          (coordinate_value_stage (core_named_name x) n
           - coordinate_value_stage (core_named_name y) n) <= 2 * dyadic n.
  Proof.
    intros x y Hxy n. unfold coordinate_value_stage.
    eapply Rle_trans.
    - apply direct_core_value_lipschitz.
    - pose proof (core_named_tail x n) as Hx.
      pose proof (core_named_tail y n) as Hy.
      rewrite Hxy in Hx.
      rewrite (distance_symmetric (core_named_value y)
        (core_decode (core_stage (core_named_name x) n))) in Hx.
      eapply Rle_trans.
      + apply distance_triangle with (y := core_named_value y).
      + lra.
  Qed.

  Theorem value_name_extensional :
    forall (x y : CoreNamedPoint B),
      core_named_value x = core_named_value y -> forall n,
        Rabs
          (rcv_stage (coordinate_value_name (core_named_name x)) n
           - rcv_stage (coordinate_value_name (core_named_name y)) n) <= 2 * dyadic n.
  Proof. intros. simpl. now apply equal_point_value_stages_close. Qed.
End Completion.

End UELAT_V3_CoordinateCoreCauchy2.
