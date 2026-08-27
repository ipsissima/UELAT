(** NormalizedCoreCoordinates.v -- normalized rational-core coordinates for
    Steps 2--3 of authoritative Theorem 3.2. *)

From Coq Require Import Reals QArith Qreals List Lra Nra Field.
Import ListNotations.
Local Open Scope Q_scope.
From UELAT.V3 Require Import
  CertificateEnrichment RepresentedSpace ComputableBanach BanachNormLemmas.

Module UELAT_V3_NormalizedCoreCoordinates.
Import UELAT_V3_CertificateEnrichment.
Import UELAT_V3_RepresentedSpace.
Import UELAT_V3_ComputableBanach.
Import UELAT_V3_BanachNormLemmas.

Section Coordinates.
  Variable B : RealComputableBanachPresentation.

  Definition core_scale_factor (p : core_code B) : Q :=
    let q := core_norm_approx B p 0 in q * q + 4.

  Lemma core_scale_factor_real_positive : forall p,
    0 < Q2R (core_scale_factor p).
  Proof.
    intro p. unfold core_scale_factor. rewrite Q2R_plus, Q2R_mult.
    change (Q2R (4 : Q)) with 4%R. nra.
  Qed.

  Lemma core_scale_factor_nonzero_Q : forall p,
    ~ core_scale_factor p == 0.
  Proof.
    intros p Hq. apply Qeq_eqR in Hq.
    change (Q2R (0 : Q)) with 0%R in Hq.
    pose proof (core_scale_factor_real_positive p). lra.
  Qed.

  Lemma core_norm_below_scale_factor : forall p,
    cb_norm B (core_decode p) < Q2R (core_scale_factor p).
  Proof.
    intro p. set (q := core_norm_approx B p 0).
    pose proof (core_norm_approx_sound B p 0) as Happ.
    simpl dyadic in Happ.
    change (Rabs (Q2R q - cb_norm B (core_decode p)) <= 1) in Happ.
    assert (Hupper : cb_norm B (core_decode p) <= Q2R q + 1).
    { pose proof (Rle_abs (-(Q2R q - cb_norm B (core_decode p)))) as Habs.
      rewrite Rabs_Ropp in Habs. lra. }
    unfold core_scale_factor. fold q. rewrite Q2R_plus, Q2R_mult.
    change (Q2R (4 : Q)) with 4%R. nra.
  Qed.

  Definition normalized_core_code (p : core_code B) : core_code B :=
    core_scale (/ core_scale_factor p) p.

  Definition normalized_core (i : nat) : carrier (cb_metric B) :=
    core_decode (normalized_core_code (core_enum B i)).

  Theorem normalized_core_norm_lt_one : forall p,
    cb_norm B (core_decode (normalized_core_code p)) < 1.
  Proof.
    intro p. unfold normalized_core_code.
    rewrite core_scale_sound, cb_norm_scale.
    rewrite Q2R_inv by apply core_scale_factor_nonzero_Q.
    pose proof (core_scale_factor_real_positive p) as Hc.
    rewrite Rabs_pos_eq by (left; apply Rinv_0_lt_compat; exact Hc).
    apply (Rmult_lt_reg_r (Q2R (core_scale_factor p))); [exact Hc|].
    replace
      ((/ Q2R (core_scale_factor p) * cb_norm B (core_decode p))
       * Q2R (core_scale_factor p))
      with (cb_norm B (core_decode p)) by (field; lra).
    ring_simplify. apply core_norm_below_scale_factor.
  Qed.

  Corollary normalized_enumerated_core_norm_lt_one : forall i,
    cb_norm B (normalized_core i) < 1.
  Proof. intro i. unfold normalized_core. apply normalized_core_norm_lt_one. Qed.

  Theorem normalized_core_rationally_spans_original_core : forall p,
    exists i c : Q,
      core_decode p = cb_scale B (Q2R c) (normalized_core i).
  Proof.
    intro p. destruct (core_enum_surjective B p) as [i Hi].
    exists i, (core_scale_factor p).
    unfold normalized_core, normalized_core_code. rewrite Hi.
    rewrite core_scale_sound, cb_scale_assoc.
    rewrite Q2R_inv by apply core_scale_factor_nonzero_Q.
    pose proof (core_scale_factor_real_positive p) as Hc.
    replace
      (Q2R (core_scale_factor p) * / Q2R (core_scale_factor p))
      with 1 by (field; lra).
    rewrite cb_scale_one. reflexivity.
  Qed.

  Definition CoordinatePoint := nat -> R.
  Definition RationalCoordinateTerm := (Q * nat)%type.

  Fixpoint coordinate_sum (a : CoordinatePoint)
      (terms : list RationalCoordinateTerm) : R :=
    match terms with
    | [] => 0
    | (q,i) :: rest => Q2R q * a i + coordinate_sum a rest
    end.

  Fixpoint combination_code (terms : list RationalCoordinateTerm) : core_code B :=
    match terms with
    | [] => core_zero B
    | (q,i) :: rest =>
        core_add B
          (core_scale B q (normalized_core_code (core_enum B i)))
          (combination_code rest)
    end.

  Definition CoordinateAdmissible (a : CoordinatePoint) : Prop :=
    forall terms,
      Rabs (coordinate_sum a terms)
        <= cb_norm B (core_decode (combination_code terms)).
End Coordinates.

End UELAT_V3_NormalizedCoreCoordinates.
