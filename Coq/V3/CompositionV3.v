(** * CompositionV3.v — manuscript-exact Proposition 5.3

    Identity and composition for the five-clause Definition 5.1
    interface.  The approximation transformer is composed exactly as
    printed: Xi_T at beta, then Xi_S at eta/2, then one target-language
    weakening to the announced composite bound. *)

From Stdlib Require Import List Reals QArith Qreals Qcanon Lra Field Ring.
From UELAT.V3 Require Import EvidenceSyntax Presentation Evidence
  EvidenceClosureV3 RealizableMapV3 GenericLiftV3.
Import ListNotations.
Local Open Scope Qc_scope.

Module V3_CompositionV3.

Import V3_EvidenceSyntax.
Import V3_Presentation.
Import V3_Evidence.
Import V3_EvidenceClosureV3.
Import V3_RealizableMapV3.
Import V3_GenericLiftV3.

Lemma cv3_pos_nonzero : forall q : Qc, (0 < q)%Qc -> q <> 0.
Proof.
  intros q Hq. apply not_eq_sym. apply Qclt_not_eq. exact Hq.
Qed.

Lemma cv3_zero_lt_one : (0 < 1)%Qc.
Proof.
  unfold Qclt. simpl. repeat rewrite Qred_correct. auto with qarith.
Qed.

Lemma cv3_mult_le_mono_l :
  forall L a b : Qc, (0 <= L)%Qc -> (a <= b)%Qc -> (L * a <= L * b)%Qc.
Proof.
  intros L a b HL Hab.
  rewrite (Qcmult_comm L a), (Qcmult_comm L b).
  apply Qcmult_le_compat_r; assumption.
Qed.

Section Identity.
Variable P : Presentation.
Variable EC : EvidenceClosureV3 P.

Definition identity_realizable_v3 : RealizableMapV3 P P.
Proof.
  refine {|
    rv3_T := fun x => x;
    rv3_Lambda := 1;
    rv3_Lambda_nonneg := _;
    rv3_lipschitz := _;
    rv3_lip_derivation := [];
    rv3_name := fun nu => nu;
    rv3_name_ok := _;
    rv3_code := fun p _eta => p;
    rv3_code_witness := fun p eta => ecv3_canonical_witness EC p eta;
    rv3_code_ok := _;
    rv3_xi := fun nu p r eta V =>
      ec_app_weaken_witness (ecv3_base EC) nu p r (1 * r + eta) V;
    rv3_xi_ok := _;
    rv3_theta := fun _a _b W => W;
    rv3_theta_bound := _;
    rv3_theta_id := _;
    rv3_theta_comp := _
  |}.
  - apply Qclt_le_weak. exact cv3_zero_lt_one.
  - intros x y. rewrite Qc2R_1. lra.
  - intro nu. reflexivity.
  - intros p eta Heta.
    apply ecv3_canonical_ok. apply Qclt_le_weak. exact Heta.
  - intros nu p r eta V Hr Heta Happ. simpl.
    eapply ec_app_weaken_ok.
    + rewrite Qcmult_1_l.
      rewrite <- (Qcplus_0_r r).
      apply Qcplus_le_compat; [apply Qcle_refl |].
      apply Qclt_le_weak. exact Heta.
    + exact Happ.
  - intros a b W. simpl. rewrite Qcmult_1_l. apply Qcle_refl.
  - intro a. reflexivity.
  - intros a b c W1 W2. reflexivity.
Defined.

Theorem identity_realizable_v3_map :
  forall x : F P, rv3_T identity_realizable_v3 x = x.
Proof. reflexivity. Qed.

End Identity.

Section Composite.
Variables P G H : Presentation.
Variable T : RealizableMapV3 P G.
Variable S : RealizableMapV3 G H.
Variable ECH : EvidenceClosureV3 H.

Definition cv3_two : Qc := 1 + 1.

Lemma cv3_two_pos : (0 < cv3_two)%Qc.
Proof.
  unfold cv3_two, Qclt, Qcplus. simpl.
  repeat rewrite Qred_correct. auto with qarith.
Qed.

Lemma cv3_two_nonzero : cv3_two <> 0.
Proof. apply cv3_pos_nonzero. exact cv3_two_pos. Qed.

Definition cv3_scale : Qc :=
  match Qclt_le_dec (rv3_Lambda S) 1 with
  | left _ => 1
  | right _ => rv3_Lambda S
  end.

Lemma cv3_scale_ge_one : (1 <= cv3_scale)%Qc.
Proof.
  unfold cv3_scale. destruct (Qclt_le_dec (rv3_Lambda S) 1) as [H|H].
  - apply Qcle_refl.
  - exact H.
Qed.

Lemma cv3_lambdaS_le_scale : (rv3_Lambda S <= cv3_scale)%Qc.
Proof.
  unfold cv3_scale. destruct (Qclt_le_dec (rv3_Lambda S) 1) as [H|H].
  - apply Qclt_le_weak. exact H.
  - apply Qcle_refl.
Qed.

Lemma cv3_scale_pos : (0 < cv3_scale)%Qc.
Proof. eapply Qclt_le_trans; [exact cv3_zero_lt_one | apply cv3_scale_ge_one]. Qed.

Lemma cv3_scale_nonzero : cv3_scale <> 0.
Proof. apply cv3_pos_nonzero. exact cv3_scale_pos. Qed.

Definition cv3_beta_den : Qc := cv3_two * cv3_scale.
Definition cv3_beta (eta : Qc) : Qc := eta / cv3_beta_den.
Definition cv3_half (eta : Qc) : Qc := eta / cv3_two.

Lemma cv3_beta_den_pos : (0 < cv3_beta_den)%Qc.
Proof.
  unfold cv3_beta_den.
  rewrite <- Qcmult_0_l with (n := cv3_scale).
  apply Qcmult_lt_compat_r; [apply cv3_scale_pos | apply cv3_two_pos].
Qed.

Lemma cv3_div_pos : forall a d : Qc, (0 < a)%Qc -> (0 < d)%Qc -> (0 < a / d)%Qc.
Proof.
  intros a d Ha Hd.
  apply Qcnot_le_lt. intro Hbad.
  assert (Hd0 : (0 <= d)%Qc) by (apply Qclt_le_weak; exact Hd).
  pose proof (Qcmult_le_compat_r (a / d) 0 d Hbad Hd0) as Hmul.
  assert (Hcancel : (a / d) * d = a).
  { field. apply cv3_pos_nonzero. exact Hd. }
  rewrite Hcancel, Qcmult_0_l in Hmul.
  exact (Qclt_not_le 0 a Ha Hmul).
Qed.

Lemma cv3_beta_pos : forall eta, (0 < eta)%Qc -> (0 < cv3_beta eta)%Qc.
Proof. intros eta Heta. unfold cv3_beta. apply cv3_div_pos; [exact Heta | apply cv3_beta_den_pos]. Qed.

Lemma cv3_half_pos : forall eta, (0 < eta)%Qc -> (0 < cv3_half eta)%Qc.
Proof. intros eta Heta. unfold cv3_half. apply cv3_div_pos; [exact Heta | apply cv3_two_pos]. Qed.

Lemma cv3_scale_beta_eq_half : forall eta,
  cv3_scale * cv3_beta eta = cv3_half eta.
Proof.
  intro eta. unfold cv3_beta, cv3_beta_den, cv3_half.
  field. split; [apply cv3_two_nonzero | apply cv3_scale_nonzero].
Qed.

Lemma cv3_two_half_eq : forall eta,
  cv3_half eta + cv3_half eta = eta.
Proof.
  intro eta. unfold cv3_half.
  pose proof (Qcmult_div_r eta cv3_two cv3_two_nonzero) as Hhalf.
  unfold cv3_two in Hhalf.
  rewrite Qcmult_plus_distr_l, !Qcmult_1_l in Hhalf.
  exact Hhalf.
Qed.

Lemma cv3_scaled_beta_le_half : forall eta,
  (0 < eta)%Qc ->
  (rv3_Lambda S * cv3_beta eta <= cv3_half eta)%Qc.
Proof.
  intros eta Heta.
  assert (Hb0 : (0 <= cv3_beta eta)%Qc) by
    (apply Qclt_le_weak; apply cv3_beta_pos; exact Heta).
  eapply Qcle_trans.
  - apply Qcmult_le_compat_r; [apply cv3_lambdaS_le_scale | exact Hb0].
  - rewrite cv3_scale_beta_eq_half. apply Qcle_refl.
Qed.

Lemma cv3_defect_le_eta : forall eta,
  (0 < eta)%Qc ->
  (rv3_Lambda S * cv3_beta eta + cv3_half eta <= eta)%Qc.
Proof.
  intros eta Heta.
  eapply Qcle_trans.
  - apply Qcplus_le_compat.
    + apply cv3_scaled_beta_le_half. exact Heta.
    + apply Qcle_refl.
  - rewrite cv3_two_half_eq. apply Qcle_refl.
Qed.

Lemma cv3_intermediate_nonneg : forall u eta,
  (0 <= u)%Qc -> (0 < eta)%Qc ->
  (0 <= rv3_Lambda T * u + cv3_beta eta)%Qc.
Proof.
  intros u eta Hu Heta.
  rewrite <- (Qcplus_0_l 0). apply Qcplus_le_compat.
  - rewrite <- (Qcmult_0_r (rv3_Lambda T)).
    apply cv3_mult_le_mono_l; [apply rv3_Lambda_nonneg | exact Hu].
  - apply Qclt_le_weak. apply cv3_beta_pos. exact Heta.
Qed.

Lemma cv3_composite_bound_le : forall u eta,
  (0 <= u)%Qc -> (0 < eta)%Qc ->
  (rv3_Lambda S * (rv3_Lambda T * u + cv3_beta eta) + cv3_half eta
   <= (rv3_Lambda S * rv3_Lambda T) * u + eta)%Qc.
Proof.
  intros u eta Hu Heta.
  rewrite Qcmult_plus_distr_r.
  rewrite <- Qcmult_assoc.
  rewrite Qcplus_assoc.
  apply Qcplus_le_compat.
  - apply Qcle_refl.
  - apply cv3_defect_le_eta. exact Heta.
Qed.

Lemma cv3_Qc2R_mult : forall p q : Qc,
  Qc2R (p * q) = (Qc2R p * Qc2R q)%R.
Proof.
  intros p q. unfold Qc2R. rewrite <- Q2R_mult.
  apply Qeq_eqR. apply Qred_correct.
Qed.

Definition cv3_code (p : CodeF P) (eta : Qc) : CodeF H :=
  rv3_code S (rv3_code T p (cv3_beta eta)) (cv3_half eta).

Definition cv3_code_raw_witness (p : CodeF P) (eta : Qc) : list bool :=
  rv3_xi S
    (rv3_name T (iotaF P p))
    (rv3_code T p (cv3_beta eta))
    (cv3_beta eta) (cv3_half eta)
    (rv3_code_witness T p (cv3_beta eta)).

Definition cv3_code_witness (p : CodeF P) (eta : Qc) : list bool :=
  ec_app_weaken_witness (ecv3_base ECH)
    (rv3_name S (rv3_name T (iotaF P p)))
    (cv3_code p eta)
    (rv3_Lambda S * cv3_beta eta + cv3_half eta)
    eta
    (cv3_code_raw_witness p eta).

Lemma cv3_code_raw_ok : forall p eta,
  (0 < eta)%Qc ->
  AppCheck H
    (rv3_name S (rv3_name T (iotaF P p)))
    (cv3_code p eta)
    (rv3_Lambda S * cv3_beta eta + cv3_half eta)
    (cv3_code_raw_witness p eta) = true.
Proof.
  intros p eta Heta. unfold cv3_code_raw_witness, cv3_code.
  eapply rv3_xi_ok.
  - apply Qclt_le_weak. apply cv3_beta_pos. exact Heta.
  - apply cv3_half_pos. exact Heta.
  - apply rv3_code_ok. apply cv3_beta_pos. exact Heta.
Qed.

Lemma cv3_code_ok : forall p eta,
  (0 < eta)%Qc ->
  AppCheck H
    (rv3_name S (rv3_name T (iotaF P p)))
    (cv3_code p eta) eta (cv3_code_witness p eta) = true.
Proof.
  intros p eta Heta. unfold cv3_code_witness.
  eapply ec_app_weaken_ok.
  - apply cv3_defect_le_eta. exact Heta.
  - apply cv3_code_raw_ok. exact Heta.
Qed.

Definition cv3_xi_raw_witness
    (nu : NameF P) (p : CodeF P) (u eta : Qc) (V : list bool) : list bool :=
  rv3_xi S
    (rv3_name T nu)
    (rv3_code T p (cv3_beta eta))
    (rv3_Lambda T * u + cv3_beta eta)
    (cv3_half eta)
    (rv3_xi T nu p u (cv3_beta eta) V).

Definition cv3_xi_witness
    (nu : NameF P) (p : CodeF P) (u eta : Qc) (V : list bool) : list bool :=
  ec_app_weaken_witness (ecv3_base ECH)
    (rv3_name S (rv3_name T nu))
    (cv3_code p eta)
    (rv3_Lambda S * (rv3_Lambda T * u + cv3_beta eta) + cv3_half eta)
    ((rv3_Lambda S * rv3_Lambda T) * u + eta)
    (cv3_xi_raw_witness nu p u eta V).

Lemma cv3_xi_raw_ok : forall nu p u eta V,
  (0 <= u)%Qc -> (0 < eta)%Qc ->
  AppCheck P nu p u V = true ->
  AppCheck H
    (rv3_name S (rv3_name T nu))
    (cv3_code p eta)
    (rv3_Lambda S * (rv3_Lambda T * u + cv3_beta eta) + cv3_half eta)
    (cv3_xi_raw_witness nu p u eta V) = true.
Proof.
  intros nu p u eta V Hu Heta Happ.
  unfold cv3_xi_raw_witness, cv3_code.
  eapply rv3_xi_ok.
  - apply cv3_intermediate_nonneg; assumption.
  - apply cv3_half_pos. exact Heta.
  - eapply rv3_xi_ok.
    + exact Hu.
    + apply cv3_beta_pos. exact Heta.
    + exact Happ.
Qed.

Lemma cv3_xi_ok : forall nu p u eta V,
  (0 <= u)%Qc -> (0 < eta)%Qc ->
  AppCheck P nu p u V = true ->
  AppCheck H
    (rv3_name S (rv3_name T nu))
    (cv3_code p eta)
    ((rv3_Lambda S * rv3_Lambda T) * u + eta)
    (cv3_xi_witness nu p u eta V) = true.
Proof.
  intros nu p u eta V Hu Heta Happ. unfold cv3_xi_witness.
  eapply ec_app_weaken_ok.
  - apply cv3_composite_bound_le; assumption.
  - apply cv3_xi_raw_ok; assumption.
Qed.

Definition compose_realizable_v3 : RealizableMapV3 P H.
Proof.
  refine {|
    rv3_T := fun x => rv3_T S (rv3_T T x);
    rv3_Lambda := rv3_Lambda S * rv3_Lambda T;
    rv3_Lambda_nonneg := _;
    rv3_lipschitz := _;
    rv3_lip_derivation := rv3_lip_derivation T ++ rv3_lip_derivation S;
    rv3_name := fun nu => rv3_name S (rv3_name T nu);
    rv3_name_ok := _;
    rv3_code := cv3_code;
    rv3_code_witness := cv3_code_witness;
    rv3_code_ok := cv3_code_ok;
    rv3_xi := cv3_xi_witness;
    rv3_xi_ok := cv3_xi_ok;
    rv3_theta := fun a b W =>
      rv3_theta S (rv3_name T a) (rv3_name T b) (rv3_theta T a b W);
    rv3_theta_bound := _;
    rv3_theta_id := _;
    rv3_theta_comp := _
  |}.
  - rewrite <- Qcmult_0_l with (n := rv3_Lambda T).
    apply Qcmult_le_compat_r; [apply rv3_Lambda_nonneg | apply rv3_Lambda_nonneg].
  - intros x y.
    pose proof (rv3_lipschitz T x y) as HT.
    pose proof (rv3_lipschitz S (rv3_T T x) (rv3_T T y)) as HS.
    rewrite cv3_Qc2R_mult. rewrite Rmult_assoc.
    eapply Rle_trans; [exact HS |].
    apply Rmult_le_compat_l.
    + rewrite <- Qc2R_0. apply Qc2R_le. apply rv3_Lambda_nonneg.
    + exact HT.
  - intro nu. simpl. rewrite rv3_name_ok, rv3_name_ok. reflexivity.
  - intros a b W. simpl.
    eapply Qcle_trans; [apply rv3_theta_bound |].
    eapply Qcle_trans.
    + apply cv3_mult_le_mono_l; [apply rv3_Lambda_nonneg | apply rv3_theta_bound].
    + rewrite Qcmult_assoc. apply Qcle_refl.
  - intro a. simpl. rewrite rv3_theta_id. apply rv3_theta_id.
  - intros a b c W1 W2. simpl.
    rewrite rv3_theta_comp, rv3_theta_comp. reflexivity.
Defined.

Theorem compose_realizable_v3_lambda :
  rv3_Lambda compose_realizable_v3 = rv3_Lambda S * rv3_Lambda T.
Proof. reflexivity. Qed.

Theorem compose_realizable_v3_map : forall x : F P,
  rv3_T compose_realizable_v3 x = rv3_T S (rv3_T T x).
Proof. reflexivity. Qed.

End Composite.

Section ComposedLift.
Variables P G H : Presentation.
Variable T : RealizableMapV3 P G.
Variable S : RealizableMapV3 G H.

Definition composed_lift_object_v3 (c : EvidenceObject P) : EvidenceObject H :=
  lift_object_v3 G H S (lift_object_v3 P G T c).

Definition composed_lift_morphism_v3 {c d : EvidenceObject P}
    (f : EvidenceMorphism c d)
  : EvidenceMorphism (composed_lift_object_v3 c) (composed_lift_object_v3 d) :=
  lift_morphism_v3 G H S (lift_morphism_v3 P G T f).

Theorem composed_lift_underlying_v3 : forall c : EvidenceObject P,
  deltaF H (eo_name (composed_lift_object_v3 c))
  = rv3_T S (rv3_T T (deltaF P (eo_name c))).
Proof.
  intro c. unfold composed_lift_object_v3.
  rewrite (lift_underlying_v3 G H S (lift_object_v3 P G T c)).
  rewrite (lift_underlying_v3 P G T c). reflexivity.
Qed.

Theorem composed_lift_id_v3 : forall c : EvidenceObject P,
  composed_lift_morphism_v3 (id_evidence c)
  = id_evidence (composed_lift_object_v3 c).
Proof.
  intro c. unfold composed_lift_morphism_v3, composed_lift_object_v3.
  rewrite (lift_morphism_id_v3 P G T c).
  apply lift_morphism_id_v3.
Qed.

Theorem composed_lift_comp_v3 :
  forall c d e (f : EvidenceMorphism c d) (g : EvidenceMorphism d e),
    composed_lift_morphism_v3 (comp_evidence f g)
    = comp_evidence (composed_lift_morphism_v3 f) (composed_lift_morphism_v3 g).
Proof.
  intros c d e f g. unfold composed_lift_morphism_v3, composed_lift_object_v3.
  rewrite (lift_morphism_comp_v3 P G T c d e f g).
  apply lift_morphism_comp_v3.
Qed.

End ComposedLift.

End V3_CompositionV3.
