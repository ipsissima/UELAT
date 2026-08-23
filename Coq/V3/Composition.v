(** * Composition.v — Proposition 5.3 (closure under composition)

    Paper reference: Ballús Santacana, arXiv:2506.22693 v3,
    Proposition 5.3.

    This module follows the printed proof quantitatively. For
    T : F -> G and S : G -> H, the composite finite-code realizer uses

      beta(eta) = eta / (2 * max(1,Lambda_S))

    for the T-stage and eta/2 for the S-stage. The combined certified
    defect is <= eta and is then promoted to the announced defect eta by
    the computational AppCheck weakening rule of Def. 2.1.

    The second half of the proposition is intentionally weaker than a
    uniqueness statement: S_* o T_* is proved to be a valid evidence
    lift of S o T. We do NOT claim it is literally equal to every
    possible lift built from a different finite compiler. *)

From Stdlib Require Import List Reals QArith Qreals Qcanon Lra Lia Field.
From UELAT.V3 Require Import EvidenceSyntax Presentation Evidence
  RealizableMap GenericLift.
Import ListNotations.
Local Open Scope Qc_scope.

Module V3_Composition.

Import V3_EvidenceSyntax.
Import V3_Presentation.
Import V3_Evidence.
Import V3_RealizableMap.
Import V3_GenericLift.

Section CompositeMap.
Variables P G H : Presentation.
Variable T : RealizableMap P G.
Variable S : RealizableMap G H.
Variable ECH : EvidenceClosure (P := H).

Definition comp_two : Qc := 1 + 1.

Lemma comp_two_pos : (0 < comp_two)%Qc.
Proof.
  unfold comp_two, Qclt, Qcplus. simpl.
  repeat rewrite Qred_correct.
  auto with qarith.
Qed.

Lemma comp_two_nonzero : comp_two <> 0.
Proof. apply qc_pos_nonzero. exact comp_two_pos. Qed.

Definition comp_scale : Qc :=
  match Qclt_le_dec (rm_Lambda S) 1 with
  | left _  => 1
  | right _ => rm_Lambda S
  end.

Lemma comp_scale_ge_one : (1 <= comp_scale)%Qc.
Proof.
  unfold comp_scale. destruct (Qclt_le_dec (rm_Lambda S) 1) as [Hlt|Hge].
  - apply Qcle_refl.
  - exact Hge.
Qed.

Lemma comp_lambdaS_le_scale : (rm_Lambda S <= comp_scale)%Qc.
Proof.
  unfold comp_scale. destruct (Qclt_le_dec (rm_Lambda S) 1) as [Hlt|Hge].
  - apply Qclt_le_weak. exact Hlt.
  - apply Qcle_refl.
Qed.

Lemma comp_scale_pos : (0 < comp_scale)%Qc.
Proof.
  eapply Qclt_le_trans.
  - exact qc_zero_lt_one.
  - apply comp_scale_ge_one.
Qed.

Lemma comp_scale_nonzero : comp_scale <> 0.
Proof. apply qc_pos_nonzero. exact comp_scale_pos. Qed.

Definition comp_beta_den : Qc := comp_two * comp_scale.

Lemma comp_beta_den_pos : (0 < comp_beta_den)%Qc.
Proof.
  unfold comp_beta_den.
  rewrite <- Qcmult_0_l with (n := comp_scale).
  apply Qcmult_lt_compat_r; [apply comp_scale_pos | apply comp_two_pos].
Qed.

Lemma comp_beta_den_nonzero : comp_beta_den <> 0.
Proof. apply qc_pos_nonzero. exact comp_beta_den_pos. Qed.

Definition comp_beta (eta : Qc) : Qc := eta / comp_beta_den.
Definition comp_half (eta : Qc) : Qc := eta / comp_two.

Lemma comp_div_pos :
  forall a d : Qc, (0 < a)%Qc -> (0 < d)%Qc -> (0 < a / d)%Qc.
Proof.
  intros a d Ha Hd.
  apply Qcnot_le_lt. intro Hbad.
  assert (Hd0 : (0 <= d)%Qc) by (apply Qclt_le_weak; exact Hd).
  pose proof (Qcmult_le_compat_r (a / d) 0 d Hbad Hd0) as Hmul.
  assert (Hcancel : (a / d) * d = a).
  { field. apply qc_pos_nonzero. exact Hd. }
  rewrite Hcancel, Qcmult_0_l in Hmul.
  exact (Qclt_not_le 0 a Ha Hmul).
Qed.

Lemma comp_beta_pos :
  forall eta : Qc, (0 < eta)%Qc -> (0 < comp_beta eta)%Qc.
Proof.
  intros eta Heta. unfold comp_beta.
  apply comp_div_pos; [exact Heta | apply comp_beta_den_pos].
Qed.

Lemma comp_half_pos :
  forall eta : Qc, (0 < eta)%Qc -> (0 < comp_half eta)%Qc.
Proof.
  intros eta Heta. unfold comp_half.
  apply comp_div_pos; [exact Heta | apply comp_two_pos].
Qed.

Lemma comp_scale_beta_eq_half :
  forall eta : Qc, comp_scale * comp_beta eta = comp_half eta.
Proof.
  intro eta. unfold comp_beta, comp_beta_den, comp_half.
  field.
  apply comp_beta_den_nonzero.
Qed.

Lemma comp_two_half_eq :
  forall eta : Qc, comp_half eta + comp_half eta = eta.
Proof.
  intro eta. unfold comp_half.
  field. apply comp_two_nonzero.
Qed.

Lemma comp_scaled_beta_le_half :
  forall eta : Qc, (0 < eta)%Qc ->
    (rm_Lambda S * comp_beta eta <= comp_half eta)%Qc.
Proof.
  intros eta Heta.
  assert (Hb0 : (0 <= comp_beta eta)%Qc).
  { apply Qclt_le_weak. apply comp_beta_pos. exact Heta. }
  eapply Qcle_trans.
  - apply Qcmult_le_compat_r; [apply comp_lambdaS_le_scale | exact Hb0].
  - rewrite comp_scale_beta_eq_half. apply Qcle_refl.
Qed.

Lemma comp_defect_le_eta :
  forall eta : Qc, (0 < eta)%Qc ->
    (rm_Lambda S * comp_beta eta + comp_half eta <= eta)%Qc.
Proof.
  intros eta Heta.
  eapply Qcle_trans.
  - apply Qcplus_le_compat.
    + apply comp_scaled_beta_le_half. exact Heta.
    + apply Qcle_refl.
  - rewrite comp_two_half_eq. apply Qcle_refl.
Qed.

Lemma comp_Qc2R_mult :
  forall p q : Qc, Qc2R (p * q) = (Qc2R p * Qc2R q)%R.
Proof.
  intros p q. unfold Qc2R. rewrite <- Q2R_mult.
  apply Qeq_eqR. apply Qred_correct.
Qed.

Definition comp_code (p : CodeF P) (eta : Qc) : CodeF H :=
  rm_code S (rm_code T p (comp_beta eta)) (comp_half eta).

Definition comp_raw_witness (p : CodeF P) (eta : Qc) : list bool :=
  rm_app_transport_witness G H S ECH
    (rm_name T (iotaF P p))
    (rm_code T p (comp_beta eta))
    (comp_beta eta)
    (comp_half eta)
    (rm_code_witness T p (comp_beta eta)).

Definition comp_code_witness (p : CodeF P) (eta : Qc) : list bool :=
  ec_app_weaken_witness ECH
    (rm_name S (rm_name T (iotaF P p)))
    (comp_code p eta)
    (rm_Lambda S * comp_beta eta + comp_half eta)
    eta
    (comp_raw_witness p eta).

Lemma comp_raw_ok :
  forall (p : CodeF P) (eta : Qc),
    (0 < eta)%Qc ->
    AppCheck H
      (rm_name S (rm_name T (iotaF P p)))
      (comp_code p eta)
      (rm_Lambda S * comp_beta eta + comp_half eta)
      (comp_raw_witness p eta) = true.
Proof.
  intros p eta Heta.
  unfold comp_raw_witness, comp_code.
  apply rm_app_transport_ok.
  - apply comp_half_pos. exact Heta.
  - apply rm_code_ok. apply comp_beta_pos. exact Heta.
Qed.

Lemma comp_code_ok :
  forall (p : CodeF P) (eta : Qc),
    (0 < eta)%Qc ->
    AppCheck H
      (rm_name S (rm_name T (iotaF P p)))
      (comp_code p eta) eta (comp_code_witness p eta) = true.
Proof.
  intros p eta Heta. unfold comp_code_witness.
  eapply ec_app_weaken_ok.
  - apply comp_defect_le_eta. exact Heta.
  - apply comp_raw_ok. exact Heta.
Qed.

Definition compose_realizable : RealizableMap P H.
Proof.
  refine {|
    rm_T := fun x => rm_T S (rm_T T x);
    rm_Lambda := rm_Lambda S * rm_Lambda T;
    rm_Lambda_nonneg := _;
    rm_lipschitz := _;
    rm_name := fun nu => rm_name S (rm_name T nu);
    rm_name_ok := _;
    rm_lip_store := rm_lip_store T ++ rm_lip_store S;
    rm_lip_apply := fun _ nu p q V =>
      rm_theta S
        (rm_name T nu)
        (rm_name T (iotaF P p))
        (rm_lip_apply T (rm_lip_store T) nu p q V);
    rm_lip_apply_ok := _;
    rm_code := comp_code;
    rm_code_witness := comp_code_witness;
    rm_code_ok := comp_code_ok;
    rm_theta := fun a b W =>
      rm_theta S (rm_name T a) (rm_name T b) (rm_theta T a b W);
    rm_theta_bound := _;
    rm_theta_id := _;
    rm_theta_comp := _
  |}.
  - rewrite <- Qcmult_0_l with (n := rm_Lambda T).
    apply Qcmult_le_compat_r; [apply rm_Lambda_nonneg | apply rm_Lambda_nonneg].
  - intros x y.
    pose proof (rm_lipschitz T x y) as HT.
    pose proof (rm_lipschitz S (rm_T T x) (rm_T T y)) as HS.
    rewrite comp_Qc2R_mult.
    rewrite Rmult_assoc.
    eapply Rle_trans; [exact HS |].
    apply Rmult_le_compat_l.
    + rewrite <- Qc2R_0. apply Qc2R_le. apply rm_Lambda_nonneg.
    + exact HT.
  - intro nu. simpl.
    rewrite rm_name_ok. rewrite rm_name_ok. reflexivity.
  - intros nu p q V Happ. simpl.
    eapply Qcle_trans.
    + apply rm_theta_bound.
    + eapply Qcle_trans.
      * apply qc_mult_le_mono_l.
        -- apply rm_Lambda_nonneg.
        -- apply rm_lip_apply_ok. exact Happ.
      * rewrite Qcmult_assoc. apply Qcle_refl.
  - intros a b W. simpl.
    eapply Qcle_trans.
    + apply rm_theta_bound.
    + eapply Qcle_trans.
      * apply qc_mult_le_mono_l.
        -- apply rm_Lambda_nonneg.
        -- apply rm_theta_bound.
      * rewrite Qcmult_assoc. apply Qcle_refl.
  - intro a. simpl.
    rewrite rm_theta_id. apply rm_theta_id.
  - intros a b c W1 W2. simpl.
    rewrite rm_theta_comp.
    rewrite rm_theta_comp.
    reflexivity.
Defined.

Theorem compose_realizable_lambda :
  rm_Lambda compose_realizable = rm_Lambda S * rm_Lambda T.
Proof. reflexivity. Qed.

Theorem compose_realizable_map :
  forall x : F P,
    rm_T compose_realizable x = rm_T S (rm_T T x).
Proof. intro x. reflexivity. Qed.

End CompositeMap.

Section ComposedLift.
Variables P G H : Presentation.
Variable T : RealizableMap P G.
Variable S : RealizableMap G H.
Variable ECG : EvidenceClosure (P := G).
Variable ECH : EvidenceClosure (P := H).

Definition composed_lift_object (c : EvidenceObject P) : EvidenceObject H :=
  lift_object G H S ECH (lift_object P G T ECG c).

Definition composed_lift_morphism {c d : EvidenceObject P}
    (f : EvidenceMorphism c d)
  : EvidenceMorphism (composed_lift_object c) (composed_lift_object d) :=
  lift_morphism G H S ECH (lift_morphism P G T ECG f).

Theorem composed_lift_underlying :
  forall c : EvidenceObject P,
    deltaF H (eo_name (composed_lift_object c))
    = rm_T S (rm_T T (deltaF P (eo_name c))).
Proof.
  intro c. unfold composed_lift_object.
  rewrite (lift_underlying G H S ECH (lift_object P G T ECG c)).
  rewrite (lift_underlying P G T ECG c).
  reflexivity.
Qed.

Theorem composed_lift_id :
  forall c : EvidenceObject P,
    composed_lift_morphism (id_evidence c)
    = id_evidence (composed_lift_object c).
Proof.
  intro c. unfold composed_lift_morphism, composed_lift_object.
  rewrite (lift_morphism_id P G T ECG c).
  apply lift_morphism_id.
Qed.

Theorem composed_lift_comp :
  forall (c d e : EvidenceObject P)
         (f : EvidenceMorphism c d) (g : EvidenceMorphism d e),
    composed_lift_morphism (comp_evidence f g)
    = comp_evidence (composed_lift_morphism f) (composed_lift_morphism g).
Proof.
  intros c d e f g. unfold composed_lift_morphism, composed_lift_object.
  rewrite (lift_morphism_comp P G T ECG c d e f g).
  apply lift_morphism_comp.
Qed.

Theorem composed_lift_is_valid_for_composite :
  forall c : EvidenceObject P,
    deltaF H (eo_name (composed_lift_object c))
    = rm_T S (rm_T T (deltaF P (eo_name c))).
Proof. apply composed_lift_underlying. Qed.

End ComposedLift.

End V3_Composition.