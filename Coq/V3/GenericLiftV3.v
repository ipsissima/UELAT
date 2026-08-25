(** * GenericLiftV3.v — Theorem 5.2 over the exact five-clause interface

    This is the migration target for Theorem 5.2.  Unlike the older
    GenericLift module, certificate construction consumes the explicit
    Xi_T field of Definition 5.1 directly.  No EvidenceClosure argument
    is needed to manufacture Xi_T after the fact. *)

From Stdlib Require Import Reals QArith Qreals Qcanon Lra Lia Field.
From UELAT.V3 Require Import EvidenceSyntax Presentation Evidence
  MetricReflection RealizableMapV3.
Local Open Scope Qc_scope.

Module V3_GenericLiftV3.

Import V3_EvidenceSyntax.
Import V3_Presentation.
Import V3_Evidence.
Import V3_MetricReflection.
Import V3_RealizableMapV3.

Section WithMap.
Variables P G : Presentation.
Variable T : RealizableMapV3 P G.

Definition gv3_three : Qc := 1 + 1 + 1.

Lemma gv3_zero_lt_one : (0 < 1)%Qc.
Proof.
  unfold Qclt. simpl. repeat rewrite Qred_correct. auto with qarith.
Qed.

Lemma gv3_pos_nonzero : forall q : Qc, (0 < q)%Qc -> q <> 0.
Proof.
  intros q Hq. apply not_eq_sym. apply Qclt_not_eq. exact Hq.
Qed.

Lemma gv3_two_lt_three : (1 + 1 < gv3_three)%Qc.
Proof.
  unfold gv3_three, Qclt, Qcplus. simpl.
  repeat rewrite Qred_correct. auto with qarith.
Qed.

Lemma gv3_three_pos : (0 < gv3_three)%Qc.
Proof.
  unfold gv3_three, Qclt, Qcplus. simpl.
  repeat rewrite Qred_correct. auto with qarith.
Qed.

Lemma gv3_three_nonzero : gv3_three <> 0.
Proof. apply gv3_pos_nonzero. exact gv3_three_pos. Qed.

Definition gv3_scale : Qc :=
  match Qclt_le_dec (rv3_Lambda T) 1 with
  | left _ => 1
  | right _ => rv3_Lambda T
  end.

Lemma gv3_scale_ge_one : (1 <= gv3_scale)%Qc.
Proof.
  unfold gv3_scale. destruct (Qclt_le_dec (rv3_Lambda T) 1) as [H|H].
  - apply Qcle_refl.
  - exact H.
Qed.

Lemma gv3_lambda_le_scale : (rv3_Lambda T <= gv3_scale)%Qc.
Proof.
  unfold gv3_scale. destruct (Qclt_le_dec (rv3_Lambda T) 1) as [H|H].
  - apply Qclt_le_weak. exact H.
  - apply Qcle_refl.
Qed.

Lemma gv3_scale_pos : (0 < gv3_scale)%Qc.
Proof. eapply Qclt_le_trans; [apply gv3_zero_lt_one | apply gv3_scale_ge_one]. Qed.

Lemma gv3_scale_nonzero : gv3_scale <> 0.
Proof. apply gv3_pos_nonzero. exact gv3_scale_pos. Qed.

Definition gv3_alpha_den : Qc := gv3_three * gv3_scale.

Lemma gv3_alpha_den_pos : (0 < gv3_alpha_den)%Qc.
Proof.
  unfold gv3_alpha_den.
  rewrite <- Qcmult_0_l with (n := gv3_scale).
  apply Qcmult_lt_compat_r; [apply gv3_scale_pos | apply gv3_three_pos].
Qed.

Lemma gv3_alpha_den_nonzero : gv3_alpha_den <> 0.
Proof. apply gv3_pos_nonzero. exact gv3_alpha_den_pos. Qed.

Lemma gv3_div_pos : forall a d : Qc, (0 < a)%Qc -> (0 < d)%Qc -> (0 < a / d)%Qc.
Proof.
  intros a d Ha Hd.
  apply Qcnot_le_lt. intro Hbad.
  assert (Hd0 : (0 <= d)%Qc) by (apply Qclt_le_weak; exact Hd).
  pose proof (Qcmult_le_compat_r (a / d) 0 d Hbad Hd0) as Hmul.
  assert (Hcancel : (a / d) * d = a).
  { field. apply gv3_pos_nonzero. exact Hd. }
  rewrite Hcancel, Qcmult_0_l in Hmul.
  exact (Qclt_not_le 0 a Ha Hmul).
Qed.

Definition gv3_alpha (eps : Qc) : Qc := eps / gv3_alpha_den.
Definition gv3_eta (eps : Qc) : Qc := eps / gv3_three.

Lemma gv3_alpha_pos : forall eps, (0 < eps)%Qc -> (0 < gv3_alpha eps)%Qc.
Proof. intros eps H. unfold gv3_alpha. apply gv3_div_pos; [exact H|apply gv3_alpha_den_pos]. Qed.

Lemma gv3_eta_pos : forall eps, (0 < eps)%Qc -> (0 < gv3_eta eps)%Qc.
Proof. intros eps H. unfold gv3_eta. apply gv3_div_pos; [exact H|apply gv3_three_pos]. Qed.

Lemma gv3_scale_alpha_eq_eta : forall eps, gv3_scale * gv3_alpha eps = gv3_eta eps.
Proof.
  intro eps. unfold gv3_alpha, gv3_alpha_den, gv3_eta.
  field. split; [apply gv3_three_nonzero | apply gv3_scale_nonzero].
Qed.

Lemma gv3_eta_twice_lt_eps :
  forall eps, (0 < eps)%Qc -> (gv3_eta eps + gv3_eta eps < eps)%Qc.
Proof.
  intros eps Heps.
  assert (Heta : (0 < gv3_eta eps)%Qc) by (apply gv3_eta_pos; exact Heps).
  pose proof (Qcmult_lt_compat_r (1 + 1) gv3_three (gv3_eta eps)
                Heta gv3_two_lt_three) as H.
  rewrite Qcmult_plus_distr_l, !Qcmult_1_l in H.
  unfold gv3_eta in H.
  rewrite Qcmult_div_r in H by apply gv3_three_nonzero.
  exact H.
Qed.

Lemma gv3_mult_le_mono_l :
  forall L a b : Qc, (0 <= L)%Qc -> (a <= b)%Qc -> (L * a <= L * b)%Qc.
Proof.
  intros L a b HL Hab.
  rewrite (Qcmult_comm L a), (Qcmult_comm L b).
  apply Qcmult_le_compat_r; assumption.
Qed.

Lemma gv3_scaled_source_le_eta :
  forall eps r,
    (0 < eps)%Qc -> (0 <= r)%Qc -> (r < gv3_alpha eps)%Qc ->
    (rv3_Lambda T * r <= gv3_eta eps)%Qc.
Proof.
  intros eps r Heps Hr0 Hrlt.
  assert (H1 : (rv3_Lambda T * r <= gv3_scale * r)%Qc).
  { apply Qcmult_le_compat_r; [apply gv3_lambda_le_scale | exact Hr0]. }
  assert (H2 : (gv3_scale * r < gv3_scale * gv3_alpha eps)%Qc).
  { rewrite (Qcmult_comm gv3_scale r), (Qcmult_comm gv3_scale (gv3_alpha eps)).
    apply Qcmult_lt_compat_r; [apply gv3_scale_pos | exact Hrlt]. }
  rewrite gv3_scale_alpha_eq_eta in H2.
  eapply Qcle_trans; [exact H1 | apply Qclt_le_weak; exact H2].
Qed.

Lemma gv3_output_nonneg :
  forall r eps, (0 <= r)%Qc -> (0 < eps)%Qc ->
    (0 <= rv3_Lambda T * r + gv3_eta eps)%Qc.
Proof.
  intros r eps Hr Heps.
  rewrite <- (Qcplus_0_l 0). apply Qcplus_le_compat.
  - rewrite <- (Qcmult_0_r (rv3_Lambda T)).
    apply gv3_mult_le_mono_l; [apply rv3_Lambda_nonneg | exact Hr].
  - apply Qclt_le_weak. apply gv3_eta_pos. exact Heps.
Qed.

Lemma gv3_output_lt :
  forall r eps,
    (0 < eps)%Qc -> (0 <= r)%Qc -> (r < gv3_alpha eps)%Qc ->
    (rv3_Lambda T * r + gv3_eta eps < eps)%Qc.
Proof.
  intros r eps Heps Hr Hrlt.
  eapply Qcle_lt_trans.
  - apply Qcplus_le_compat.
    + apply gv3_scaled_source_le_eta; assumption.
    + apply Qcle_refl.
  - apply gv3_eta_twice_lt_eps. exact Heps.
Qed.

Definition lift_run_v3 (c : EvidenceObject P) (eps : Qc)
  : CodeF G * Qc * list bool :=
  let alpha := gv3_alpha eps in
  let eta := gv3_eta eps in
  let '(p,r,V) := cs_run (eo_system c) alpha in
  (rv3_code T p eta,
   rv3_Lambda T * r + eta,
   rv3_xi T (eo_name c) p r eta V).

Definition lift_cert_system_v3 (c : EvidenceObject P)
  : CertSystem (rv3_name T (eo_name c)).
Proof.
  refine {| cs_run := lift_run_v3 c; cs_bound_lt := _; cs_accept := _ |}.
  - intros eps Heps. unfold lift_run_v3.
    set (alpha := gv3_alpha eps). set (eta := gv3_eta eps).
    destruct (cs_run (eo_system c) alpha) as [[p r] V] eqn:Hrun. simpl.
    assert (Ha : (0 < alpha)%Qc) by (unfold alpha; apply gv3_alpha_pos; exact Heps).
    pose proof (cs_bound_lt (eo_system c) alpha Ha) as Hsrc.
    rewrite Hrun in Hsrc. simpl in Hsrc. destruct Hsrc as [Hr0 Hrlt]. split.
    + unfold eta. apply gv3_output_nonneg; assumption.
    + unfold alpha, eta in *. apply gv3_output_lt; assumption.
  - intros eps Heps. unfold lift_run_v3.
    set (alpha := gv3_alpha eps). set (eta := gv3_eta eps).
    destruct (cs_run (eo_system c) alpha) as [[p r] V] eqn:Hrun. simpl.
    assert (Ha : (0 < alpha)%Qc) by (unfold alpha; apply gv3_alpha_pos; exact Heps).
    assert (He : (0 < eta)%Qc) by (unfold eta; apply gv3_eta_pos; exact Heps).
    pose proof (cs_bound_lt (eo_system c) alpha Ha) as Hb.
    pose proof (cs_accept (eo_system c) alpha Ha) as Hacc.
    rewrite Hrun in Hb, Hacc. simpl in Hb, Hacc. destruct Hb as [Hr0 _].
    apply rv3_xi_ok; assumption.
Defined.

Definition lift_object_v3 (c : EvidenceObject P) : EvidenceObject G :=
  {| eo_name := rv3_name T (eo_name c); eo_system := lift_cert_system_v3 c |}.

Theorem lift_underlying_v3 : forall c,
  deltaF G (eo_name (lift_object_v3 c)) = rv3_T T (deltaF P (eo_name c)).
Proof. intro c. simpl. apply rv3_name_ok. Qed.

Definition lift_morphism_v3 {c d : EvidenceObject P}
    (f : EvidenceMorphism c d)
  : EvidenceMorphism (lift_object_v3 c) (lift_object_v3 d).
Proof.
  refine (@Build_EvidenceMorphism G (lift_object_v3 c) (lift_object_v3 d)
            (rv3_Lambda T * em_bound f)
            (rv3_theta T (eo_name c) (eo_name d) (@em_spine P c d f)) _ _).
  - apply (proj2 (qcleb_iff _ _)).
    rewrite <- (Qcmult_0_r (rv3_Lambda T)).
    apply gv3_mult_le_mono_l; [apply rv3_Lambda_nonneg | apply em_bound_nonneg].
  - apply (proj2 (qcleb_iff _ _)).
    eapply Qcle_trans; [apply rv3_theta_bound |].
    apply gv3_mult_le_mono_l; [apply rv3_Lambda_nonneg | apply em_spine_le_bound].
Defined.

Theorem lift_morphism_id_v3 : forall c,
  lift_morphism_v3 (id_evidence c) = id_evidence (lift_object_v3 c).
Proof.
  intro c. apply EvidenceMorphism_eq.
  - simpl. apply Qcmult_0_r.
  - simpl. apply rv3_theta_id.
Qed.

Theorem lift_morphism_comp_v3 :
  forall c d e (f : EvidenceMorphism c d) (g : EvidenceMorphism d e),
    lift_morphism_v3 (comp_evidence f g)
    = comp_evidence (lift_morphism_v3 f) (lift_morphism_v3 g).
Proof.
  intros c d e f g. apply EvidenceMorphism_eq.
  - simpl. apply Qcmult_plus_distr_r.
  - simpl. apply rv3_theta_comp.
Qed.

Theorem lift_achievable_v3 :
  forall (c d : EvidenceObject P) (q : Qc),
    achievable_bound P c d q ->
    achievable_bound G (lift_object_v3 c) (lift_object_v3 d) (rv3_Lambda T * q).
Proof.
  intros c d q [W Hle].
  exists (rv3_theta T (eo_name c) (eo_name d) W).
  eapply Qcle_trans; [apply rv3_theta_bound |].
  apply gv3_mult_le_mono_l; [apply rv3_Lambda_nonneg | exact Hle].
Qed.

Lemma gv3_Qc2R_mult : forall p q : Qc,
  Qc2R (p * q) = (Qc2R p * Qc2R q)%R.
Proof.
  intros p q. unfold Qc2R. rewrite <- Q2R_mult.
  apply Qeq_eqR. apply Qred_correct.
Qed.

Theorem lift_lawvere_lipschitz_v3 :
  forall (c d : EvidenceObject P) (rP rG : R),
    is_lawvere_dist P c d rP ->
    is_lawvere_dist G (lift_object_v3 c) (lift_object_v3 d) rG ->
    (rG <= Qc2R (rv3_Lambda T) * rP)%R.
Proof.
  intros c d rP rG [_ HnearP] [HlowerG _].
  set (L := Qc2R (rv3_Lambda T)).
  assert (HL : (0 <= L)%R).
  { unfold L. rewrite <- Qc2R_0. apply Qc2R_le. apply rv3_Lambda_nonneg. }
  apply Rnot_lt_le. intro Hbad.
  set (eps := ((rG - L * rP) / 2)%R).
  assert (Heps : (0 < eps)%R) by (unfold eps; lra).
  assert (Hden : (0 < L + 1)%R) by lra.
  set (delta := (eps / (L + 1))%R).
  assert (Hdelta : (0 < delta)%R).
  { unfold delta. apply Rdiv_lt_0_compat; assumption. }
  assert (Hratio : (L * delta < eps)%R).
  {
    apply (Rmult_lt_reg_r (L + 1)); [exact Hden |].
    unfold delta. rewrite Rmult_assoc.
    replace ((eps / (L + 1)) * (L + 1))%R with eps by (field; lra).
    nra.
  }
  destruct (HnearP delta Hdelta) as [q [Hq Hqnear]].
  pose proof (lift_achievable_v3 c d q Hq) as Hlift.
  specialize (HlowerG (rv3_Lambda T * q)%Qc Hlift).
  rewrite gv3_Qc2R_mult in HlowerG.
  assert (Hq_upper : (Qc2R q < rP + delta)%R) by exact Hqnear.
  assert (HLq : (L * Qc2R q < L * rP + eps)%R).
  {
    destruct (Req_dec L 0) as [HL0|HL0].
    - rewrite HL0. simpl. lra.
    - assert (HLpos : 0 < L) by lra.
      assert (Hmul : L * Qc2R q < L * (rP + delta)).
      { apply Rmult_lt_compat_l; assumption. }
      nra.
  }
  unfold L in *. lra.
Qed.

End WithMap.
End V3_GenericLiftV3.
