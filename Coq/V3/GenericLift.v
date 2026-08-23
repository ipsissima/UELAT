(** * GenericLift.v — Theorem 5.2, exact functorial and metric content

    This module formalizes the generic lifting theorem at the strength
    actually printed in v3.  It uses the manuscript's quantitative
    algorithm

      alpha_T(eps) = eps / (3 * max(1,Lambda_T)),
      eta(eps)     = eps / 3,

    so one source certificate at [alpha_T(eps)] and one code-realizer
    call at defect [eps/3] produce the target certificate.

    Crucially, this theorem does NOT assume Definition 4.3 evidence
    regularity.  Definition 2.1 already requires the evidence language
    to support application of a stored Lipschitz estimate to a tagged
    source proof.  [V3_RealizableMap.rm_lip_apply] exposes exactly that
    operation, so source AppCheck evidence is transported directly.

    Genuine proof-relevant morphisms [(q,W)] are sent to
    [(Lambda_T q, Theta_T W)]. Identity and composition are Leibniz
    equalities, the forgetful square commutes, and the metric inequality
    is proved in the GLB representation of [d_Cert]. *)

From Stdlib Require Import Reals QArith Qreals Qcanon Lra Lia Field.
From UELAT.V3 Require Import EvidenceSyntax Presentation Evidence
  MetricReflection RealizableMap.
Local Open Scope Qc_scope.

Module V3_GenericLift.

Import V3_EvidenceSyntax.
Import V3_Presentation.
Import V3_Evidence.
Import V3_MetricReflection.
Import V3_RealizableMap.

Section WithMap.
Variables P G : Presentation.
Variable T : RealizableMap P G.
(** This record is the Rocq realization of the target presentation's
    Def. 2.1 evidence-language closure rules. *)
Variable ECG : EvidenceClosure (P := G).

(** ** Exact quantitative budget from Theorem 5.2. *)
Definition qc_three : Qc := 1 + 1 + 1.

Lemma qc_zero_lt_one : (0 < 1)%Qc.
Proof.
  unfold Qclt. simpl.
  repeat rewrite Qred_correct.
  auto with qarith.
Qed.

Lemma qc_pos_nonzero :
  forall q : Qc, (0 < q)%Qc -> q <> 0.
Proof.
  intros q Hq.
  apply not_eq_sym.
  apply Qclt_not_eq.
  exact Hq.
Qed.

Lemma qc_two_lt_three : (1 + 1 < qc_three)%Qc.
Proof.
  unfold qc_three, Qclt, Qcplus. simpl.
  repeat rewrite Qred_correct.
  auto with qarith.
Qed.

Lemma qc_three_pos : (0 < qc_three)%Qc.
Proof.
  unfold qc_three, Qclt, Qcplus. simpl.
  repeat rewrite Qred_correct.
  auto with qarith.
Qed.

Lemma qc_three_nonzero : qc_three <> 0.
Proof. apply qc_pos_nonzero. exact qc_three_pos. Qed.

(** A computational max(1,Lambda_T), using decidable Qc order. *)
Definition rm_scale : Qc :=
  match Qclt_le_dec (rm_Lambda T) 1 with
  | left _  => 1
  | right _ => rm_Lambda T
  end.

Lemma rm_scale_ge_one : (1 <= rm_scale)%Qc.
Proof.
  unfold rm_scale. destruct (Qclt_le_dec (rm_Lambda T) 1) as [Hlt|Hge].
  - apply Qcle_refl.
  - exact Hge.
Qed.

Lemma rm_lambda_le_scale : (rm_Lambda T <= rm_scale)%Qc.
Proof.
  unfold rm_scale. destruct (Qclt_le_dec (rm_Lambda T) 1) as [Hlt|Hge].
  - apply Qclt_le_weak. exact Hlt.
  - apply Qcle_refl.
Qed.

Lemma rm_scale_pos : (0 < rm_scale)%Qc.
Proof.
  eapply Qclt_le_trans; [exact qc_zero_lt_one | apply rm_scale_ge_one].
Qed.

Lemma rm_scale_nonzero : rm_scale <> 0.
Proof. apply qc_pos_nonzero. exact rm_scale_pos. Qed.

Definition rm_alpha_den : Qc := qc_three * rm_scale.

Lemma rm_alpha_den_pos : (0 < rm_alpha_den)%Qc.
Proof.
  unfold rm_alpha_den.
  rewrite <- Qcmult_0_l with (n := rm_scale).
  apply Qcmult_lt_compat_r; [apply rm_scale_pos | apply qc_three_pos].
Qed.

Lemma rm_alpha_den_nonzero : rm_alpha_den <> 0.
Proof. apply qc_pos_nonzero. exact rm_alpha_den_pos. Qed.

Lemma qc_div_pos :
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

Definition rm_alpha (eps : Qc) : Qc := eps / rm_alpha_den.
Definition rm_eta   (eps : Qc) : Qc := eps / qc_three.

Lemma rm_alpha_pos :
  forall eps : Qc, (0 < eps)%Qc -> (0 < rm_alpha eps)%Qc.
Proof.
  intros eps Heps. unfold rm_alpha.
  apply qc_div_pos; [exact Heps | apply rm_alpha_den_pos].
Qed.

Lemma rm_eta_pos :
  forall eps : Qc, (0 < eps)%Qc -> (0 < rm_eta eps)%Qc.
Proof.
  intros eps Heps. unfold rm_eta.
  apply qc_div_pos; [exact Heps | apply qc_three_pos].
Qed.

Lemma rm_scale_alpha_eq_eta :
  forall eps : Qc, rm_scale * rm_alpha eps = rm_eta eps.
Proof.
  intro eps. unfold rm_alpha, rm_alpha_den, rm_eta.
  field.
  split; [apply qc_three_nonzero | apply rm_scale_nonzero].
Qed.

Lemma rm_eta_twice_lt_eps :
  forall eps : Qc, (0 < eps)%Qc ->
    (rm_eta eps + rm_eta eps < eps)%Qc.
Proof.
  intros eps Heps.
  assert (Heta : (0 < rm_eta eps)%Qc) by (apply rm_eta_pos; exact Heps).
  pose proof (Qcmult_lt_compat_r (1 + 1) qc_three (rm_eta eps)
                Heta qc_two_lt_three) as H.
  rewrite Qcmult_plus_distr_l, !Qcmult_1_l in H.
  unfold rm_eta in H.
  rewrite Qcmult_div_r in H by apply qc_three_nonzero.
  exact H.
Qed.

Lemma rm_scaled_source_le_eta :
  forall eps r : Qc,
    (0 < eps)%Qc -> (0 <= r)%Qc -> (r < rm_alpha eps)%Qc ->
    (rm_Lambda T * r <= rm_eta eps)%Qc.
Proof.
  intros eps r Heps Hr0 Hrlt.
  assert (H1 : (rm_Lambda T * r <= rm_scale * r)%Qc).
  { apply Qcmult_le_compat_r; [apply rm_lambda_le_scale | exact Hr0]. }
  assert (H2 : (rm_scale * r < rm_scale * rm_alpha eps)%Qc).
  {
    rewrite (Qcmult_comm rm_scale r), (Qcmult_comm rm_scale (rm_alpha eps)).
    apply Qcmult_lt_compat_r; [apply rm_scale_pos | exact Hrlt].
  }
  rewrite rm_scale_alpha_eq_eta in H2.
  eapply Qcle_trans; [exact H1 | apply Qclt_le_weak; exact H2].
Qed.

Lemma rm_output_error_nonneg :
  forall r eps : Qc,
    (0 <= r)%Qc -> (0 < eps)%Qc ->
    (0 <= rm_Lambda T * r + rm_eta eps)%Qc.
Proof.
  intros r eps Hr0 Heps.
  apply Qcplus_le_compat.
  - rewrite <- (Qcmult_0_r (rm_Lambda T)).
    apply qc_mult_le_mono_l; [apply rm_Lambda_nonneg | exact Hr0].
  - apply Qclt_le_weak. apply rm_eta_pos. exact Heps.
Qed.

Lemma rm_output_error_lt :
  forall r eps : Qc,
    (0 < eps)%Qc -> (0 <= r)%Qc -> (r < rm_alpha eps)%Qc ->
    (rm_Lambda T * r + rm_eta eps < eps)%Qc.
Proof.
  intros r eps Heps Hr0 Hrlt.
  eapply Qcle_lt_trans.
  - apply Qcplus_le_compat.
    + apply rm_scaled_source_le_eta; assumption.
    + apply Qcle_refl.
  - apply rm_eta_twice_lt_eps. exact Heps.
Qed.

(** ** Object map of T_* — exact printed algorithm. *)
Definition lift_run (c : EvidenceObject P) (eps : Qc)
  : CodeF G * Qc * list bool :=
  let alpha := rm_alpha eps in
  let eta   := rm_eta eps in
  let '(p, r, V) := cs_run (eo_system c) alpha in
  (rm_code T p eta,
   rm_Lambda T * r + eta,
   rm_app_transport_witness P G T ECG (eo_name c) p r eta V).

Definition lift_cert_system (c : EvidenceObject P)
  : CertSystem (rm_name T (eo_name c)).
Proof.
  refine {| cs_run := lift_run c;
            cs_bound_lt := _;
            cs_accept := _ |}.
  - intros eps Heps.
    unfold lift_run.
    set (alpha := rm_alpha eps).
    set (eta := rm_eta eps).
    destruct (cs_run (eo_system c) alpha) as [[p r] V] eqn:Hrun.
    simpl.
    assert (Halpha : (0 < alpha)%Qc).
    { unfold alpha. apply rm_alpha_pos. exact Heps. }
    pose proof (cs_bound_lt (eo_system c) alpha Halpha) as Hsrc.
    rewrite Hrun in Hsrc. simpl in Hsrc.
    destruct Hsrc as [Hr0 Hrlt]. split.
    + unfold eta. apply rm_output_error_nonneg; assumption.
    + unfold alpha, eta in *. apply rm_output_error_lt; assumption.
  - intros eps Heps.
    unfold lift_run.
    set (alpha := rm_alpha eps).
    set (eta := rm_eta eps).
    destruct (cs_run (eo_system c) alpha) as [[p r] V] eqn:Hrun.
    simpl.
    assert (Halpha : (0 < alpha)%Qc).
    { unfold alpha. apply rm_alpha_pos. exact Heps. }
    assert (Heta : (0 < eta)%Qc).
    { unfold eta. apply rm_eta_pos. exact Heps. }
    pose proof (cs_accept (eo_system c) alpha Halpha) as Hsrc.
    rewrite Hrun in Hsrc. simpl in Hsrc.
    apply rm_app_transport_ok; assumption.
Defined.

Definition lift_object (c : EvidenceObject P) : EvidenceObject G :=
  {| eo_name := rm_name T (eo_name c);
     eo_system := lift_cert_system c |}.

Theorem lift_underlying :
  forall c : EvidenceObject P,
    deltaF G (eo_name (lift_object c))
    = rm_T T (deltaF P (eo_name c)).
Proof.
  intro c. simpl. apply rm_name_ok.
Qed.

Theorem lift_run_uses_printed_budget :
  forall (c : EvidenceObject P) (eps : Qc),
    lift_run c eps =
      let '(p, r, V) := cs_run (eo_system c) (rm_alpha eps) in
      (rm_code T p (rm_eta eps),
       rm_Lambda T * r + rm_eta eps,
       rm_app_transport_witness P G T ECG
         (eo_name c) p r (rm_eta eps) V).
Proof. reflexivity. Qed.

(** ** Morphism map: (q,W) |-> (Lambda q, Theta W). *)
Definition lift_morphism {c d : EvidenceObject P}
    (f : EvidenceMorphism c d)
  : EvidenceMorphism (lift_object c) (lift_object d).
Proof.
  refine {| em_q := rm_Lambda T * em_bound f;
            em_spine := rm_theta T (eo_name c) (eo_name d) (em_spine f);
            em_nonneg := _;
            em_slack := _ |}.
  - apply (proj2 (qcleb_iff _ _)).
    rewrite <- (Qcmult_0_r (rm_Lambda T)).
    apply qc_mult_le_mono_l.
    + apply rm_Lambda_nonneg.
    + apply em_bound_nonneg.
  - apply (proj2 (qcleb_iff _ _)).
    eapply Qcle_trans.
    + apply rm_theta_bound.
    + apply qc_mult_le_mono_l.
      * apply rm_Lambda_nonneg.
      * apply em_spine_le_bound.
Defined.

Theorem lift_morphism_id :
  forall c : EvidenceObject P,
    lift_morphism (id_evidence c) = id_evidence (lift_object c).
Proof.
  intro c. apply EvidenceMorphism_eq.
  - simpl. apply Qcmult_0_r.
  - simpl. apply rm_theta_id.
Qed.

Theorem lift_morphism_comp :
  forall (c d e : EvidenceObject P)
         (f : EvidenceMorphism c d) (g : EvidenceMorphism d e),
    lift_morphism (comp_evidence f g)
    = comp_evidence (lift_morphism f) (lift_morphism g).
Proof.
  intros c d e f g. apply EvidenceMorphism_eq.
  - simpl. apply Qcmult_plus_distr_r.
  - simpl. apply rm_theta_comp.
Qed.

Theorem lift_achievable :
  forall (c d : EvidenceObject P) (q : Qc),
    achievable_bound P c d q ->
    achievable_bound G (lift_object c) (lift_object d) (rm_Lambda T * q).
Proof.
  intros c d q Hq.
  unfold achievable_bound in *; simpl in *.
  apply rm_certified_dist. exact Hq.
Qed.

Lemma Qc2R_mult :
  forall p q : Qc, Qc2R (p * q) = (Qc2R p * Qc2R q)%R.
Proof.
  intros p q. unfold Qc2R. rewrite <- Q2R_mult.
  apply Qeq_eqR. apply Qred_correct.
Qed.

(** ** Metric-reflection part of Theorem 5.2. *)
Theorem lift_lawvere_lipschitz :
  forall (c d : EvidenceObject P) (rP rG : R),
    is_lawvere_dist P c d rP ->
    is_lawvere_dist G (lift_object c) (lift_object d) rG ->
    (rG <= Qc2R (rm_Lambda T) * rP)%R.
Proof.
  intros c d rP rG [_ HnearP] [HlowerG _].
  set (L := Qc2R (rm_Lambda T)).
  assert (HL : (0 <= L)%R).
  { unfold L. rewrite <- Qc2R_0. apply Qc2R_le. apply rm_Lambda_nonneg. }
  apply Rnot_lt_le. intro Hbad.
  set (eps := (rG - L * rP) / 2)%R.
  assert (Heps : (0 < eps)%R) by (unfold eps; lra).
  assert (Hden : (0 < L + 1)%R) by lra.
  set (delta := eps / (L + 1))%R.
  assert (Hdelta : (0 < delta)%R).
  { unfold delta. apply Rdiv_lt_0_compat; assumption. }
  assert (Hratio : (L * delta < eps)%R).
  {
    apply (Rmult_lt_reg_r (L + 1)); [exact Hden |].
    unfold delta.
    rewrite Rmult_assoc.
    replace ((eps / (L + 1)) * (L + 1))%R with eps.
    2:{ field. lra. }
    nra.
  }
  destruct (HnearP delta Hdelta) as [q [Hqacc Hqnear]].
  pose proof (lift_achievable c d q Hqacc) as Htgt.
  specialize (HlowerG (rm_Lambda T * q) Htgt).
  rewrite Qc2R_mult in HlowerG.
  unfold L in HlowerG at 2.
  nra.
Qed.

End WithMap.

(** ** Correspondence with v3

    Theorem 5.2:
      exact printed source tolerance  -> rm_alpha
      exact printed realizer defect   -> rm_eta
      executable object map           -> lift_cert_system/lift_object
      forgetful square                -> lift_underlying
      morphism map                    -> lift_morphism
      strict functor laws             -> lift_morphism_id,
                                        lift_morphism_comp
      metric Lipschitz statement      -> lift_lawvere_lipschitz

    There is deliberately no EvidenceRegular hypothesis here.  The
    source AppCheck certificate is transported by Def. 2.1's stored
    Lipschitz evidence rule, exposed by RealizableMap.rm_lip_apply.

    Status remains IN-PROGRESS until this exact branch compiles, coqchk
    passes, and Print Assumptions reports are committed. *)

End V3_GenericLift.