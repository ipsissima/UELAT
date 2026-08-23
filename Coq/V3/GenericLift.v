(** * GenericLift.v — Theorem 5.2, functorial and metric content

    Completes the generic lift built in [V3_RealizableMap].  Objects are
    transported by the executable certificate-system construction there;
    this module transports the genuine proof-relevant morphisms [(q,W)],
    proves strict identity/composition laws, and proves the Lawvere-metric
    Lipschitz inequality in the GLB representation used by §3. *)

From Stdlib Require Import Reals QArith Qreals Qcanon Lra Lia Field.
From UELAT.V3 Require Import EvidenceSyntax Presentation Evidence
  MetricReflection EffectiveCompleteness RealizableMap.
Local Open Scope Qc_scope.

Module V3_GenericLift.

Import V3_EvidenceSyntax.
Import V3_Presentation.
Import V3_Evidence.
Import V3_MetricReflection.
Import V3_EffectiveCompleteness.
Import V3_RealizableMap.

Section WithMap.
Variables P G : Presentation.
Variable T : RealizableMap P G.
Variable ERP : EvidenceRegular (P := P).
Variable ECG : EvidenceClosure (P := G).

Definition lift_object (c : EvidenceObject P) : EvidenceObject G :=
  rm_lift_object P G T ERP ECG c.

(** A proof-relevant morphism [(q,W)] goes to
    [(Lambda*q, Theta_T(W))].  The intrinsic target spine bound is below
    the announced target bound by clause 4 plus source slack. *)
Definition lift_morphism {c d : EvidenceObject P}
    (f : EvidenceMorphism c d)
  : EvidenceMorphism (lift_object c) (lift_object d).
Proof.
  refine {| em_q := rm_Lambda T * em_bound f;
            em_spine := rm_theta T (eo_name c) (eo_name d) (em_spine f);
            em_slack := _ |}.
  apply (proj2 (qcleb_iff _ _)).
  eapply Qcle_trans.
  - apply rm_theta_bound.
  - apply qc_mult_le_mono_l.
    + apply rm_Lambda_nonneg.
    + apply em_spine_le_bound.
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

(** Achievable source bounds transport to achievable target bounds. *)
Theorem lift_achievable :
  forall (c d : EvidenceObject P) (q : Qc),
    achievable_bound P c d q ->
    achievable_bound G (lift_object c) (lift_object d) (rm_Lambda T * q).
Proof.
  intros c d q Hq.
  unfold achievable_bound in *; simpl in *.
  apply rm_certified_dist. exact Hq.
Qed.

(** Canonical rational multiplication commutes with the embedding in R. *)
Lemma Qc2R_mult :
  forall p q : Qc, Qc2R (p * q) = (Qc2R p * Qc2R q)%R.
Proof.
  intros p q. unfold Qc2R. rewrite <- Q2R_mult.
  apply Qeq_eqR. apply Qred_correct.
Qed.

(** Theorem 5.2, d_Cert/Lawvere-metric content.

    [is_lawvere_dist] is the repository's exact GLB presentation of
    d_Cert.  The statement below is therefore the paper inequality

       d_G(T_*c,T_*d) <= Lambda_T d_P(c,d)

    without introducing a separate infimum term.

    The proof takes a source achievable bound arbitrarily close to the
    source GLB and transports it.  The epsilon is divided by L+1 rather
    than L, so the proof is uniform at L=0. *)
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

(** Correspondence with v3:

    Thm. 5.2 object map       → V3_RealizableMap.rm_lift_object
    Thm. 5.2 morphism map     → lift_morphism
    strict functor laws       → lift_morphism_id, lift_morphism_comp
    metric Lipschitz content  → lift_lawvere_lipschitz

    Status remains IN-PROGRESS until these theorems compile, coqchk
    passes, and their Print Assumptions reports are committed. *)

End V3_GenericLift.
