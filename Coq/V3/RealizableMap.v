(** * RealizableMap.v — certifiably realizable Lipschitz maps (§5)

    Paper reference: Ballús Santacana, "Universal Gluing and Contextual
    Choice: Certificate-Carrying Approximation, Functorial Evidence, and
    Effective Descent", arXiv:2506.22693 v3, Definition 5.1 and
    Theorem 5.2.

    STATUS: IN-PROGRESS (see docs/FORMALIZATION_STATUS.md).

    This revision matches the FOUR conceptual clauses of Def 5.1 and
    begins the actual generic lifting theorem.  Clause 4 (Theta_T) is
    explicit data with strict identity/composition laws.  Clause 1's
    stored finite Lipschitz derivation is separate.  Approximation
    transport is executable and derived, and the object-level target
    certificate system is constructed below using an explicit rational
    error budget. *)

From Stdlib Require Import Reals QArith Qreals Qcanon Lra Lia.
From UELAT.V3 Require Import EvidenceSyntax Presentation Evidence EffectiveCompleteness.
Local Open Scope Qc_scope.

Module V3_RealizableMap.

Import V3_EvidenceSyntax.
Import V3_Presentation.
Import V3_Evidence.
Import V3_EffectiveCompleteness.

Record RealizableMap (P G : Presentation) : Type := {
  rm_T             : F P -> F G;
  rm_Lambda        : Qc;
  rm_Lambda_nonneg : 0 <= rm_Lambda;
  rm_lipschitz     :
    forall x y : F P,
      (distF G (rm_T x) (rm_T y) <= Qc2R rm_Lambda * distF P x y)%R;

  rm_name    : NameF P -> NameF G;
  rm_name_ok : forall nu : NameF P, deltaF G (rm_name nu) = rm_T (deltaF P nu);

  rm_lip_store : list bool;
  rm_lip_apply :
    list bool -> NameF P -> NameF P -> Qc -> list bool -> list bool;
  rm_lip_apply_ok :
    forall (nu mu : NameF P) (q : Qc) (W : list bool),
      DistLeaf P nu mu q W = true ->
      DistLeaf G (rm_name nu) (rm_name mu) (rm_Lambda * q)
               (rm_lip_apply rm_lip_store nu mu q W) = true;

  rm_code         : CodeF P -> Qc -> CodeF G;
  rm_code_witness : CodeF P -> Qc -> list bool;
  rm_code_ok :
    forall (p : CodeF P) (eta : Qc),
      0 < eta ->
      AppCheck G (rm_name (iotaF P p)) (rm_code p eta) eta
               (rm_code_witness p eta) = true;

  rm_theta :
    forall (a b : NameF P),
      PSpine P a b -> PSpine G (rm_name a) (rm_name b);
  rm_theta_bound :
    forall (a b : NameF P) (W : PSpine P a b),
      (sp_bound (rm_theta a b W) <= rm_Lambda * sp_bound W)%Qc;
  rm_theta_id :
    forall a : NameF P,
      rm_theta a a (sp_nil a) = sp_nil (rm_name a);
  rm_theta_comp :
    forall (a b c : NameF P) (W1 : PSpine P a b) (W2 : PSpine P b c),
      rm_theta a c (sp_app W1 W2)
      = sp_app (rm_theta a b W1) (rm_theta b c W2)
}.

Arguments rm_T {_ _} _ _.
Arguments rm_Lambda {_ _} _.
Arguments rm_Lambda_nonneg {_ _} _.
Arguments rm_lipschitz {_ _} _ _ _.
Arguments rm_name {_ _} _ _.
Arguments rm_name_ok {_ _} _ _.
Arguments rm_lip_store {_ _} _.
Arguments rm_lip_apply {_ _} _ _ _ _ _ _.
Arguments rm_lip_apply_ok {_ _} _ {_ _ _ _} _.
Arguments rm_code {_ _} _ _ _.
Arguments rm_code_witness {_ _} _ _ _.
Arguments rm_code_ok {_ _} _ {_ _} _.
Arguments rm_theta {_ _} _ _ _ _.
Arguments rm_theta_bound {_ _} _ {_ _} _.
Arguments rm_theta_id {_ _} _ _.
Arguments rm_theta_comp {_ _} _ {_ _ _} _ _.

Section WithMap.
Variables P G : Presentation.
Variable T : RealizableMap P G.

(** Clause-1 stored derivation induces a canonical strict transformer,
    kept separate from the explicit clause-4 transformer. *)
Definition rm_stored_theta_prim (nu mu : NameF P)
    (s : PrimStep (DistLeaf P) nu mu)
  : PrimStep (DistLeaf G) (rm_name T nu) (rm_name T mu) :=
  mkPrimStep (rm_Lambda T * ps_bound s)
             (rm_lip_apply T (rm_lip_store T) nu mu (ps_bound s) (ps_witness s))
             (rm_lip_apply_ok T (ps_ok s)).

Definition rm_stored_theta (a b : NameF P) (W : PSpine P a b)
  : PSpine G (rm_name T a) (rm_name T b) :=
  sp_transport (rm_name T) rm_stored_theta_prim W.

Theorem rm_stored_theta_id :
  forall a : NameF P,
    rm_stored_theta a a (sp_nil a) = sp_nil (rm_name T a).
Proof. intro a. apply sp_transport_nil. Qed.

Theorem rm_stored_theta_comp :
  forall (a b c : NameF P) (W1 : PSpine P a b) (W2 : PSpine P b c),
    rm_stored_theta a c (sp_app W1 W2)
    = sp_app (rm_stored_theta a b W1) (rm_stored_theta b c W2).
Proof. intros. apply sp_transport_app. Qed.

Lemma rm_stored_theta_prim_scale :
  forall nu mu (s : PrimStep (DistLeaf P) nu mu),
    ps_bound (rm_stored_theta_prim nu mu s) = rm_Lambda T * ps_bound s.
Proof. reflexivity. Qed.

Theorem rm_stored_theta_bound :
  forall (a b : NameF P) (W : PSpine P a b),
    sp_bound (rm_stored_theta a b W) = rm_Lambda T * sp_bound W.
Proof.
  intros a b W. unfold rm_stored_theta.
  apply sp_bound_transport_scale. apply rm_stored_theta_prim_scale.
Qed.

Lemma qc_mult_le_mono_l :
  forall L a b : Qc, 0 <= L -> a <= b -> L * a <= L * b.
Proof.
  intros L a b HL Hab.
  rewrite (Qcmult_comm L a), (Qcmult_comm L b).
  apply Qcmult_le_compat_r; assumption.
Qed.

Lemma qc_zero_lt_one : (0 < 1)%Qc.
Proof. vm_compute. Qed.

Lemma qc_one_lt_two : (1 < 1 + 1)%Qc.
Proof.
  rewrite <- (Qcplus_0_l 1) at 1.
  apply Qcmult_lt_0_le_reg_r with (z := 1); try apply qc_zero_lt_one.
  rewrite !Qcmult_1_r. apply Qclt_le_weak. exact qc_zero_lt_one.
Qed.

Lemma rm_lambda_plus_one_pos : (0 < rm_Lambda T + 1)%Qc.
Proof.
  eapply Qclt_le_trans with (y := 1).
  - exact qc_zero_lt_one.
  - rewrite <- (Qcplus_0_l 1).
    apply Qcplus_le_compat; [apply rm_Lambda_nonneg | apply Qcle_refl].
Qed.

Definition rm_budget_den : Qc := (1 + 1) * (rm_Lambda T + 1).

Lemma rm_budget_den_pos : (0 < rm_budget_den)%Qc.
Proof.
  unfold rm_budget_den.
  assert (Htwo : (0 < 1 + 1)%Qc).
  { eapply Qclt_trans; [exact qc_zero_lt_one | exact qc_one_lt_two]. }
  rewrite <- Qcmult_0_l with (n := rm_Lambda T + 1).
  apply Qcmult_lt_compat_r; [apply rm_lambda_plus_one_pos | exact Htwo].
Qed.

Lemma rm_budget_den_nonzero : rm_budget_den <> 0.
Proof. apply Qclt_not_eq. exact rm_budget_den_pos. Qed.

Lemma qc_inv_pos : forall d : Qc, 0 < d -> 0 < / d.
Proof.
  intros d Hd.
  apply Qcnot_le_lt. intro Hinv.
  pose proof (Qcmult_le_compat_r (/d) 0 d Hinv (Qclt_le_weak Hd)) as Hmul.
  rewrite Qcmult_inv_l in Hmul by (apply Qclt_not_eq; exact Hd).
  rewrite Qcmult_0_l in Hmul.
  exact (Qclt_not_le qc_zero_lt_one Hmul).
Qed.

Definition rm_budget (eps : Qc) : Qc := eps / rm_budget_den.

Lemma rm_budget_pos :
  forall eps : Qc, 0 < eps -> 0 < rm_budget eps.
Proof.
  intros eps Heps. unfold rm_budget, Qcdiv.
  rewrite <- Qcmult_0_l with (n := / rm_budget_den).
  apply Qcmult_lt_compat_r.
  - apply qc_inv_pos. apply rm_budget_den_pos.
  - exact Heps.
Qed.

Lemma rm_lambda_plus_one_lt_den :
  (rm_Lambda T + 1 < rm_budget_den)%Qc.
Proof.
  unfold rm_budget_den.
  rewrite <- Qcmult_1_l with (n := rm_Lambda T + 1).
  rewrite Qcmult_comm with (x := 1 + 1) (y := rm_Lambda T + 1).
  apply Qcmult_lt_compat_r.
  - apply rm_lambda_plus_one_pos.
  - exact qc_one_lt_two.
Qed.

Lemma rm_budget_error_strict :
  forall eps : Qc, 0 < eps ->
    (rm_Lambda T * rm_budget eps + rm_budget eps < eps)%Qc.
Proof.
  intros eps Heps.
  assert (Hb : (0 < rm_budget eps)%Qc) by (apply rm_budget_pos; exact Heps).
  assert (Hmul :
    ((rm_Lambda T + 1) * rm_budget eps < rm_budget_den * rm_budget eps)%Qc).
  { apply Qcmult_lt_compat_r; [exact Hb | apply rm_lambda_plus_one_lt_den]. }
  rewrite Qcmult_plus_distr_l in Hmul.
  rewrite Qcmult_1_l in Hmul.
  unfold rm_budget in Hmul.
  rewrite Qcmult_div_r in Hmul by apply rm_budget_den_nonzero.
  exact Hmul.
Qed.

Theorem rm_certified_dist :
  forall (nu mu : NameF P) (q : Qc),
    certified_dist P nu mu q ->
    certified_dist G (rm_name T nu) (rm_name T mu) (rm_Lambda T * q).
Proof.
  intros nu mu q [W Hle].
  exists (rm_theta T nu mu W).
  eapply Qcle_trans.
  - apply rm_theta_bound.
  - apply qc_mult_le_mono_l; [apply rm_Lambda_nonneg | exact Hle].
Qed.

Variable ERP : EvidenceRegular (P := P).
Variable ECG : EvidenceClosure (P := G).

Definition rm_app_transport_spine
    (nu : NameF P) (p : CodeF P) (r : Qc) (V : list bool)
  : PSpine G (rm_name T nu) (rm_name T (iotaF P p)) :=
  rm_theta T nu (iotaF P p) (er_promote_spine ERP nu p r V).

Lemma rm_app_transport_spine_bound :
  forall (nu : NameF P) (p : CodeF P) (r : Qc) (V : list bool),
    AppCheck P nu p r V = true ->
    (sp_bound (rm_app_transport_spine nu p r V) <= rm_Lambda T * r)%Qc.
Proof.
  intros nu p r V Happ.
  unfold rm_app_transport_spine.
  eapply Qcle_trans.
  - apply rm_theta_bound.
  - apply qc_mult_le_mono_l.
    + apply rm_Lambda_nonneg.
    + apply er_promote_bound. exact Happ.
Qed.

Definition rm_app_transport_witness
    (nu : NameF P) (p : CodeF P) (r eta : Qc) (V : list bool)
  : list bool :=
  ec_mixed_witness ECG
    (rm_name T nu)
    (rm_name T (iotaF P p))
    (rm_code T p eta)
    (rm_Lambda T * r)
    eta
    (rm_app_transport_spine nu p r V)
    (rm_code_witness T p eta).

Theorem rm_app_transport_ok :
  forall (nu : NameF P) (p : CodeF P) (r eta : Qc) (V : list bool),
    0 < eta ->
    AppCheck P nu p r V = true ->
    AppCheck G (rm_name T nu) (rm_code T p eta)
      (rm_Lambda T * r + eta)
      (rm_app_transport_witness nu p r eta V) = true.
Proof.
  intros nu p r eta V Heta Happ.
  unfold rm_app_transport_witness.
  apply ec_mixed_ok.
  - apply rm_app_transport_spine_bound. exact Happ.
  - apply rm_code_ok. exact Heta.
Qed.

Corollary rm_app_transport :
  forall (nu : NameF P) (p : CodeF P) (r eta : Qc) (V : list bool),
    0 < eta ->
    AppCheck P nu p r V = true ->
    exists V',
      AppCheck G (rm_name T nu) (rm_code T p eta)
               (rm_Lambda T * r + eta) V' = true.
Proof.
  intros nu p r eta V Heta Happ.
  exists (rm_app_transport_witness nu p r eta V).
  apply rm_app_transport_ok; assumption.
Qed.

(** ** Theorem 5.2 — object-level generic lift.

    The same budget [b = eps/(2(Lambda+1))] is used for the source
    certificate tolerance and for the finite-code realization defect.
    If the source certificate returns [r < b], the target announced
    error is [Lambda*r+b], which is strictly below eps. *)

Definition rm_lift_run (c : EvidenceObject P) (eps : Qc)
  : CodeF G * Qc * list bool :=
  let b := rm_budget eps in
  let '(p, r, V) := cs_run (eo_system c) b in
  (rm_code T p b,
   rm_Lambda T * r + b,
   rm_app_transport_witness (eo_name c) p r b V).

Definition rm_lift_cert_system (c : EvidenceObject P)
  : CertSystem (rm_name T (eo_name c)).
Proof.
  refine {| cs_run := rm_lift_run c;
            cs_bound_lt := _;
            cs_accept := _ |}.
  - intros eps Heps.
    unfold rm_lift_run.
    set (b := rm_budget eps).
    destruct (cs_run (eo_system c) b) as [[p r] V] eqn:Hrun.
    simpl.
    assert (Hbpos : (0 < b)%Qc) by (unfold b; apply rm_budget_pos; exact Heps).
    pose proof (cs_bound_lt (eo_system c) b Hbpos) as Hsrc.
    rewrite Hrun in Hsrc. simpl in Hsrc.
    destruct Hsrc as [Hr0 Hrlt]. split.
    + apply Qcplus_le_compat.
      * rewrite Qcmult_comm.
        apply Qcmult_le_compat_r; [exact Hr0 | apply rm_Lambda_nonneg].
      * apply Qclt_le_weak. exact Hbpos.
    + eapply Qcle_lt_trans.
      * apply Qcplus_le_compat.
        -- apply qc_mult_le_mono_l; [apply rm_Lambda_nonneg | apply Qclt_le_weak; exact Hrlt].
        -- apply Qcle_refl.
      * unfold b. apply rm_budget_error_strict. exact Heps.
  - intros eps Heps.
    unfold rm_lift_run.
    set (b := rm_budget eps).
    destruct (cs_run (eo_system c) b) as [[p r] V] eqn:Hrun.
    simpl.
    assert (Hbpos : (0 < b)%Qc) by (unfold b; apply rm_budget_pos; exact Heps).
    pose proof (cs_accept (eo_system c) b Hbpos) as Hsrc.
    rewrite Hrun in Hsrc. simpl in Hsrc.
    apply rm_app_transport_ok; assumption.
Defined.

Definition rm_lift_object (c : EvidenceObject P) : EvidenceObject G :=
  {| eo_name := rm_name T (eo_name c);
     eo_system := rm_lift_cert_system c |}.

Theorem rm_analytic_lipschitz :
  forall nu mu : NameF P,
    (distF G (deltaF G (rm_name T nu)) (deltaF G (rm_name T mu))
     <= Qc2R (rm_Lambda T) * distF P (deltaF P nu) (deltaF P mu))%R.
Proof.
  intros nu mu. rewrite !rm_name_ok. apply rm_lipschitz.
Qed.

End WithMap.

(** ** Correspondence with v3

      Def. 5.1 → [RealizableMap]: four clauses at the manuscript's
      stated generality; clause 4 is explicit data.  The obsolete fifth
      approximation-transport hypothesis remains absent.

      Thm. 5.2 → the object-level construction is now
      [rm_lift_cert_system]/[rm_lift_object], using the explicit strict
      budget [rm_budget].  Still missing in this file: the morphism lift,
      strict functor laws, and the Lawvere-metric Lipschitz theorem.
      Status therefore remains IN-PROGRESS until the complete theorem is
      compiled, checked, and assumption-audited. *)

End V3_RealizableMap.
