(** * RealizableMap.v — certifiably realizable Lipschitz maps (§5)

    Paper reference: Ballús Santacana, "Universal Gluing and Contextual
    Choice: Certificate-Carrying Approximation, Functorial Evidence, and
    Effective Descent", arXiv:2506.22693 v3, Definition 5.1 and
    Theorem 5.2.

    STATUS: IN-PROGRESS (see docs/FORMALIZATION_STATUS.md).

    This module formalizes Definition 5.1 and the evidence-transport
    ingredients used by Theorem 5.2.  The actual generic-lift algorithm,
    including the theorem's printed quantitative budget

        alpha_T(eps) = eps / (3 max(1,Lambda_T)),   eta = eps/3,

    lives in [V3_GenericLift].  Keeping that algorithm out of this record
    module prevents an alternative valid error split from being mistaken
    for the exact quantitative statement of the manuscript.

    Definition 5.1 has FOUR clauses.  Clause 4 (Theta_T) is explicit
    data with strict identity/composition laws.  Clause 1's stored finite
    Lipschitz derivation is separate.  The obsolete fifth
    approximation-transport field remains absent: approximation transport
    is executable and derived below. *)

From Stdlib Require Import Reals QArith Qreals Qcanon Lra Lia.
From UELAT.V3 Require Import EvidenceSyntax Presentation Evidence EffectiveCompleteness.
Local Open Scope Qc_scope.

Module V3_RealizableMap.

Import V3_EvidenceSyntax.
Import V3_Presentation.
Import V3_Evidence.
Import V3_EffectiveCompleteness.

(** ** Definition 5.1 — certifiably realizable Lipschitz map. *)

Record RealizableMap (P G : Presentation) : Type := {
  (* ---- Clause 1: analytic Lipschitz map ---- *)
  rm_T             : F P -> F G;
  rm_Lambda        : Qc;
  rm_Lambda_nonneg : 0 <= rm_Lambda;
  rm_lipschitz     :
    forall x y : F P,
      (distF G (rm_T x) (rm_T y) <= Qc2R rm_Lambda * distF P x y)%R;

  (* ---- Clause 2: name transformer with exact naturality ---- *)
  rm_name    : NameF P -> NameF G;
  rm_name_ok : forall nu : NameF P, deltaF G (rm_name nu) = rm_T (deltaF P nu);

  (* ---- Clause 1 continued: stored finite derivation ----
     It follows the name transformer in record order because its checker
     law mentions transported names. *)
  rm_lip_store : list bool;
  rm_lip_apply :
    list bool -> NameF P -> NameF P -> Qc -> list bool -> list bool;
  rm_lip_apply_ok :
    forall (nu mu : NameF P) (q : Qc) (W : list bool),
      DistLeaf P nu mu q W = true ->
      DistLeaf G (rm_name nu) (rm_name mu) (rm_Lambda * q)
               (rm_lip_apply rm_lip_store nu mu q W) = true;

  (* ---- Clause 3: finite-code realizer with accepted defect evidence ---- *)
  rm_code         : CodeF P -> Qc -> CodeF G;
  rm_code_witness : CodeF P -> Qc -> list bool;
  rm_code_ok :
    forall (p : CodeF P) (eta : Qc),
      0 < eta ->
      AppCheck G (rm_name (iotaF P p)) (rm_code p eta) eta
               (rm_code_witness p eta) = true;

  (* ---- Clause 4: explicit distance-evidence transformer Theta_T ---- *)
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

(** ** Clause-1 stored derivation induces a canonical strict transformer.

    This construction is deliberately separate from the explicit
    clause-4 [rm_theta].  The manuscript permits clause 4 as data; in a
    concrete proof-tree language it is normally induced by the stored
    derivation, but the abstract definition does not identify them. *)

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

(** Rational monotonicity helper used throughout the lift. *)
Lemma qc_mult_le_mono_l :
  forall L a b : Qc, 0 <= L -> a <= b -> L * a <= L * b.
Proof.
  intros L a b HL Hab.
  rewrite (Qcmult_comm L a), (Qcmult_comm L b).
  apply Qcmult_le_compat_r; assumption.
Qed.

(** ** Transport of certified distance using explicit clause 4. *)
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

(** ** Approximation-evidence transport, executable and derived. *)
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

(** Analytic Lipschitz estimate on transported names. *)
Theorem rm_analytic_lipschitz :
  forall nu mu : NameF P,
    (distF G (deltaF G (rm_name T nu)) (deltaF G (rm_name T mu))
     <= Qc2R (rm_Lambda T) * distF P (deltaF P nu) (deltaF P mu))%R.
Proof.
  intros nu mu. rewrite !rm_name_ok. apply rm_lipschitz.
Qed.

End WithMap.

(** ** Correspondence with v3

      Definition 5.1 → [RealizableMap].  The four clauses are represented
      at the manuscript's stated generality:
        clause 1: rm_T, rm_Lambda, rm_Lambda_nonneg, rm_lipschitz,
                  rm_lip_store/rm_lip_apply/rm_lip_apply_ok;
        clause 2: rm_name, rm_name_ok;
        clause 3: rm_code, rm_code_witness, rm_code_ok;
        clause 4: rm_theta, rm_theta_bound, rm_theta_id, rm_theta_comp.

      [rm_stored_theta] separately shows the canonical transformer induced
      by the stored derivation.  It is not silently substituted for the
      explicit fourth clause.

      The obsolete fifth field rm_app_promote remains absent.
      [rm_app_transport_witness]/[rm_app_transport_ok] derive its useful
      computational content from Defs 4.3/5.1 plus the target mixed rule.

      Theorem 5.2 itself, including its EXACT printed error budget, is in
      [V3_GenericLift]. *)

End V3_RealizableMap.
