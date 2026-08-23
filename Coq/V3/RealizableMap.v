(** * RealizableMap.v — certifiably realizable Lipschitz maps (§5)

    Paper reference: Ballús Santacana, "Universal Gluing and Contextual
    Choice: Certificate-Carrying Approximation, Functorial Evidence, and
    Effective Descent", arXiv:2506.22693 v3, Definition 5.1 and
    Theorem 5.2.

    STATUS: IN-PROGRESS (see docs/FORMALIZATION_STATUS.md).

    The extra fifth field [rm_app_promote] from the old proxy remains
    removed. Approximation transport is now not only existentially
    provable but EXECUTABLE: [rm_app_transport_witness] computes the
    finite target AppCheck witness and [rm_app_transport_ok] proves it
    accepted. This is the form required to build Theorem 5.2's target
    [CertSystem.cs_run]. *)

From Stdlib Require Import Reals QArith Qreals Qcanon Lra Lia.
From UELAT.V3 Require Import EvidenceSyntax Presentation Evidence EffectiveCompleteness.
Local Open Scope Qc_scope.

Module V3_RealizableMap.

Import V3_EvidenceSyntax.
Import V3_Presentation.
Import V3_Evidence.
Import V3_EffectiveCompleteness.

(** ** Definition 5.1 — certifiably realizable Lipschitz map.

    NOTE: clause 4 is still DERIVED below from the stored Lipschitz
    derivation. This is intentionally still marked IN-PROGRESS: before
    declaring Def 5.1 definition-exact we will restore clause 4 as
    explicit data, while retaining the derived construction as a
    canonical constructor. *)

Record RealizableMap (P G : Presentation) : Type := {

  (* ---- Clause 1: analytic Lipschitz map with stored derivation ---- *)
  rm_T             : F P -> F G;
  rm_Lambda        : Qc;
  rm_Lambda_nonneg : 0 <= rm_Lambda;
  rm_lipschitz     :
    forall x y : F P,
      (distF G (rm_T x) (rm_T y) <= Qc2R rm_Lambda * distF P x y)%R;

  (* ---- Clause 2: name transformer with naturality ---- *)
  rm_name    : NameF P -> NameF G;
  rm_name_ok : forall nu : NameF P, deltaF G (rm_name nu) = rm_T (deltaF P nu);

  (* ---- Clause 1 continued: stored finite derivation ---- *)
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
               (rm_code_witness p eta) = true
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

Section WithMap.
Variables P G : Presentation.
Variable T : RealizableMap P G.

(** ** Clause 4, currently derived: primitive evidence transformer. *)

Definition rm_theta_prim (nu mu : NameF P)
    (s : PrimStep (DistLeaf P) nu mu)
  : PrimStep (DistLeaf G) (rm_name T nu) (rm_name T mu) :=
  mkPrimStep (rm_Lambda T * ps_bound s)
             (rm_lip_apply T (rm_lip_store T) nu mu (ps_bound s) (ps_witness s))
             (rm_lip_apply_ok T (ps_ok s)).

Lemma rm_theta_prim_scale :
  forall nu mu (s : PrimStep (DistLeaf P) nu mu),
    ps_bound (rm_theta_prim nu mu s) = rm_Lambda T * ps_bound s.
Proof. reflexivity. Qed.

Definition rm_theta (a b : NameF P) (W : PSpine P a b)
  : PSpine G (rm_name T a) (rm_name T b) :=
  sp_transport (rm_name T) rm_theta_prim W.

Theorem rm_theta_id :
  forall a : NameF P, rm_theta a a (sp_nil a) = sp_nil (rm_name T a).
Proof. intro a. apply sp_transport_nil. Qed.

Theorem rm_theta_comp :
  forall (a b c : NameF P) (W1 : PSpine P a b) (W2 : PSpine P b c),
    rm_theta a c (sp_app W1 W2)
    = sp_app (rm_theta a b W1) (rm_theta b c W2).
Proof. intros. apply sp_transport_app. Qed.

Theorem rm_theta_bound :
  forall (a b : NameF P) (W : PSpine P a b),
    sp_bound (rm_theta a b W) = rm_Lambda T * sp_bound W.
Proof.
  intros a b W. unfold rm_theta.
  apply sp_bound_transport_scale. apply rm_theta_prim_scale.
Qed.

(** ** Transport of certified distance. *)

Lemma qc_mult_le_mono_l :
  forall L a b : Qc, 0 <= L -> a <= b -> L * a <= L * b.
Proof.
  intros L a b HL Hab.
  rewrite (Qcmult_comm L a), (Qcmult_comm L b).
  apply Qcmult_le_compat_r; assumption.
Qed.

Theorem rm_certified_dist :
  forall (nu mu : NameF P) (q : Qc),
    certified_dist P nu mu q ->
    certified_dist G (rm_name T nu) (rm_name T mu) (rm_Lambda T * q).
Proof.
  intros nu mu q [W Hle].
  exists (rm_theta nu mu W). rewrite rm_theta_bound.
  apply qc_mult_le_mono_l; [apply rm_Lambda_nonneg | exact Hle].
Qed.

(** ** Approximation-evidence transport, executable and derived.

    Earlier scaffolding returned [exists V'] in Prop. That theorem is
    useful logically but cannot define a target certificate procedure.
    The following definition computes the witness itself from the
    witness-producing EvidenceRegular and EvidenceClosure interfaces. *)

Variable ERP : EvidenceRegular (P := P).
Variable ECG : EvidenceClosure (P := G).

Definition rm_app_transport_spine
    (nu : NameF P) (p : CodeF P) (r : Qc) (V : list bool)
  : PSpine G (rm_name T nu) (rm_name T (iotaF P p)) :=
  rm_theta nu (iotaF P p) (er_promote_spine ERP nu p r V).

Lemma rm_app_transport_spine_bound :
  forall (nu : NameF P) (p : CodeF P) (r : Qc) (V : list bool),
    AppCheck P nu p r V = true ->
    (sp_bound (rm_app_transport_spine nu p r V) <= rm_Lambda T * r)%Qc.
Proof.
  intros nu p r V Happ.
  unfold rm_app_transport_spine. rewrite rm_theta_bound.
  apply qc_mult_le_mono_l.
  - apply rm_Lambda_nonneg.
  - apply er_promote_bound. exact Happ.
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

(** Existential presentation retained as a corollary for logical users. *)

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

(** ** Analytic Lipschitz estimate on transported names. *)

Theorem rm_analytic_lipschitz :
  forall nu mu : NameF P,
    (distF G (deltaF G (rm_name T nu)) (deltaF G (rm_name T mu))
     <= Qc2R (rm_Lambda T) * distF P (deltaF P nu) (deltaF P mu))%R.
Proof.
  intros nu mu. rewrite !rm_name_ok. apply rm_lipschitz.
Qed.

End WithMap.

(** ** Correspondence with v3

      Paper definition:
        Definition 5.1 (Certifiably realizable Lipschitz map).
      Rocq definition:
        V3_RealizableMap.RealizableMap.
      Correspondence: IN-PROGRESS. Clauses 1--3 are represented; the
      current [rm_theta] gives a canonical clause-4 transformer derived
      from the stored Lipschitz derivation, but the manuscript permits
      clause 4 as explicit data. A following commit will restore that
      literal four-clause interface and keep this derived transformer as
      a constructor theorem rather than silently strengthening Def 5.1.

      Paper theorem:
        Theorem 5.2 (Generic lifting) — evidence-transport content.
      Rocq content currently includes:
        rm_theta_id, rm_theta_comp,
        rm_theta_bound, rm_certified_dist,
        rm_app_transport_witness / rm_app_transport_ok,
        rm_analytic_lipschitz.
      The important new fact is that approximation transport is now
      executable: it computes the finite target certificate witness,
      rather than merely proving an existential in Prop. This removes a
      genuine obstruction to constructing the object-level T_*.

      Still missing from Thm 5.2: the target EvidenceObject / CertSystem,
      the morphism-level lift, strict functor laws, and the
      d_Cert/Lawvere-metric Lipschitz statement. *)

End V3_RealizableMap.
