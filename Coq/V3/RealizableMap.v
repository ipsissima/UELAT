(** * RealizableMap.v — certifiably realizable Lipschitz maps (§5)

    Paper reference: Ballús Santacana, "Universal Gluing and Contextual
    Choice: Certificate-Carrying Approximation, Functorial Evidence, and
    Effective Descent", arXiv:2506.22693 v3, Definition 5.1 and
    Theorem 5.2.

    STATUS: IN-PROGRESS (see docs/FORMALIZATION_STATUS.md).

    This module formalizes Definition 5.1 together with the evidence
    operation that Definition 2.1 explicitly requires: application of a
    stored Lipschitz estimate to a tagged source proof.

    That distinction is important.  A source approximation certificate

        AppCheck_P(nu,p,r,V)

    must be transformable directly into target distance evidence between
    T^#nu and T^#(iota p), with bound Lambda_T*r.  The generic lifting
    theorem therefore does NOT require the later Definition 4.3
    evidence-regularity hypothesis merely to promote AppCheck to
    DistCheck.  Earlier Rocq scaffolding did exactly that; this revision
    removes the spurious hypothesis and follows the manuscript's proof.

    Definition 5.1 still has FOUR clauses.  Clause 4 (Theta_T) is
    explicit distance-evidence data with strict identity/composition
    laws.  Clause 1's stored derivation is kept distinct: its application
    to approximation evidence is the Def. 2.1 stored-Lipschitz rule.
    The obsolete fifth approximation-transport assumption remains absent. *)

From Stdlib Require Import Reals QArith Qreals Qcanon Lra Lia.
From UELAT.V3 Require Import EvidenceSyntax Presentation Evidence.
Local Open Scope Qc_scope.

Module V3_RealizableMap.

Import V3_EvidenceSyntax.
Import V3_Presentation.
Import V3_Evidence.

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
  rm_name_ok : forall nu : NameF P,
      deltaF G (rm_name nu) = rm_T (deltaF P nu);

  (* ---- Clause 1 continued: finite stored Lipschitz derivation ----

     Definition 2.1 allows a target checker to invoke the source checker
     on a tagged subproof and apply a stored Lipschitz estimate.  At the
     abstract Rocq interface this is represented computationally: given
     the stored derivation plus source approximation data, manufacture a
     normalized target distance proof tree.  Sound use of that tree is
     conditional on source AppCheck acceptance. *)
  rm_lip_store : list bool;
  rm_lip_apply :
    list bool ->
    forall (nu : NameF P) (p : CodeF P) (q : Qc), list bool ->
      PSpine G (rm_name nu) (rm_name (iotaF P p));
  rm_lip_apply_ok :
    forall (nu : NameF P) (p : CodeF P) (q : Qc) (V : list bool),
      AppCheck P nu p q V = true ->
      (sp_bound (rm_lip_apply rm_lip_store nu p q V)
       <= rm_Lambda * q)%Qc;

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

Lemma qc_mult_le_mono_l :
  forall L a b : Qc, 0 <= L -> a <= b -> L * a <= L * b.
Proof.
  intros L a b HL Hab.
  rewrite (Qcmult_comm L a), (Qcmult_comm L b).
  apply Qcmult_le_compat_r; assumption.
Qed.

(** ** Clause 4 transports already-distance-certified evidence. *)
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

(** ** Stored-Lipschitz application to approximation evidence.

    This is the source-to-target proof transformation used in the first
    line of the Theorem 5.2 certificate construction.  It is NOT
    Definition 4.3 evidence regularity and requires no promotion of
    AppCheck to a source DistCheck witness. *)
Definition rm_app_transport_spine
    (nu : NameF P) (p : CodeF P) (r : Qc) (V : list bool)
  : PSpine G (rm_name T nu) (rm_name T (iotaF P p)) :=
  rm_lip_apply T (rm_lip_store T) nu p r V.

Lemma rm_app_transport_spine_bound :
  forall (nu : NameF P) (p : CodeF P) (r : Qc) (V : list bool),
    AppCheck P nu p r V = true ->
    (sp_bound (rm_app_transport_spine nu p r V)
     <= rm_Lambda T * r)%Qc.
Proof.
  intros nu p r V Happ.
  unfold rm_app_transport_spine.
  apply rm_lip_apply_ok. exact Happ.
Qed.

(** Target evidence closure is the other Def. 2.1 ingredient: compose
    the transformed distance proof with the code-realizer AppCheck proof
    by one triangle/mixed step. *)
Variable ECG : EvidenceClosure (P := G).

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

Theorem rm_analytic_lipschitz :
  forall nu mu : NameF P,
    (distF G (deltaF G (rm_name T nu)) (deltaF G (rm_name T mu))
     <= Qc2R (rm_Lambda T) * distF P (deltaF P nu) (deltaF P mu))%R.
Proof.
  intros nu mu. rewrite !rm_name_ok. apply rm_lipschitz.
Qed.

End WithMap.

(** ** Correspondence with v3

    Definition 5.1:
      clause 1 — analytic map, rational Lambda>=0, analytic estimate,
                 finite stored derivation;
      clause 2 — rm_name/rm_name_ok;
      clause 3 — rm_code/rm_code_witness/rm_code_ok;
      clause 4 — rm_theta/rm_theta_bound/rm_theta_id/rm_theta_comp.

    Definition 2.1's evidence-language rule "application of a stored
    Lipschitz estimate" is exposed by rm_lip_apply/rm_lip_apply_ok: a
    source AppCheck proof is a tagged finite subproof from which the
    target distance tree is manufactured.  Consequently Theorem 5.2
    does not require Definition 4.3 evidence regularity.

    [rm_app_transport_witness]/[rm_app_transport_ok] then add the target
    code-realizer witness and one mixed/triangle step, exactly as in the
    manuscript proof.  No fifth Def. 5.1 hypothesis is introduced. *)

End V3_RealizableMap.
