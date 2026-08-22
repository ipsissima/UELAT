(** * RealizableMap.v — certifiably realizable Lipschitz maps (§5)

    Paper reference: Ballús Santacana, "Universal Gluing and Contextual
    Choice: Certificate-Carrying Approximation, Functorial Evidence, and
    Effective Descent", arXiv:2506.22693 v3, Definition 5.1 and
    Theorem 5.2.

    STATUS: IN-PROGRESS (see docs/FORMALIZATION_STATUS.md).

    ** This record now has Definition 5.1's FOUR clauses

    The previous revision was an explicitly-flagged proxy with five
    components. What changed:

    - Clause 1 now carries a STORED FINITE DERIVATION of the Lipschitz
      estimate, not only the analytic Prop. Both are present and kept
      distinct: [rm_lipschitz] is the analytic content, while
      [rm_lip_store] together with [rm_lip_apply] / [rm_lip_apply_ok]
      is the finite evidence-language object that actually manufactures
      target leaf evidence.

    - Clause 4's Θ_T is no longer a field. It is DEFINED
      ([rm_theta_prim], [rm_theta]) from the stored derivation, so the
      evidence transformation genuinely arises from that derivation
      rather than being an independent assumption that happens to agree
      with it. Its two strict laws are then THEOREMS
      ([rm_theta_id], [rm_theta_comp]), inherited from
      [sp_transport_nil] / [sp_transport_app].

    - The extra fifth field [rm_app_promote] is REMOVED. Approximation
      evidence transport is derived instead, as
      [rm_app_transport], from: evidence regularity on the source, the
      derived Θ_T, the finite-code realizer, and the §2 mixed rule.
      That derivation is the content of [rm_app_transport] below and is
      the theorem showing the fifth field was unnecessary.

    ** One honest caveat about "stored derivation"

    At this level of abstraction, carrying a finite store plus a
    uniform application procedure is interderivable with carrying the
    application procedure alone — one can always curry. The store
    becomes mathematically forceful only for a CONCRETE evidence
    language, where a presentation must exhibit an actual finite
    derivation object. What is formalized here is the interface shape
    the paper describes; it is recorded as such rather than claimed to
    be stronger than it is. *)

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

  (* ---- Clause 1 (continued): the stored finite derivation, and the
         uniform procedure that applies it to a primitive step ---- *)
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

(** ** Clause 4, DERIVED: the primitive evidence transformer.

    Note it receives BOTH endpoint names [nu] and [mu] — this is the
    general Θ_T(ν, μ, r, W) of Def 5.1, not a source-blind special
    case. Its witness is produced by applying the STORED derivation. *)

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

(** Θ_T on whole normalized derivations. *)

Definition rm_theta (a b : NameF P) (W : PSpine P a b)
  : PSpine G (rm_name T a) (rm_name T b) :=
  sp_transport (rm_name T) rm_theta_prim W.

(** ** The two STRICT laws Def 5.1 clause 4 demands — as theorems. *)

Theorem rm_theta_id :
  forall a : NameF P, rm_theta a a (sp_nil a) = sp_nil (rm_name T a).
Proof. intro a. apply sp_transport_nil. Qed.

Theorem rm_theta_comp :
  forall (a b c : NameF P) (W1 : PSpine P a b) (W2 : PSpine P b c),
    rm_theta a c (sp_app W1 W2)
    = sp_app (rm_theta a b W1) (rm_theta b c W2).
Proof. intros. apply sp_transport_app. Qed.

(** Bound scaling on whole derivations. *)

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

(** ** Approximation-evidence transport, DERIVED.

    This is the theorem establishing that the old fifth field
    [rm_app_promote] was unnecessary. Given accepted source
    approximation evidence for [(nu, p, r)], we produce accepted TARGET
    approximation evidence for [(T^# nu, tau_T(p, eta), Lambda*r + eta)]
    out of:

      - evidence regularity on the source (promote AppCheck to a
        certified distance against the canonical name of [p]);
      - the derived Θ_T (transport that distance, scaling by Lambda);
      - the finite-code realizer (clause 3) at defect [eta];
      - the §2 mixed rule on the target.

    Nothing outside Def 5.1's clauses and Def 2.1's stated evidence
    language is used. *)

Variable ERP : EvidenceRegular P.
Variable ECG : EvidenceClosure (P := G).

Theorem rm_app_transport :
  forall (nu : NameF P) (p : CodeF P) (r eta : Qc) (V : list bool),
    0 < eta ->
    AppCheck P nu p r V = true ->
    exists V',
      AppCheck G (rm_name T nu) (rm_code T p eta)
               (rm_Lambda T * r + eta) V' = true.
Proof.
  intros nu p r eta V Heta Happ.
  (* 1. source approximation evidence promotes to certified distance *)
  pose proof (er_promote P ERP nu p r V Happ) as Hsrc.
  (* 2. transport it along Theta_T *)
  pose proof (rm_certified_dist nu (iotaF P p) r Hsrc) as Htgt.
  (* 3. the code realizer supplies target approximation evidence
        for the transported canonical name *)
  pose proof (rm_code_ok T p eta Heta) as Hcode.
  (* 4. the mixed rule composes them, adding the bounds *)
  eapply (ec_mixed ECG). exact Htgt. exact Hcode.
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
      Correspondence: the record now has Def 5.1's FOUR clauses, with
      clause 4 derived rather than assumed:
        clause 1: rm_T, rm_Lambda, rm_Lambda_nonneg, rm_lipschitz
                  (analytic), plus rm_lip_store / rm_lip_apply /
                  rm_lip_apply_ok (the stored finite derivation and the
                  uniform procedure applying it);
        clause 2: rm_name, rm_name_ok;
        clause 3: rm_code, rm_code_witness, rm_code_ok;
        clause 4: rm_theta_prim / rm_theta — DEFINED from the stored
                  derivation, with the strict laws rm_theta_id and
                  rm_theta_comp proved.
      The previous revision's extra field rm_app_promote is gone; see
      rm_app_transport. Status remains IN-PROGRESS because the
      object-level and morphism-level T_* of Thm 5.2 are not yet
      constructed — that is the next commit, not a hidden gap.

      Paper theorem:
        Theorem 5.2 (Generic lifting) — evidence-transport content.
      Rocq theorems:
        rm_theta_id, rm_theta_comp (strict Θ_T laws),
        rm_theta_bound, rm_certified_dist (Λ_T scaling),
        rm_app_transport (approximation transport, DERIVED),
        rm_analytic_lipschitz.
      Correspondence: CHECKED-RESTRICTED. What is NOT yet here:
      the functor T_* on evidence objects and morphisms, the strict
      functor laws for it, and the d_Cert-level Lipschitz statement.

    A note on hypotheses. [rm_app_transport] takes an
    [EvidenceRegular P] and an [EvidenceClosure G] as Section
    variables. Neither is an addition to Def 5.1: evidence regularity
    is Def 4.3, and the closure record holds only rules Def 2.1's §2
    already requires of the evidence language (symmetry, weakening, the
    mixed rule). Reflexivity and the triangle rule are NOT among them —
    those are proved in Presentation.v. *)

End V3_RealizableMap.
