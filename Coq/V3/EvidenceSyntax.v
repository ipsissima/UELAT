(** * EvidenceSyntax.v — normalized evidence syntax (§2)

    Paper reference: Ballús Santacana, "Universal Gluing and Contextual
    Choice: Certificate-Carrying Approximation, Functorial Evidence, and
    Effective Descent", arXiv:2506.22693 v3, §2 (the paragraph following
    Definition 2.1 on the evidence language and its normal form).

    STATUS: IN-PROGRESS (see docs/FORMALIZATION_STATUS.md).

    ** Why this module exists

    The paper states, immediately after Definition 2.1:

      "Structural proof trees are stored in a fixed normal form in which
       reflexivity is the unit and the triangle-composition spine is
       flattened. Thus the witness composition used below is strictly
       unital and associative, rather than merely associative up to
       syntactic rebracketing."

    That is a mathematical hypothesis of the paper, and it is exactly
    what Definition 5.1's clause on Θ_T needs: Θ_T must preserve
    identity and concatenation ON THE NOSE. Until the normal form is
    represented, "on the nose" cannot even be stated.

    A flattened spine whose unit is reflexivity is a list. So
    [dsp_refl := []], [dsp_comp := app], and "strictly unital and
    associative" becomes [app_nil_l] / [app_nil_r] / [app_assoc] —
    Leibniz equalities, proved below rather than assumed.

    ** Composability is structural, not checked

    A step stores only its TARGET, never its source: the source of a
    step is the target of the step before it, and the source of the
    first step is the spine's declared origin. Consequently a
    non-composable spine — the [a → b] followed by [c → d] with
    [b <> c] that a source/target pair representation would permit — is
    not representable at all. The endpoint of a spine is then COMPUTED
    by [dsp_end], not asserted and not checked.

    This is the cheap half of the endpoint discipline. The remaining
    half — that a spine's computed endpoint is the target the morphism
    claims — is deliberately left to the presentation's own terminating
    checker (see below), which keeps it inside the paper's existing
    "checkers are part of the structure" discipline.

    ** Why not an intrinsically indexed spine?

    An endpoint-indexed inductive [Spine : Name -> Name -> Type] would
    also make non-composable spines untypeable, and its append is
    strictly unital and associative without casts. It was rejected for
    two reasons. First, the endpoint obligation would move into the
    TYPE of an evidence morphism, so morphism equality would carry a
    dependent index and heterogeneous-equality obligations would appear
    in exactly the functor-law proofs this normal form exists to keep
    strict. Second, and decisively, the semantic content the paper
    cares about — is this primitive leaf a valid distance witness? — is
    checker-mediated by Definition 2.1, and dependent syntax would move
    part of that into typing. Storing only targets gets the structural
    guarantee at no such cost.

    ** Why not add decidable equality on names?

    The alternative way to close the endpoint gap is a boolean
    [spine_check] with an abstract [name_eqb] field on the
    presentation. That would work, but it STRENGTHENS Definition 2.1:
    the paper requires [Name_F] to be a set with a surjection onto the
    represented domain, and nowhere requires its equality to be
    decidable. Rather than add a hypothesis the paper does not state,
    the endpoint comparison is left to [DistCheck] itself, which
    Definition 2.1 already grants as a terminating boolean procedure
    taking BOTH names as input. Section [ReferenceChecker] below offers
    a ready-made implementation for concrete presentations that do have
    decidable name equality — as an available helper, not an imposed
    field.

    ** Why bounds live in [Qc] and not [Q]

    With plain [Q], [(q1 + q2) + q3] and [q1 + (q2 + q3)] are distinct
    terms, equal only under [Qeq]. Strict associativity of SPINES would
    hold while strict associativity of MORPHISMS silently degraded to
    "up to Qeq" — weakening exactly the clause Definition 5.1 depends
    on. [Qcanon.Qc] is canonical-form rational arithmetic, for which
    stdlib proves the unit and associativity laws as Leibniz
    equalities. Section [QcStrictness] re-proves the three facts relied
    on, so CI fails loudly here rather than silently downstream. *)

From Stdlib Require Import List QArith Qcanon Bool Eqdep_dec.
Import ListNotations.
Local Open Scope Qc_scope.

Module V3_EvidenceSyntax.

(** ** The [Qc] strictness facts this design rests on. *)

Section QcStrictness.

Lemma qc_add_0_l : forall q : Qc, 0 + q = q.
Proof. intro q. apply Qcplus_0_l. Qed.

Lemma qc_add_0_r : forall q : Qc, q + 0 = q.
Proof. intro q. rewrite Qcplus_comm. apply Qcplus_0_l. Qed.

Lemma qc_add_assoc : forall a b c : Qc, a + (b + c) = a + b + c.
Proof. intros a b c. apply Qcplus_assoc. Qed.

End QcStrictness.

(** ** Elementary step of a normalized distance derivation.

    Only the TARGET is stored. The source is positional: it is the
    previous step's target, or the spine's origin for the first step.
    The leaf stays opaque ([list bool]) on purpose — the paper's normal
    form constrains the structural spine, not the internal encoding of
    a primitive verification record. *)

Record DistStep (Name : Type) : Type := mkDistStep {
  ds_tgt   : Name;
  ds_bound : Qc;
  ds_leaf  : list bool
}.

Arguments mkDistStep {_} _ _ _.
Arguments ds_tgt   {_} _.
Arguments ds_bound {_} _.
Arguments ds_leaf  {_} _.

(** ** Normalized derivation = flattened spine. *)

Definition DistSpine (Name : Type) : Type := list (DistStep Name).

Definition dsp_refl {Name : Type} : DistSpine Name := [].

Definition dsp_comp {Name : Type} (W1 W2 : DistSpine Name) : DistSpine Name :=
  W1 ++ W2.

(** ** The paper's "strictly unital and associative", as Leibniz equalities. *)

Lemma dsp_comp_refl_l :
  forall (Name : Type) (W : DistSpine Name), dsp_comp dsp_refl W = W.
Proof. intros Name W. reflexivity. Qed.

Lemma dsp_comp_refl_r :
  forall (Name : Type) (W : DistSpine Name), dsp_comp W dsp_refl = W.
Proof. intros Name W. unfold dsp_comp, dsp_refl. apply app_nil_r. Qed.

Lemma dsp_comp_assoc :
  forall (Name : Type) (W1 W2 W3 : DistSpine Name),
    dsp_comp (dsp_comp W1 W2) W3 = dsp_comp W1 (dsp_comp W2 W3).
Proof.
  intros Name W1 W2 W3. unfold dsp_comp. symmetry. apply app_assoc.
Qed.

(** ** Computed endpoint.

    [dsp_end nu W] is the name a spine starting at [nu] arrives at.
    Because sources are positional, this is a total computation with no
    well-formedness side condition. *)

Fixpoint dsp_end {Name : Type} (nu : Name) (W : DistSpine Name) : Name :=
  match W with
  | []      => nu
  | s :: W' => dsp_end (ds_tgt s) W'
  end.

Lemma dsp_end_refl :
  forall (Name : Type) (nu : Name), dsp_end nu dsp_refl = nu.
Proof. reflexivity. Qed.

Lemma dsp_end_comp :
  forall (Name : Type) (nu : Name) (W1 W2 : DistSpine Name),
    dsp_end nu (dsp_comp W1 W2) = dsp_end (dsp_end nu W1) W2.
Proof.
  intros Name nu W1. revert nu.
  induction W1 as [|s W1 IH]; intros nu W2; simpl; [reflexivity|].
  apply IH.
Qed.

(** ** Announced bound of a normalized derivation. *)

Definition dsp_bound {Name : Type} (W : DistSpine Name) : Qc :=
  fold_right (fun s acc => ds_bound s + acc) 0 W.

Lemma dsp_bound_refl :
  forall (Name : Type), dsp_bound (@dsp_refl Name) = 0.
Proof. intro Name. reflexivity. Qed.

(** Additivity under composition — a LEIBNIZ equality, which is what
    makes strict morphism laws possible downstream. *)

Lemma dsp_bound_comp :
  forall (Name : Type) (W1 W2 : DistSpine Name),
    dsp_bound (dsp_comp W1 W2) = dsp_bound W1 + dsp_bound W2.
Proof.
  intros Name W1 W2. unfold dsp_comp.
  induction W1 as [|s W1 IH]; simpl.
  - symmetry. apply qc_add_0_l.
  - rewrite IH. apply qc_add_assoc.
Qed.

(** ** Transport of a normalized derivation.

    This is the shape Θ_T takes: a step-local transformation applied
    pointwise. [map] makes the two strict laws Θ_T must satisfy —
    preservation of the identity and of concatenation — into [map_nil]
    (definitional) and [map_app] (a Leibniz equality). Nothing is
    assumed of the transformer beyond being step-local, which is
    precisely the paper's "uniform" requirement. *)

Definition dsp_transport {A B : Type}
    (step : DistStep A -> DistStep B) (W : DistSpine A) : DistSpine B :=
  map step W.

Lemma dsp_transport_refl :
  forall (A B : Type) (step : DistStep A -> DistStep B),
    dsp_transport step dsp_refl = dsp_refl.
Proof. intros. reflexivity. Qed.

Lemma dsp_transport_comp :
  forall (A B : Type) (step : DistStep A -> DistStep B) (W1 W2 : DistSpine A),
    dsp_transport step (dsp_comp W1 W2)
    = dsp_comp (dsp_transport step W1) (dsp_transport step W2).
Proof.
  intros A B step W1 W2. unfold dsp_transport, dsp_comp. apply map_app.
Qed.

(** Endpoints commute with transport, provided the step transformation
    moves targets along a map on names. This is what makes a
    transported spine run from [g nu] to [g mu], i.e. exactly what
    Θ_T must deliver for [T^#]. *)

Lemma dsp_end_transport :
  forall (A B : Type) (g : A -> B) (step : DistStep A -> DistStep B),
    (forall s, ds_tgt (step s) = g (ds_tgt s)) ->
    forall (nu : A) (W : DistSpine A),
      dsp_end (g nu) (dsp_transport step W) = g (dsp_end nu W).
Proof.
  intros A B g step Hstep nu W. revert nu.
  induction W as [|s W IH]; intros nu; simpl; [reflexivity|].
  rewrite Hstep. apply IH.
Qed.

(** ** A reference spine checker.

    Offered for concrete presentations that do have decidable name
    equality. It is NOT a field of any interface here: Definition 2.1
    does not require decidable equality on names, so imposing it would
    strengthen the paper. A presentation may use this, or supply its
    own [DistCheck] by any other terminating means.

    Acceptance asserts: every primitive leaf is admissible according to
    the supplied leaf checker (with the correct positional source), the
    computed endpoint is the declared target, and the announced bound
    is [dsp_bound]. Adjacency needs no clause — it is structural. *)

Section ReferenceChecker.
Context {Name : Type}.
Variable name_eqb : Name -> Name -> bool.
Variable leaf_ok  : Name -> Name -> Qc -> list bool -> bool.

Fixpoint leaves_ok (nu : Name) (W : DistSpine Name) : bool :=
  match W with
  | []      => true
  | s :: W' => leaf_ok nu (ds_tgt s) (ds_bound s) (ds_leaf s)
               && leaves_ok (ds_tgt s) W'
  end.

Definition spine_check (nu mu : Name) (q : Qc) (W : DistSpine Name) : bool :=
  leaves_ok nu W
  && name_eqb (dsp_end nu W) mu
  && Qc_eq_bool (dsp_bound W) q.

(** The empty spine is accepted at bound 0 between a name and itself,
    provided the supplied equality is reflexive on the nose. This is
    the reflexivity rule of the evidence language, discharged rather
    than postulated. *)

Lemma spine_check_refl :
  (forall a, name_eqb a a = true) ->
  forall nu : Name, spine_check nu nu 0 dsp_refl = true.
Proof.
  intros Hrefl nu. unfold spine_check. simpl.
  rewrite Hrefl. simpl.
  unfold Qc_eq_bool. destruct (Qc_eq_dec 0 0) as [_|Hne]; [reflexivity|].
  exfalso. apply Hne. reflexivity.
Qed.

(** Leaf admissibility is itself compositional along the spine. *)

Lemma leaves_ok_comp :
  forall (nu : Name) (W1 W2 : DistSpine Name),
    leaves_ok nu (dsp_comp W1 W2) = leaves_ok nu W1 && leaves_ok (dsp_end nu W1) W2.
Proof.
  intros nu W1. revert nu.
  induction W1 as [|s W1 IH]; intros nu W2; simpl; [reflexivity|].
  rewrite IH. apply andb_assoc.
Qed.

End ReferenceChecker.

(** ** Proof-component irrelevance for checker acceptance.

    A morphism of the evidence category bundles its normalized spine
    with a proof that the checker accepts it. To conclude equality of
    two morphisms from equality of spine and bound, the proof
    components must be equal too. Checker acceptance is an equality of
    booleans, so this follows from decidable equality on [bool] via
    Hedberg — NO axiom is required, in particular not
    [proof_irrelevance] and not [UIP] as an assumption. *)

Lemma checker_proof_irrelevant :
  forall (b : bool) (p q : b = true), p = q.
Proof. intros b p q. apply (UIP_dec Bool.bool_dec). Qed.

End V3_EvidenceSyntax.

(** ** Correspondence with v3

      Paper text:
        §2, the normalized-proof-tree convention following Def 2.1
        ("reflexivity is the unit and the triangle-composition spine is
         flattened ... strictly unital and associative").
      Rocq definitions:
        V3_EvidenceSyntax.DistSpine, dsp_refl, dsp_comp, dsp_end.
      Rocq theorems:
        dsp_comp_refl_l, dsp_comp_refl_r, dsp_comp_assoc
          — strict unitality and associativity, as Leibniz equalities;
        dsp_bound_refl, dsp_bound_comp
          — the announced bound is additive, also Leibniz, because
            bounds are canonical [Qc];
        dsp_end_refl, dsp_end_comp
          — endpoints compose;
        dsp_transport_refl, dsp_transport_comp, dsp_end_transport
          — the two strict laws Θ_T must satisfy, plus endpoint
            naturality.
      Correspondence: DEFINITION-EXACT for the normal form, with the
      strictness claims proved rather than assumed.

    Deliberately NOT claimed here:

      - SYMMETRY of normalized spines. With positional sources, the
        symmetry rule must re-thread the origin to recompute each
        reversed step's target, which is materially more involved than
        the [rev ∘ map] of a source/target representation. It is not on
        the critical path for the strict category laws or for Def 5.1's
        Θ_T clause, so it remains an abstract witness constructor in
        [V3_Evidence.EvidenceClosure] for now rather than being given a
        normalized implementation. This is a gap, and is recorded as
        one; it is not a claim.
      - Anything about [AppCheck]. Approximation evidence is not
        composed along a spine, so it needs no normal form of this
        kind. The mixed rule turning a distance derivation plus an
        approximation certificate into an approximation certificate is
        a separate constructor, added when Def 5.1 needs it.
      - Any connection to a concrete presentation. Wiring
        [V3_Presentation.Presentation] to consume [DistSpine] is the
        next commit. *)
