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

    That sentence is a *mathematical hypothesis of the paper*, and it is
    exactly what Definition 5.1's clause on Θ_T needs: Θ_T is required to
    preserve identity and concatenation ON THE NOSE. Until the normal
    form is represented, "on the nose" cannot even be stated, and the
    earlier V3 skeleton had to defer the category laws.

    This module represents the normal form directly:

      - a normalized distance derivation is a FLATTENED SPINE, i.e. a
        list of elementary steps;
      - reflexivity is the empty spine, which is the unit of append;
      - triangle composition is [app], which is strictly associative.

    So "strictly unital and associative" becomes [app_nil_l],
    [app_nil_r], [app_assoc] — Leibniz equalities, not setoid ones.
    Nothing here is invented to make the proof convenient: the list
    structure IS the paper's flattened spine.

    ** Why bounds live in [Qc] and not [Q]

    A normalized derivation carries a rational bound. If bounds were
    plain [Q], then [(q1 + q2) + q3] and [q1 + (q2 + q3)] would be
    distinct terms — equal only under [Qeq] — and strict associativity
    of *morphisms* would be false even though strict associativity of
    *spines* holds. Silently retreating to "associative up to Qeq"
    would weaken exactly the clause Definition 5.1 relies on.

    [Qcanon.Qc] is the standard fix: rationals in canonical form, for
    which stdlib proves associativity and unit laws as Leibniz
    equalities. Section [QcStrictness] below re-proves the three facts
    this design depends on, so that CI fails loudly here rather than
    silently downstream if the ambient stdlib ever changes.

    ** What this module does NOT do

    It does not touch [V3_Presentation.Presentation] or
    [V3_Evidence]. Rewiring those to consume normalized spines is the
    next commit; keeping this module standalone makes the foundation
    reviewable and independently checkable. *)

From Stdlib Require Import List QArith Qcanon Bool Eqdep_dec.
Import ListNotations.
Local Open Scope Qc_scope.

Module V3_EvidenceSyntax.

(** ** The [Qc] strictness facts this design rests on.

    These are restatements of stdlib lemmas. They exist so that the
    Leibniz-ness of the rational arithmetic is asserted where it is
    relied upon, and is checked by CI. *)

Section QcStrictness.

Lemma qc_add_0_l : forall q : Qc, 0 + q = q.
Proof. intro q. apply Qcplus_0_l. Qed.

Lemma qc_add_0_r : forall q : Qc, q + 0 = q.
Proof. intro q. rewrite Qcplus_comm. apply Qcplus_0_l. Qed.

Lemma qc_add_assoc : forall a b c : Qc, a + (b + c) = a + b + c.
Proof. intros a b c. apply Qcplus_assoc. Qed.

End QcStrictness.

(** ** Elementary step of a normalized distance derivation.

    A step records the two names it relates, the rational bound it
    announces, and the concrete finite leaf data the checker consults.
    The leaf stays opaque ([list bool]) on purpose: the paper's normal
    form constrains the STRUCTURAL spine, not the internal encoding of
    a primitive verification record. *)

Record DistStep (Name : Type) : Type := mkDistStep {
  ds_src   : Name;
  ds_tgt   : Name;
  ds_bound : Qc;
  ds_leaf  : list bool
}.

Arguments mkDistStep {_} _ _ _ _.
Arguments ds_src   {_} _.
Arguments ds_tgt   {_} _.
Arguments ds_bound {_} _.
Arguments ds_leaf  {_} _.

(** ** Normalized derivation = flattened spine. *)

Definition DistSpine (Name : Type) : Type := list (DistStep Name).

(** Reflexivity is the unit: the empty spine. *)
Definition dsp_refl {Name : Type} : DistSpine Name := [].

(** Triangle composition is concatenation of spines. *)
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

(** ** Announced bound of a normalized derivation. *)

Definition dsp_bound {Name : Type} (W : DistSpine Name) : Qc :=
  fold_right (fun s acc => ds_bound s + acc) 0 W.

Lemma dsp_bound_refl :
  forall (Name : Type), dsp_bound (@dsp_refl Name) = 0.
Proof. intro Name. reflexivity. Qed.

(** Additivity of the bound under composition — a LEIBNIZ equality,
    which is what makes strict morphism laws possible downstream. *)

Lemma dsp_bound_comp :
  forall (Name : Type) (W1 W2 : DistSpine Name),
    dsp_bound (dsp_comp W1 W2) = dsp_bound W1 + dsp_bound W2.
Proof.
  intros Name W1 W2. unfold dsp_comp.
  induction W1 as [|s W1 IH]; simpl.
  - symmetry. apply qc_add_0_l.
  - rewrite IH. apply qc_add_assoc.
Qed.

(** ** Symmetry.

    The symmetry rule reverses the spine and flips each step. It is
    contravariant on composition, as a symmetry rule must be. *)

Definition ds_flip {Name : Type} (s : DistStep Name) : DistStep Name :=
  mkDistStep (ds_tgt s) (ds_src s) (ds_bound s) (ds_leaf s).

Definition dsp_sym {Name : Type} (W : DistSpine Name) : DistSpine Name :=
  rev (map ds_flip W).

Lemma dsp_sym_refl :
  forall (Name : Type), dsp_sym (@dsp_refl Name) = dsp_refl.
Proof. intro Name. reflexivity. Qed.

Lemma dsp_sym_comp :
  forall (Name : Type) (W1 W2 : DistSpine Name),
    dsp_sym (dsp_comp W1 W2) = dsp_comp (dsp_sym W2) (dsp_sym W1).
Proof.
  intros Name W1 W2. unfold dsp_sym, dsp_comp.
  rewrite map_app. apply rev_app_distr.
Qed.

Lemma ds_flip_involutive :
  forall (Name : Type) (s : DistStep Name), ds_flip (ds_flip s) = s.
Proof. intros Name [a b q l]. reflexivity. Qed.

Lemma dsp_sym_involutive :
  forall (Name : Type) (W : DistSpine Name), dsp_sym (dsp_sym W) = W.
Proof.
  intros Name W. unfold dsp_sym.
  rewrite map_rev, rev_involutive, map_map.
  rewrite <- (map_id W) at 2.
  apply map_ext. intro s. apply ds_flip_involutive.
Qed.

Lemma dsp_bound_sym :
  forall (Name : Type) (W : DistSpine Name),
    dsp_bound (dsp_sym W) = dsp_bound W.
Proof.
  intros Name W. unfold dsp_sym.
  induction W as [|s W IH]; simpl; [reflexivity|].
  rewrite fold_right_app. simpl.
  rewrite <- IH. clear IH.
  (* fold over a reversed list with a commutative-associative operator *)
  generalize (rev (map ds_flip W)) as L. intro L.
  induction L as [|t L IHL]; simpl.
  - rewrite qc_add_0_r. reflexivity.
  - rewrite <- IHL. rewrite !qc_add_assoc.
    f_equal. apply Qcplus_comm.
Qed.

(** ** Transport of a normalized derivation along a map on names.

    This is the shape Θ_T takes: a step-local transformation applied
    pointwise. [map] makes the two strict laws Θ_T must satisfy —
    preservation of the identity and of concatenation — into [map_nil]
    (definitional) and [map_app] (a Leibniz equality). Nothing is
    assumed about the transformer beyond being step-local, which is
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

(** ** Proof-component irrelevance for checker acceptance.

    A morphism of the evidence category bundles its normalized spine
    with a proof that the checker accepts it. To conclude equality of
    two morphisms from equality of their spines and bounds, the proof
    components must be equal too. Checker acceptance is an equality of
    booleans, so this follows from decidable equality on [bool] via
    Hedberg — NO axiom is required, in particular not [proof_irrelevance]
    or [UIP] as an assumption. *)

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
        V3_EvidenceSyntax.DistSpine, dsp_refl, dsp_comp.
      Rocq theorems:
        dsp_comp_refl_l, dsp_comp_refl_r, dsp_comp_assoc
        (strict unitality and associativity, as Leibniz equalities);
        dsp_bound_refl, dsp_bound_comp (the announced bound is additive,
        also as a Leibniz equality, because bounds are canonical [Qc]).
      Correspondence: DEFINITION-EXACT for the normal form, with the
      strictness claims proved rather than assumed.

    Deliberately NOT claimed here:

      - That this is the only possible reading of the paper's normal
        form. It is *a* faithful one: flattened spine, reflexivity as
        unit, concatenation as composition. If the intended normal form
        carries additional structure (e.g. explicit weakening nodes
        rather than bound arithmetic), this module is where that would
        be recorded.
      - Anything about [AppCheck]. Approximation evidence is not
        composed along a spine, so it needs no normal form of this kind;
        the mixed rule that turns a distance derivation plus an
        approximation certificate into an approximation certificate is
        a separate constructor, added when Def 5.1 needs it.
      - Any connection to a concrete presentation. Wiring
        [V3_Presentation.Presentation] to consume [DistSpine] is the
        next commit. *)
