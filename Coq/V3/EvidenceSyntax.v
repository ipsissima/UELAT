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

    That is a hypothesis of the paper, and it is what Definition 5.1's
    clause on Θ_T needs: Θ_T must preserve identity and concatenation ON
    THE NOSE. Until the normal form is represented, "on the nose"
    cannot be stated.

    ** Representation: endpoint-indexed flattened spine

    [Spine a b] is a flattened list of primitive steps running from name
    [a] to name [b], with the endpoints carried in the TYPE:

      sp_nil  : Spine a a                                  (reflexivity)
      sp_cons : PrimStep a b -> Spine b c -> Spine a c     (one step)

    Reflexivity is the empty spine, and composition [sp_app] is
    concatenation — so "strictly unital and associative" is proved
    below as Leibniz equalities.

    ** Three properties this buys, and why each was needed

    (1) NON-COMPOSABLE SPINES ARE UNTYPEABLE. A raw list of
        source/target steps admits [a → b] followed by [c → d] with
        [b <> c]. Here the shared index makes that ill-typed.

    (2) Θ_T SEES BOTH ENDPOINTS. This is the decisive reason for
        indexing rather than storing only a target and threading the
        source positionally. A source-blind step forces transport to be
        [map step], and a step-local [step] cannot depend on where its
        step STARTED. But Def 5.1's transformer is
        Θ_T(ν, μ, r, W) — it is allowed to depend on both names, and
        the existing [rm_dist_promote] signature takes both. Restricting
        to a source-blind θ_T(μ, r, W) would silently strengthen
        Def 5.1. Here [sp_transport] recurses over the indexed spine, so
        its primitive component receives BOTH endpoint names.

    (3) THE ENDPOINT IS STRUCTURAL, NOT INFERRED FROM SOUNDNESS. With a
        computed endpoint one would have to tie "the spine ends at μ" to
        the declared target via the checker. That does not work:
        [DistCheck_sound] yields an analytic distance inequality between
        DECODED names, never syntactic equality of names, so it cannot
        discharge the endpoint obligation the strict functor laws need.
        Indexing removes the obligation instead of trying to recover it.

    ** Semantic validity stays checker-mediated

    Indexing carries only STRUCTURAL endpoints. Whether a primitive step
    is a valid distance witness remains a terminating boolean check:
    [PrimStep a b] bundles a rational bound, finite witness data, and a
    proof that the supplied leaf checker accepts them. So this does not
    trade the paper's checker philosophy for dependent types; it applies
    typing only to composability, which is syntax, and leaves
    admissibility to checkers, which is semantics.

    ** No decidable equality on names is assumed

    Definition 2.1 requires [Name_F] to be a set with a surjection onto
    the represented domain; it nowhere requires decidable equality. The
    indexed representation needs none — composability is definitional
    rather than tested.

    ** Why bounds live in [Qc] and not [Q]

    With plain [Q], [(q1 + q2) + q3] and [q1 + (q2 + q3)] are distinct
    terms equal only under [Qeq], so strict associativity of MORPHISMS
    would degrade to "up to Qeq" even where spines composed strictly —
    weakening exactly the clause Def 5.1 depends on. [Qcanon.Qc] has
    Leibniz unit and associativity laws; section [QcStrictness]
    re-proves the three facts relied on so CI fails here rather than
    silently downstream. *)

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

(** ** Proof-component irrelevance for checker acceptance.

    Two primitive steps with the same bound and the same witness are
    equal, because the remaining component is an equality of booleans
    and [bool] has decidable equality (Hedberg). NO axiom is used — in
    particular not [proof_irrelevance] and not [UIP] as an assumption. *)

Lemma checker_proof_irrelevant :
  forall (b : bool) (p q : b = true), p = q.
Proof. intros b p q. apply (UIP_dec Bool.bool_dec). Qed.

(** ** Primitive steps and normalized spines. *)

Section Normalized.

Variable Name : Type.
Variable DistLeaf : Name -> Name -> Qc -> list bool -> bool.

(** A primitive step from [nu] to [mu]: a rational bound, finite
    witness data, and terminating-checker acceptance. *)

Record PrimStep (nu mu : Name) : Type := mkPrimStep {
  ps_bound   : Qc;
  ps_witness : list bool;
  ps_ok      : DistLeaf nu mu ps_bound ps_witness = true
}.

(** Two primitive steps between the same names, with the same bound and
    witness, are equal. Uses [checker_proof_irrelevant]; no axiom. *)

Lemma PrimStep_eq :
  forall (nu mu : Name) (s t : PrimStep nu mu),
    ps_bound nu mu s = ps_bound nu mu t ->
    ps_witness nu mu s = ps_witness nu mu t ->
    s = t.
Proof.
  intros nu mu [b1 w1 p1] [b2 w2 p2] Hb Hw. simpl in *.
  subst b2 w2. f_equal. apply checker_proof_irrelevant.
Qed.

(** The endpoint-indexed flattened spine. *)

Inductive Spine : Name -> Name -> Type :=
| sp_nil  : forall a : Name, Spine a a
| sp_cons : forall a b c : Name, PrimStep a b -> Spine b c -> Spine a c.

(** Concatenation. The convoy pattern makes the dependent match
    explicit rather than relying on inference. *)

Fixpoint sp_app (a b c : Name) (W1 : Spine a b) (W2 : Spine b c)
  {struct W1} : Spine a c :=
  match W1 in Spine x y return Spine y c -> Spine x c with
  | sp_nil x            => fun W => W
  | sp_cons x m y s rest => fun W => sp_cons x m c s (sp_app m y c rest W)
  end W2.

(** ** Strict unitality and associativity, as Leibniz equalities.

    The left unit law holds definitionally; the other two are proved by
    induction, and neither requires a cast, because the indices of both
    sides are syntactically identical. *)

Lemma sp_app_nil_l :
  forall (a b : Name) (W : Spine a b), sp_app a a b (sp_nil a) W = W.
Proof. intros a b W. reflexivity. Qed.

Lemma sp_app_nil_r :
  forall (a b : Name) (W : Spine a b), sp_app a b b W (sp_nil b) = W.
Proof.
  intros a b W. induction W as [x | x m y s rest IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma sp_app_assoc :
  forall (a b c d : Name)
         (W1 : Spine a b) (W2 : Spine b c) (W3 : Spine c d),
    sp_app a c d (sp_app a b c W1 W2) W3
    = sp_app a b d W1 (sp_app b c d W2 W3).
Proof.
  intros a b c d W1. revert c d.
  induction W1 as [x | x m y s rest IH]; intros c d W2 W3; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

(** ** Announced bound. *)

Fixpoint sp_bound (a b : Name) (W : Spine a b) {struct W} : Qc :=
  match W with
  | sp_nil _             => 0
  | sp_cons _ m _ s rest => ps_bound _ _ s + sp_bound m _ rest
  end.

Lemma sp_bound_nil :
  forall a : Name, sp_bound a a (sp_nil a) = 0.
Proof. reflexivity. Qed.

(** Additivity — a LEIBNIZ equality, which is what makes strict
    morphism laws possible downstream. *)

Lemma sp_bound_app :
  forall (a b c : Name) (W1 : Spine a b) (W2 : Spine b c),
    sp_bound a c (sp_app a b c W1 W2)
    = sp_bound a b W1 + sp_bound b c W2.
Proof.
  intros a b c W1. revert c.
  induction W1 as [x | x m y s rest IH]; intros c W2; simpl.
  - symmetry. apply qc_add_0_l.
  - rewrite IH. apply qc_add_assoc.
Qed.

End Normalized.

Arguments PrimStep {_} _ _ _.
Arguments mkPrimStep {_ _ _ _} _ _ _.
Arguments ps_bound {_ _ _ _} _.
Arguments ps_witness {_ _ _ _} _.
Arguments ps_ok {_ _ _ _} _.
Arguments Spine {_} _ _ _.
Arguments sp_nil {_ _} _.
Arguments sp_cons {_ _} _ _ _ _ _.
Arguments sp_app {_ _ _ _ _} _ _.
Arguments sp_bound {_ _ _ _} _.

(** ** Transport of a normalized derivation — the shape of Θ_T.

    [sp_transport] recurses over the indexed spine. Its primitive
    component [theta_prim] receives BOTH endpoint names [nu] and [mu],
    so it expresses the general Θ_T(ν, μ, r, W) of Definition 5.1
    rather than a source-blind special case. *)

Section Transport.

Variable NameA NameB : Type.
Variable LeafA : NameA -> NameA -> Qc -> list bool -> bool.
Variable LeafB : NameB -> NameB -> Qc -> list bool -> bool.

(** The name transformer, i.e. [T^#]. *)
Variable g : NameA -> NameB.

(** The primitive evidence transformer. It sees both endpoints. *)
Variable theta_prim :
  forall nu mu : NameA, PrimStep LeafA nu mu -> PrimStep LeafB (g nu) (g mu).

Fixpoint sp_transport (a b : NameA) (W : Spine LeafA a b) {struct W}
  : Spine LeafB (g a) (g b) :=
  match W in Spine _ x y return Spine LeafB (g x) (g y) with
  | sp_nil x             => sp_nil (g x)
  | sp_cons x m y s rest => sp_cons (g x) (g m) (g y)
                                    (theta_prim x m s)
                                    (sp_transport m y rest)
  end.

(** ** The two strict laws Θ_T must satisfy, as genuine theorems.

    Identity preservation is definitional; concatenation preservation
    is a Leibniz equality proved by induction, with no cast. *)

Lemma sp_transport_nil :
  forall a : NameA, sp_transport a a (sp_nil a) = sp_nil (g a).
Proof. reflexivity. Qed.

Lemma sp_transport_app :
  forall (a b c : NameA) (W1 : Spine LeafA a b) (W2 : Spine LeafA b c),
    sp_transport a c (sp_app W1 W2)
    = sp_app (sp_transport a b W1) (sp_transport b c W2).
Proof.
  intros a b c W1. revert c.
  induction W1 as [x | x m y s rest IH]; intros c W2; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

(** If the primitive transformer scales bounds by a fixed factor, the
    whole spine's bound scales by that factor. This is the arithmetic
    half of the Λ_T-Lipschitz clause of Theorem 5.2. *)

Lemma sp_bound_transport_scale :
  forall (Lam : Qc),
    (forall nu mu (s : PrimStep LeafA nu mu),
        ps_bound (theta_prim nu mu s) = Lam * ps_bound s) ->
    forall (a b : NameA) (W : Spine LeafA a b),
      sp_bound (sp_transport a b W) = Lam * sp_bound W.
Proof.
  intros Lam Hscale a b W.
  induction W as [x | x m y s rest IH]; simpl.
  - symmetry. apply Qcmult_0_r.
  - rewrite Hscale, IH. symmetry. apply Qcmult_plus_distr_r.
Qed.

End Transport.

Arguments sp_transport {_ _ _ _} _ _ {_ _} _.

End V3_EvidenceSyntax.

(** ** Correspondence with v3

      Paper text:
        §2, the normalized-proof-tree convention following Def 2.1
        ("reflexivity is the unit and the triangle-composition spine is
         flattened ... strictly unital and associative").
      Rocq definitions:
        V3_EvidenceSyntax.Spine, sp_nil, sp_cons, sp_app, sp_bound.
      Rocq theorems:
        sp_app_nil_l, sp_app_nil_r, sp_app_assoc
          — strict unitality and associativity, Leibniz;
        sp_bound_nil, sp_bound_app
          — the announced bound is additive, Leibniz, because bounds
            are canonical [Qc];
        sp_transport_nil, sp_transport_app
          — the two strict laws Θ_T must satisfy, proved rather than
            assumed, for a transformer that sees BOTH endpoints;
        sp_bound_transport_scale
          — arithmetic half of the Λ_T-Lipschitz clause of Thm 5.2;
        PrimStep_eq, checker_proof_irrelevant
          — step equality from bound and witness alone, axiom-free.
      Correspondence: DEFINITION-EXACT for the normal form, with the
      strictness claims proved rather than assumed.

    Deliberately NOT claimed here:

      - SYMMETRY of normalized spines. Reversing an indexed spine is a
        genuine construction (it must rebuild the chain backwards), and
        it is off the critical path for the strict category laws and for
        Def 5.1's Θ_T clause. It remains an abstract witness constructor
        in [V3_Evidence.EvidenceClosure]. This is a recorded gap, not a
        claim.
      - WEAKENING. Raising an announced bound is not yet represented; as
        with symmetry it stays an abstract closure constructor for now.
      - Anything about [AppCheck]. Approximation evidence is not
        composed along a spine and so needs no normal form of this kind.
        The mixed rule turning a distance derivation plus an
        approximation certificate into an approximation certificate is a
        separate constructor, added when Def 5.1 needs it.
      - Any connection to a concrete presentation. Wiring
        [V3_Presentation.Presentation] to supply [DistLeaf] is the next
        commit. *)
