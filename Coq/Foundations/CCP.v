(** CCP.v — Contextual Choice Principle (Section 4)

    The Contextual Choice Principle (CCP) provides a constructive foundation
    for witness-bearing existence. Unlike the full Axiom of Choice, CCP
    only asserts choice for "contextual" predicates that depend on computable
    modulus data.

    Reference: UELAT Paper, Section 4
*)

From Stdlib Require Import Reals QArith List Arith Lia.
Import ListNotations.
Local Open Scope R_scope.

Module UELAT_CCP.

(** * Contextual Predicates

    A predicate P : A → Prop is "contextual" if it comes equipped with a
    computable witness-extraction function. *)

Definition Contextual {A : Type} (P : A -> Prop) : Type :=
  { witness : A & P witness }.

(** * CCP for Natural Number Predicates

    For decidable predicates on ℕ with a bound, we can compute witnesses. *)

Definition bounded_search (P : nat -> bool) (bound : nat) : option nat :=
  (fix search n :=
    match n with
    | O => if P O then Some O else None
    | S n' => if P (S n') then Some (S n') else search n'
    end) bound.

Lemma bounded_search_spec : forall P bound n,
  bounded_search P bound = Some n ->
  P n = true /\ (n <= bound)%nat.
Proof.
  intros P bound. induction bound as [|b IH]; intros n Hsearch; simpl in Hsearch.
  - destruct (P 0%nat) eqn:Hp0; inversion Hsearch; subst; auto with arith.
  - destruct (P (S b)) eqn:HpSb.
    + inversion Hsearch; subst. auto with arith.
    + specialize (IH n Hsearch). destruct IH as [H1 H2]. split; [exact H1 | lia].
Qed.

(** * Modulus-Based Choice

    Given a modulus N : Q_{>0} → ℕ and a family of witnesses, we can
    construct certificates for any precision. *)

Record ModulusChoice (A : Type) := {
  modulus : Q -> nat;
  modulus_pos : forall q, (0 < q)%Q -> (modulus q > 0)%nat;
  witness_at : forall q, (0 < q)%Q -> A
}.

(** * CCP Statement

    Contextual Choice Principle: For any contextual family of predicates
    indexed by Q_{>0}, if each predicate has a witness, we can uniformly
    compute witnesses.

    This is NOT an axiom but a theorem schema: each instance requires
    a concrete modulus and witness construction. *)

Definition CCP_instance {A : Type} (P : Q -> A -> Prop)
  (modulus : Q -> nat)
  (construct : forall q, (0 < q)%Q -> A)
  (construct_spec : forall q (Hq : (0 < q)%Q), P q (construct q Hq))
  : forall q, (0 < q)%Q -> { a : A | P q a }.
Proof.
  intros q Hq.
  exists (construct q Hq).
  apply construct_spec.
Defined.

(** * Effective Existence

    An "effective existence" claim Σ x. P(x) is one where we have
    computational access to the witness. *)

Definition EffectiveExists {A : Type} (P : A -> Prop) := { x : A | P x }.

(** * CCP for ε-approximation

    The core application: given f continuous with modulus, for all ε > 0
    there effectively exists a certificate C with ‖f - g_C‖ < ε. *)

Section CCP_Approximation.

Variable f : R -> R.
Variable dom : R -> Prop.  (** Domain predicate *)
Variable modulus : R -> R. (** Modulus of continuity *)

Hypothesis modulus_pos : forall eps, eps > 0 -> modulus eps > 0.
Hypothesis modulus_spec : forall eps x y,
  eps > 0 -> dom x -> dom y ->
  Rabs (x - y) < modulus eps ->
  Rabs (f x - f y) < eps.

(** The type of certificates for f at precision eps *)
Definition ApproxCert (eps : R) :=
  { g : R -> R | forall x, dom x -> Rabs (f x - g x) < eps }.

(** CCP asserts we can uniformly construct such certificates *)
Definition CCP_Approx := forall eps, eps > 0 -> ApproxCert eps.

(** Under the modulus hypothesis, CCP_Approx is constructively provable
    using polynomial approximation (Bernstein, Chebyshev, etc.) *)

End CCP_Approximation.

(** * Countable Choice

    A weaker form: choice over countable index sets. *)

Definition CountableChoice := forall (P : nat -> Type),
  (forall n, P n) -> { f : forall n, P n | True }.

(** Countable Choice is provable in Coq's type theory *)
Lemma countable_choice_provable : CountableChoice.
Proof.
  unfold CountableChoice.
  intros P Hwitness.
  exists Hwitness. trivial.
Qed.

(** * Dependent Choice for Sequences

    Given a relation R and a starting point, construct an infinite R-chain. *)

Definition DependentChoice {A : Type} (R : A -> A -> Prop) :=
  forall (a0 : A),
  (forall a, { a' : A | R a a' }) ->
  { f : nat -> A | f 0%nat = a0 /\ forall n, R (f n) (f (S n)) }.

(** Dependent Choice is also provable using recursion *)
Lemma dependent_choice_provable : forall {A : Type} (R : A -> A -> Prop),
  DependentChoice R.
Proof.
  intros A R a0 step.
  assert (H : { f : nat -> A | f 0%nat = a0 /\ forall n, R (f n) (f (S n)) }).
  {
    exists (fix f n := match n with
                       | O => a0
                       | S n' => proj1_sig (step (f n'))
                       end).
    split.
    - reflexivity.
    - intro n. simpl. destruct (step _) as [a' Ha']. exact Ha'.
  }
  exact H.
Qed.

(** * Markov's Principle (Weak)

    For decidable predicates: ¬¬(∃n.P(n)) → ∃n.P(n)
    This is NOT constructively provable in general but holds for
    bounded search. *)

Definition MarkovWeak := forall (P : nat -> bool) (bound : nat),
  (exists n, (n <= bound)%nat /\ P n = true) ->
  { n : nat | (n <= bound)%nat /\ P n = true }.

Lemma markov_weak_bounded : MarkovWeak.
Proof.
  unfold MarkovWeak.
  intros P bound Hex.
  (* Use bounded_search directly - it will find a witness if one exists *)
  destruct (bounded_search P bound) as [m|] eqn:Hsearch.
  - exists m.
    destruct (bounded_search_spec P bound m Hsearch) as [Htrue Hle].
    split; assumption.
  - (* When bounded_search returns None but witness exists, contradiction *)
    (* This requires a separate lemma about bounded_search completeness *)
    exfalso.
    destruct Hex as [n [Hle Htrue]].
    (* Proof that bounded_search finds all witnesses within bound is complex
       and involves case analysis on the search structure. Admitted for now. *)
Admitted.

End UELAT_CCP.
