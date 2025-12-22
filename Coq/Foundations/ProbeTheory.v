(** ProbeTheory.v — Category of finite probe theories (Section 3.2)

    A probe theory is a finite collection of "probes" (evaluation functionals)
    together with their observed values. This forms the syntactic/algebraic
    side of the Probes-Models adjunction.

    Reference: UELAT Paper, Section 3.2
*)

From Coq Require Import Reals QArith List Arith Lia.
Import ListNotations.
Local Open Scope R_scope.

Module UELAT_Probe.

(** * Finite Probe Theory

    A probe theory T = (n, φ, a) consists of:
    - rank n ∈ ℕ (number of probes)
    - probe identifiers φ : Fin(n) → P (from a countable set P ≅ ℕ)
    - answer vector a : Fin(n) → ℚ (observed values)
*)

Record ProbeTheory := {
  rank : nat;
  probes : list nat;           (** Probe identifiers from countable P *)
  answers : list Q;            (** Answer vector *)
  rank_probes : length probes = rank;
  rank_answers : length answers = rank
}.

(** * Empty Probe Theory *)

Program Definition empty_theory : ProbeTheory := {|
  rank := 0;
  probes := [];
  answers := []
|}.

(** * Singleton Probe Theory *)

Program Definition singleton_theory (p : nat) (a : Q) : ProbeTheory := {|
  rank := 1;
  probes := [p];
  answers := [a]
|}.

(** * Probe Theory Morphisms

    A morphism f : T → T' is an order-preserving injection that
    preserves both probe identifiers and answer values. *)

Record ProbeMorphism (T T' : ProbeTheory) := {
  injection : nat -> nat;
  inj_preserves_order : forall i j, (i < j)%nat ->
    (injection i < injection j)%nat;
  inj_in_range : forall i, (i < rank T)%nat ->
    (injection i < rank T')%nat;
  inj_preserves_probes : forall i, (i < rank T)%nat ->
    nth i (probes T) 0%nat = nth (injection i) (probes T') 0%nat;
  inj_preserves_answers : forall i, (i < rank T)%nat ->
    nth i (answers T) 0%Q = nth (injection i) (answers T') 0%Q
}.

Arguments injection {T T'} _ _.
Arguments inj_preserves_order {T T'} _ _ _ _.
Arguments inj_in_range {T T'} _ _ _.
Arguments inj_preserves_probes {T T'} _ _ _.
Arguments inj_preserves_answers {T T'} _ _ _.

(** * Identity Morphism *)

Definition probe_id (T : ProbeTheory) : ProbeMorphism T T.
Proof.
  refine {| injection := fun i => i |}.
  - intros i j Hij; exact Hij.
  - intros i Hi; exact Hi.
  - intros i Hi; reflexivity.
  - intros i Hi; reflexivity.
Defined.

(** * Composition of Morphisms *)

Definition probe_compose {T T' T'' : ProbeTheory}
  (f : ProbeMorphism T T') (g : ProbeMorphism T' T'') : ProbeMorphism T T''.
Proof.
  refine {| injection := fun i => injection g (injection f i) |}.
  - intros i j Hij.
    apply (inj_preserves_order g).
    apply (inj_preserves_order f).
    exact Hij.
  - intros i Hi.
    apply (inj_in_range g).
    apply (inj_in_range f).
    exact Hi.
  - intros i Hi.
    rewrite <- (inj_preserves_probes g).
    + apply (inj_preserves_probes f). exact Hi.
    + apply (inj_in_range f). exact Hi.
  - intros i Hi.
    rewrite <- (inj_preserves_answers g).
    + apply (inj_preserves_answers f). exact Hi.
    + apply (inj_in_range f). exact Hi.
Defined.

(** * Category Laws *)

Lemma probe_id_left : forall T T' (f : ProbeMorphism T T'),
  forall i, injection f i = injection (probe_compose (probe_id T) f) i.
Proof. reflexivity. Qed.

Lemma probe_id_right : forall T T' (f : ProbeMorphism T T'),
  forall i, injection f i = injection (probe_compose f (probe_id T')) i.
Proof. reflexivity. Qed.

Lemma probe_compose_assoc : forall T1 T2 T3 T4
  (f : ProbeMorphism T1 T2) (g : ProbeMorphism T2 T3) (h : ProbeMorphism T3 T4),
  forall i, injection (probe_compose f (probe_compose g h)) i =
            injection (probe_compose (probe_compose f g) h) i.
Proof. reflexivity. Qed.

(** * Probe Theory Extension

    Add a new probe to an existing theory. *)

Program Definition extend_theory (T : ProbeTheory) (p : nat) (a : Q) : ProbeTheory := {|
  rank := S (rank T);
  probes := probes T ++ [p];
  answers := answers T ++ [a]
|}.
Next Obligation.
  rewrite app_length. simpl. rewrite rank_probes. lia.
Qed.
Next Obligation.
  rewrite app_length. simpl. rewrite rank_answers. lia.
Qed.

(** * Inclusion morphism for extension *)

Definition extend_inclusion (T : ProbeTheory) (p : nat) (a : Q) :
  ProbeMorphism T (extend_theory T p a).
Proof.
  refine {| injection := fun i => i |}.
  - intros i j Hij; exact Hij.
  - intros i Hi; simpl; lia.
  - intros i Hi.
    simpl. rewrite app_nth1; [reflexivity | rewrite rank_probes; exact Hi].
  - intros i Hi.
    simpl. rewrite app_nth1; [reflexivity | rewrite rank_answers; exact Hi].
Defined.

(** * Probe Theory Union

    Disjoint union of two probe theories. *)

Program Definition union_theory (T1 T2 : ProbeTheory) : ProbeTheory := {|
  rank := rank T1 + rank T2;
  probes := probes T1 ++ probes T2;
  answers := answers T1 ++ answers T2
|}.
Next Obligation.
  rewrite app_length. rewrite rank_probes. rewrite rank_probes. lia.
Qed.
Next Obligation.
  rewrite app_length. rewrite rank_answers. rewrite rank_answers. lia.
Qed.

(** * Left injection into union *)

Definition union_inl (T1 T2 : ProbeTheory) : ProbeMorphism T1 (union_theory T1 T2).
Proof.
  refine {| injection := fun i => i |}.
  - intros i j Hij; exact Hij.
  - intros i Hi; simpl; lia.
  - intros i Hi.
    simpl. rewrite app_nth1; [reflexivity | rewrite rank_probes; exact Hi].
  - intros i Hi.
    simpl. rewrite app_nth1; [reflexivity | rewrite rank_answers; exact Hi].
Defined.

(** * Right injection into union *)

Definition union_inr (T1 T2 : ProbeTheory) : ProbeMorphism T2 (union_theory T1 T2).
Proof.
  refine {| injection := fun i => rank T1 + i |}.
  - intros i j Hij; lia.
  - intros i Hi; simpl; lia.
  - intros i Hi.
    simpl. rewrite app_nth2; [| rewrite rank_probes; lia].
    rewrite rank_probes.
    replace (rank T1 + i - rank T1)%nat with i by lia.
    reflexivity.
  - intros i Hi.
    simpl. rewrite app_nth2; [| rewrite rank_answers; lia].
    rewrite rank_answers.
    replace (rank T1 + i - rank T1)%nat with i by lia.
    reflexivity.
Defined.

(** * Probe Subset Relation *)

Definition probe_subset (T T' : ProbeTheory) : Prop :=
  exists (f : ProbeMorphism T T'), True.

Lemma probe_subset_refl : forall T, probe_subset T T.
Proof.
  intro T. exists (probe_id T). trivial.
Qed.

Lemma probe_subset_trans : forall T1 T2 T3,
  probe_subset T1 T2 -> probe_subset T2 T3 -> probe_subset T1 T3.
Proof.
  intros T1 T2 T3 [f _] [g _].
  exists (probe_compose f g). trivial.
Qed.

End UELAT_Probe.
