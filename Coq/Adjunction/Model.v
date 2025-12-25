(** Model.v — Category Model with locally finite condition (Section 3)

    This module defines the category Model of analytic models,
    which forms the other side of the Probes-Models adjunction.
    Objects are finite-dimensional subspaces of a function space.

    Reference: UELAT Paper, Section 3
*)

From Coq Require Import Reals QArith List Arith Lia.
From UELAT.Foundations Require Import ProbeTheory.
Import ListNotations.
Local Open Scope R_scope.

Module UELAT_Model.

(** * Basis Family

    We work with a countable orthonormal basis {b_φ}_{φ ∈ P}
    indexed by a countable set P ≅ ℕ. *)

(** Abstract basis type *)
Parameter Basis : Type.
Parameter basis_eval : Basis -> nat -> R -> R.
  (** basis_eval B φ x = b_φ(x) *)

(** Orthonormality axiom (stated abstractly) *)
Parameter basis_orthonormal : Basis -> Prop.

(** * Locally Finite Condition

    A basis family is "locally finite" if for each finite subset S ⊂ [0,1]
    and threshold τ > 0, only finitely many basis elements have
    |b_φ(x)| > τ for some x ∈ S. *)

Definition LocallyFinite (B : Basis) : Prop :=
  forall (S : list R) (tau : R),
    tau > 0 ->
    exists (bound : nat),
      forall (phi : nat) (x : R),
        In x S ->
        (phi > bound)%nat ->
        Rabs (basis_eval B phi x) <= tau.

(** * Finite-Dimensional Subspaces *)

Record FinDimSubspace := {
  fds_dim : nat;
  fds_basis_indices : list nat;
  fds_dim_spec : length fds_basis_indices = fds_dim
}.

(** Inclusion of subspaces *)
Definition subspace_incl (W1 W2 : FinDimSubspace) : Prop :=
  forall i, In i (fds_basis_indices W1) -> In i (fds_basis_indices W2).

(** * Model Morphisms

    A morphism W → W' is witnessed by subspace inclusion. *)

Record ModelMorphism (W W' : FinDimSubspace) := {
  mm_incl : subspace_incl W W'
}.

Arguments mm_incl {W W'} _.

(** * Category Structure *)

Definition model_id (W : FinDimSubspace) : ModelMorphism W W.
Proof.
  refine {| mm_incl := _ |}.
  unfold subspace_incl. intros i Hi. exact Hi.
Defined.

Definition model_compose {W1 W2 W3 : FinDimSubspace}
  (f : ModelMorphism W1 W2) (g : ModelMorphism W2 W3) : ModelMorphism W1 W3.
Proof.
  refine {| mm_incl := _ |}.
  unfold subspace_incl. intros i Hi.
  apply (mm_incl g). apply (mm_incl f). exact Hi.
Defined.

(** * Span Construction

    Given a list of basis indices, construct the spanned subspace. *)

Program Definition span (indices : list nat) : FinDimSubspace := {|
  fds_dim := length indices;
  fds_basis_indices := indices
|}.

(** * Zero Subspace *)

Definition zero_subspace : FinDimSubspace := span [].

(** * Sum of Subspaces *)

Program Definition subspace_sum (W1 W2 : FinDimSubspace) : FinDimSubspace := {|
  fds_dim := length (fds_basis_indices W1 ++ fds_basis_indices W2);
  fds_basis_indices := fds_basis_indices W1 ++ fds_basis_indices W2
|}.

(** Injections into sum *)

Definition sum_inl (W1 W2 : FinDimSubspace) : ModelMorphism W1 (subspace_sum W1 W2).
Proof.
  refine {| mm_incl := _ |}.
  unfold subspace_incl. intros i Hi. simpl.
  apply in_or_app. left. exact Hi.
Defined.

Definition sum_inr (W1 W2 : FinDimSubspace) : ModelMorphism W2 (subspace_sum W1 W2).
Proof.
  refine {| mm_incl := _ |}.
  unfold subspace_incl. intros i Hi. simpl.
  apply in_or_app. right. exact Hi.
Defined.

(** * Intersection of Subspaces *)

Fixpoint list_inter (l1 l2 : list nat) : list nat :=
  match l1 with
  | [] => []
  | x :: l1' =>
      if existsb (Nat.eqb x) l2
      then x :: list_inter l1' l2
      else list_inter l1' l2
  end.

Program Definition subspace_inter (W1 W2 : FinDimSubspace) : FinDimSubspace := {|
  fds_dim := length (list_inter (fds_basis_indices W1) (fds_basis_indices W2));
  fds_basis_indices := list_inter (fds_basis_indices W1) (fds_basis_indices W2)
|}.

(** Projections from intersection *)

Lemma list_inter_subset_l : forall l1 l2 x,
  In x (list_inter l1 l2) -> In x l1.
Proof.
  induction l1 as [|a l1' IH]; intros l2 x Hin; simpl in *.
  - contradiction.
  - destruct (existsb (Nat.eqb a) l2) eqn:Hex.
    + destruct Hin as [Heq | Hin'].
      * left. exact Heq.
      * right. apply IH. exact Hin'.
    + right. apply IH. exact Hin.
Qed.

Lemma list_inter_subset_r : forall l1 l2 x,
  In x (list_inter l1 l2) -> In x l2.
Proof.
  induction l1 as [|a l1' IH]; intros l2 x Hin; simpl in *.
  - contradiction.
  - destruct (existsb (Nat.eqb a) l2) eqn:Hex.
    + destruct Hin as [Heq | Hin'].
      * subst. apply existsb_exists in Hex.
        destruct Hex as [y [Hiny Heqb]].
        apply Nat.eqb_eq in Heqb. subst. exact Hiny.
      * apply IH. exact Hin'.
    + apply IH. exact Hin.
Qed.

Definition inter_proj_l (W1 W2 : FinDimSubspace) :
  ModelMorphism (subspace_inter W1 W2) W1.
Proof.
  refine {| mm_incl := _ |}.
  unfold subspace_incl. intros i Hi. simpl in Hi.
  apply list_inter_subset_l in Hi. exact Hi.
Defined.

Definition inter_proj_r (W1 W2 : FinDimSubspace) :
  ModelMorphism (subspace_inter W1 W2) W2.
Proof.
  refine {| mm_incl := _ |}.
  unfold subspace_incl. intros i Hi. simpl in Hi.
  apply list_inter_subset_r in Hi. exact Hi.
Defined.

(** * Directed Colimits in Model

    Model has filtered colimits, computed as unions of subspaces. *)

Record DirectedSystemModel := {
  dsm_index : nat -> FinDimSubspace;
  dsm_transition : forall n, ModelMorphism (dsm_index n) (dsm_index (S n))
}.

(** The colimit is the union of all basis indices *)
Fixpoint union_up_to (ds : DirectedSystemModel) (n : nat) : list nat :=
  match n with
  | O => fds_basis_indices (dsm_index ds O)
  | S n' => fds_basis_indices (dsm_index ds (S n')) ++ union_up_to ds n'
  end.

End UELAT_Model.
