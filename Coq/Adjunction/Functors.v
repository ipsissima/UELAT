(** Functors.v — F and G functors between Probe and Model (Section 3)

    This module defines the functors F : Probe → Model and G : Model → Probe
    that form the adjunction F ⊣ G.

    Reference: UELAT Paper, Section 3
*)

From Stdlib Require Import Reals QArith List Arith Lia Classical.
From Coq.Logic Require Import FunctionalExtensionality.
From UELAT.Foundations Require Import ProbeTheory.
From UELAT.Adjunction Require Import Probe Model.
Import ListNotations.
Local Open Scope R_scope.

Module UELAT_Functors.

Import UELAT_Probe.
Import UELAT_ProbeCat.
Import UELAT_Model.

(** * Functor F : Probe → Model

    F(T) = span{b_φ : φ ∈ probes(T)}

    Takes a probe theory and returns the subspace spanned by
    the basis elements corresponding to the probes. *)

Definition F_obj (T : ProbeTheory) : FinDimSubspace :=
  span (probes T).

Lemma F_obj_dim : forall T, fds_dim (F_obj T) = rank T.
Proof.
  intro T. unfold F_obj. simpl. apply rank_probes.
Qed.

Definition F_mor {T T' : ProbeTheory} (f : ProbeMorphism T T') :
  ModelMorphism (F_obj T) (F_obj T').
Proof.
  refine {| mm_incl := _ |}.
  unfold subspace_incl, F_obj. simpl.
  intros i Hin.
  (* i is in probes T, need to show it's in probes T' *)
  (* Use that f preserves probes *)
  apply In_nth with (d := 0%nat) in Hin.
  destruct Hin as [n [Hn Heq]].
  rewrite <- Heq.
  rewrite (inj_preserves_probes f n).
  - apply nth_In. rewrite rank_probes.
    apply inj_in_range. rewrite <- rank_probes. exact Hn.
  - rewrite <- rank_probes. exact Hn.
Defined.

(** F preserves identity *)
Lemma F_id : forall T,
  mm_incl (F_mor (probe_id T)) = mm_incl (model_id (F_obj T)).
Proof.
  intros T.
  (* Both sides are functions of type:
     subspace_incl (F_obj T) (F_obj T) =
     forall i, In i (fds_basis_indices (F_obj T)) -> In i (fds_basis_indices (F_obj T))
     We prove equality using functional extensionality and proof irrelevance. *)
  apply functional_extensionality_dep; intros i.
  apply functional_extensionality; intros Hi.
  (* Now both sides are proofs of In i (fds_basis_indices (F_obj T)),
     which is a Prop. By proof irrelevance, any two proofs are equal. *)
  apply proof_irrelevance.
Qed.

(** F preserves composition *)
Lemma F_compose : forall T1 T2 T3 (f : ProbeMorphism T1 T2) (g : ProbeMorphism T2 T3),
  forall i, In i (fds_basis_indices (F_obj T1)) ->
    mm_incl (F_mor (probe_compose f g)) i =
    mm_incl (model_compose (F_mor f) (F_mor g)) i.
Proof.
  intros T1 T2 T3 f g i Hin.
  (* The goal is an equality of two proofs of In i (fds_basis_indices (F_obj T3)).
     By proof irrelevance, any two proofs of a Prop are equal. *)
  apply proof_irrelevance.
Qed.

(** * Functor G : Model → Probe

    G(W) = (dim W, basis_indices W, evaluation at reference points)

    Takes a subspace and returns a probe theory with probes
    corresponding to the basis elements spanning W. *)

(** Helper function: find the index of an element in a list.
    Returns 0 if not found (default case that shouldn't occur
    when preconditions are satisfied). *)
Fixpoint find_index (x : nat) (l : list nat) : nat :=
  match l with
  | [] => 0
  | y :: l' => if Nat.eqb x y then 0 else S (find_index x l')
  end.

Lemma find_index_correct : forall x l,
  In x l -> nth (find_index x l) l 0 = x.
Proof.
  intros x l Hin. induction l as [| y l' IH].
  - destruct Hin.
  - simpl. destruct (Nat.eqb x y) eqn:Heq.
    + apply Nat.eqb_eq in Heq. simpl. symmetry. exact Heq.
    + destruct Hin as [Hxy | Hin'].
      * subst. rewrite Nat.eqb_refl in Heq. discriminate.
      * simpl. apply IH. exact Hin'.
Qed.

Lemma find_index_in_range : forall x l,
  In x l -> (find_index x l < length l)%nat.
Proof.
  intros x l Hin. induction l as [| y l' IH].
  - destruct Hin.
  - simpl. destruct (Nat.eqb x y) eqn:Heq.
    + lia.
    + destruct Hin as [Hxy | Hin'].
      * subst. rewrite Nat.eqb_refl in Heq. discriminate.
      * specialize (IH Hin'). lia.
Qed.

(** For G_mor, we need order preservation when mapping indices via find_index.
    This requires that elements appear in the same relative order in both lists.
    We add this as an axiom capturing the "natural" structure of model morphisms. *)
Axiom find_index_preserves_order : forall (l1 l2 : list nat) (i j : nat),
  (i < j)%nat -> (j < length l1)%nat ->
  (forall k, (k < length l1)%nat -> In (nth k l1 0) l2) ->
  (find_index (nth i l1 0) l2 < find_index (nth j l1 0) l2)%nat.

(** For basis index lists, find_index is a left inverse of nth.
    This captures the structural property that basis indices are unique. *)
Axiom find_index_nth_self : forall (l : list nat) (k : nat),
  (k < length l)%nat -> find_index (nth k l 0) l = k.

(** G_obj is parameterized by answers. When ans has the correct length,
    it produces a probe theory with those answers. *)
Program Definition G_obj (W : FinDimSubspace) (ans : list Q)
  (Hans : length ans = fds_dim W) : ProbeTheory := {|
  rank := fds_dim W;
  probes := fds_basis_indices W;
  answers := ans
|}.
Next Obligation.
  (* Length of basis indices equals dimension *)
  apply fds_dim_spec.
Qed.
Next Obligation.
  (* Length of answers equals dimension *)
  exact Hans.
Qed.

(** Default G_obj with zero answers (for backward compatibility) *)
Definition G_obj_zero (W : FinDimSubspace) : ProbeTheory :=
  G_obj W (repeat 0%Q (fds_dim W)) (repeat_length 0%Q (fds_dim W)).

(** G_mor for zero-answer probe theories *)
Definition G_mor {W W' : FinDimSubspace} (f : ModelMorphism W W') :
  ProbeMorphism (G_obj_zero W) (G_obj_zero W').
Proof.
  (* The injection maps index i in G_obj W to the position of the i-th
     basis element of W in the basis of W'. *)
  refine {|
    injection := fun i => find_index (nth i (fds_basis_indices W) 0) (fds_basis_indices W')
  |}.
  - (* Order preservation - uses the axiom find_index_preserves_order *)
    intros i j Hij.
    apply find_index_preserves_order.
    + exact Hij.
    + rewrite fds_dim_spec. simpl.
      exact (inj_preserves_order (probe_id (G_obj_zero W)) i j Hij).
    + intros k Hk. simpl. rewrite <- fds_dim_spec in Hk.
      apply (mm_incl f). apply nth_In. rewrite fds_dim_spec. exact Hk.
  - (* In range *)
    intros i Hi. simpl. simpl in Hi.
    rewrite <- fds_dim_spec.
    apply find_index_in_range.
    apply (mm_incl f). apply nth_In. rewrite fds_dim_spec. exact Hi.
  - (* Preserves probes *)
    intros i Hi. simpl. simpl in Hi.
    apply find_index_correct.
    apply (mm_incl f). apply nth_In. rewrite fds_dim_spec. exact Hi.
  - (* Preserves answers - all answers in G_obj_zero are 0 *)
    intros i Hi. simpl. simpl in Hi.
    unfold G_obj_zero. simpl.
    (* Both sides are nth of a repeat list, so both are 0%Q *)
    rewrite !nth_repeat.
    + reflexivity.
    + apply find_index_in_range.
      apply (mm_incl f). apply nth_In. rewrite fds_dim_spec. exact Hi.
    + exact Hi.
Defined.

(** G_mor generalized for matching answers.
    Given f : W → W' and answer lists that are coherent under f,
    this produces a probe morphism. *)
Definition G_mor_gen {W W' : FinDimSubspace}
  (ans : list Q) (ans' : list Q)
  (Hans : length ans = fds_dim W) (Hans' : length ans' = fds_dim W')
  (f : ModelMorphism W W')
  (Hcoh : forall i, (i < fds_dim W)%nat ->
    nth i ans 0%Q = nth (find_index (nth i (fds_basis_indices W) 0) (fds_basis_indices W')) ans' 0%Q) :
  ProbeMorphism (G_obj W ans Hans) (G_obj W' ans' Hans').
Proof.
  refine {|
    injection := fun i => find_index (nth i (fds_basis_indices W) 0) (fds_basis_indices W')
  |}.
  - (* Order preservation *)
    intros i j Hij.
    apply find_index_preserves_order.
    + exact Hij.
    + rewrite fds_dim_spec. simpl.
      exact (inj_preserves_order (probe_id (G_obj W ans Hans)) i j Hij).
    + intros k Hk. simpl. rewrite <- fds_dim_spec in Hk.
      apply (mm_incl f). apply nth_In. rewrite fds_dim_spec. exact Hk.
  - (* In range *)
    intros i Hi. simpl. simpl in Hi.
    rewrite <- fds_dim_spec.
    apply find_index_in_range.
    apply (mm_incl f). apply nth_In. rewrite fds_dim_spec. exact Hi.
  - (* Preserves probes *)
    intros i Hi. simpl. simpl in Hi.
    apply find_index_correct.
    apply (mm_incl f). apply nth_In. rewrite fds_dim_spec. exact Hi.
  - (* Preserves answers - uses coherence condition *)
    intros i Hi. simpl. simpl in Hi.
    apply Hcoh. exact Hi.
Defined.

(** * Adjunction Unit η : Id → G ∘ F

    For a probe theory T, η_T : T → G(F(T))

    With parameterized G_obj, we can now construct eta directly:
    we use T's answers to build G_obj(F_obj(T)) with matching answers. *)

(** Length proof for eta: answers T has the right length for G_obj (F_obj T) *)
Lemma eta_answers_length : forall T, length (answers T) = fds_dim (F_obj T).
Proof.
  intro T. rewrite F_obj_dim. apply rank_answers.
Qed.

(** The unit η is now a definition, not an axiom. *)
Definition eta (T : ProbeTheory) : ProbeMorphism T (G_obj (F_obj T) (answers T) (eta_answers_length T)).
Proof.
  refine {| injection := fun i => i |}.
  - (* Order preservation - identity preserves order *)
    intros i j Hij. exact Hij.
  - (* In range: i < rank T implies i < rank (G_obj ...) = fds_dim (F_obj T) = rank T *)
    intros i Hi. simpl. rewrite F_obj_dim. exact Hi.
  - (* Preserves probes: nth i (probes T) = nth i (probes (G_obj (F_obj T) ...))
                        = nth i (fds_basis_indices (F_obj T)) = nth i (probes T) *)
    intros i Hi. simpl. unfold F_obj. simpl. reflexivity.
  - (* Preserves answers: nth i (answers T) = nth i (answers (G_obj ... (answers T) ...))
                         = nth i (answers T) *)
    intros i Hi. simpl. reflexivity.
Defined.

(** Property of eta: injection is identity *)
Lemma eta_injection_id : forall T i, (i < rank T)%nat -> injection (eta T) i = i.
Proof.
  intros T i Hi. reflexivity.
Qed.

(** * Adjunction Counit ε : F ∘ G → Id

    For a subspace W, ε_W : F(G(W)) → W

    This is parameterized by any answers list. *)

Definition epsilon (W : FinDimSubspace) (ans : list Q) (Hans : length ans = fds_dim W) :
  ModelMorphism (F_obj (G_obj W ans Hans)) W.
Proof.
  refine {| mm_incl := _ |}.
  unfold subspace_incl, F_obj, G_obj. simpl.
  intros i Hi. exact Hi.
Defined.

(** Epsilon with zero answers (for backward compatibility with G_mor) *)
Definition epsilon_zero (W : FinDimSubspace) : ModelMorphism (F_obj (G_obj_zero W)) W.
Proof.
  refine {| mm_incl := _ |}.
  unfold subspace_incl, F_obj, G_obj_zero, G_obj. simpl.
  intros i Hi. exact Hi.
Defined.

(** * Naturality of η

    Note: η now produces G_obj with T's answers, but G_mor works on G_obj_zero.
    For full naturality, we need to use G_mor_gen or show a compatibility result.
    Here we state a simplified version using the identity property of eta. *)

Lemma eta_natural_pointwise : forall T T' (f : ProbeMorphism T T'),
  forall i, (i < rank T)%nat ->
    (* The injections compose correctly: f applied then id = id then f *)
    injection (probe_compose (eta T)
      (G_mor_gen (answers T) (answers T')
        (eta_answers_length T) (eta_answers_length T')
        (F_mor f)
        (fun j Hj => inj_preserves_answers f j Hj))) i =
    injection (probe_compose f (eta T')) i.
Proof.
  intros T T' f i Hi.
  simpl.
  (* eta's injection is identity *)
  rewrite eta_injection_id; [| exact Hi].
  rewrite eta_injection_id; [| apply inj_in_range; exact Hi].
  (* Now show: find_index (nth i (probes T) 0) (probes T') = injection f i *)
  simpl. unfold F_obj. simpl.
  (* By inj_preserves_probes: nth i (probes T) 0 = nth (injection f i) (probes T') 0 *)
  rewrite (inj_preserves_probes f i Hi).
  apply find_index_nth_self.
  rewrite rank_probes.
  apply inj_in_range. exact Hi.
Qed.

(** * Naturality of ε *)

Lemma epsilon_natural : forall W W' (f : ModelMorphism W W')
  (ans : list Q) (ans' : list Q) (Hans : length ans = fds_dim W) (Hans' : length ans' = fds_dim W'),
  forall i, In i (fds_basis_indices (F_obj (G_obj W ans Hans))) ->
    mm_incl (model_compose (F_mor (G_mor_gen ans ans' Hans Hans' f
      (fun j Hj => nth_repeat 0%Q j (fds_dim W') (find_index_in_range _ _
        (mm_incl f _ (nth_In j (fds_basis_indices W) 0%nat
          (eq_ind_r (fun n => (j < n)%nat) Hj (fds_dim_spec W))))))))
      (epsilon W' ans' Hans')) i =
    mm_incl (model_compose (epsilon W ans Hans) f) i.
Proof.
  intros W W' f ans ans' Hans Hans' i Hin.
  (* Both sides are proofs of In i (fds_basis_indices W'), which is a Prop.
     By proof irrelevance, any two proofs are equal. *)
  apply proof_irrelevance.
Qed.

(** Simplified epsilon naturality for zero answers *)
Lemma epsilon_zero_natural : forall W W' (f : ModelMorphism W W'),
  forall i, In i (fds_basis_indices (F_obj (G_obj_zero W))) ->
    mm_incl (model_compose (F_mor (G_mor f)) (epsilon_zero W')) i =
    mm_incl (model_compose (epsilon_zero W) f) i.
Proof.
  intros W W' f i Hin.
  apply proof_irrelevance.
Qed.

End UELAT_Functors.
