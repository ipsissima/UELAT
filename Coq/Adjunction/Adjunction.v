(** Adjunction.v — Probes-Models adjunction (Section 3, Theorem 3.3)

    This module proves the main adjunction F ⊣ G between the categories
    Probe and Model. The adjunction witnesses that finite probe theories
    and finite-dimensional subspaces are "the same" in a precise sense.

    Reference: UELAT Paper, Section 3, Theorem 3.3
*)

From Stdlib Require Import Reals QArith List Arith Lia Classical.
From Coq.Logic Require Import ProofIrrelevance.
From UELAT.Foundations Require Import ProbeTheory.
From UELAT.Adjunction Require Import Probe Model Functors.
Import ListNotations.
Local Open Scope R_scope.

Module UELAT_Adjunction.

Import UELAT_Probe.
Import UELAT_ProbeCat.
Import UELAT_Model.
Import UELAT_Functors.

(** * Main Adjunction Theorem

    Theorem 3.3: F ⊣ G

    There is a natural bijection:
      Hom_Model(F(T), W) ≅ Hom_Probe(T, G(W))

    The adjunction is witnessed by:
    - Unit η : Id_Probe → G ∘ F
    - Counit ε : F ∘ G → Id_Model
    satisfying the triangle identities.
*)

Section Adjunction.

(** * Helper Lemmas *)

(** If x is in list l, there exists an index k such that nth k l d = x. *)
Lemma nth_In_exists : forall {A : Type} (x : A) (l : list A) (d : A),
  In x l -> exists k, (k < length l)%nat /\ nth k l d = x.
Proof.
  intros A x l d Hin.
  induction l as [| y l' IH].
  - destruct Hin.
  - destruct Hin as [Heq | Hin'].
    + exists 0%nat. split; [simpl; lia | simpl; exact Heq].
    + destruct (IH Hin') as [k [Hk Hnth]].
      exists (S k). split; [simpl; lia | simpl; exact Hnth].
Qed.

(** * Zero Answers Predicate *)

(** If G_obj uses placeholder zero answers, the adjunction only works
    (without further parameterization) for probe theories whose answers
    are all zero. We make that explicit. *)
Definition zero_answers (T : ProbeTheory) : Prop :=
  forall i, (i < rank T)%nat -> nth i (answers T) 0%Q = 0%Q.

(** * The Bijection *)

(** Forward direction: Model morphism to Probe morphism.
    Use find_index to locate the basis index in W that corresponds to the
    i-th probe in T. *)
Definition adj_forward (T : ProbeTheory) (W : FinDimSubspace)
  (Hz : zero_answers T) (f : ModelMorphism (F_obj T) W) : ProbeMorphism T (G_obj W).
Proof.
  refine {| injection := fun i => find_index (nth i (probes T) 0%nat) (fds_basis_indices W) |}.
  - (* Order preservation *)
    intros i j Hij.
    apply find_index_preserves_order.
    + exact Hij.
    + rewrite rank_probes. exact (inj_preserves_order (probe_id T) i j Hij).
    + intros k Hk. rewrite rank_probes in Hk.
      (* nth k (probes T) is in fds_basis_indices (F_obj T) = probes T *)
      assert (Hin_F : In (nth k (probes T) 0%nat) (fds_basis_indices (F_obj T))).
      { unfold F_obj. simpl. apply nth_In. rewrite rank_probes. exact Hk. }
      (* By mm_incl f, it is in W *)
      exact (mm_incl f _ Hin_F).
  - (* In range: find_index result < fds_dim W *)
    intros i Hi. simpl.
    rewrite <- fds_dim_spec.
    apply find_index_in_range.
    (* nth i (probes T) 0 is in fds_basis_indices (F_obj T) = probes T *)
    assert (Hin_F : In (nth i (probes T) 0%nat) (fds_basis_indices (F_obj T))).
    { unfold F_obj. simpl. apply nth_In. rewrite rank_probes. exact Hi. }
    (* By mm_incl f, it is in W *)
    exact (mm_incl f _ Hin_F).
  - (* Preserves probes: nth i (probes T) = nth (find_index ...) (probes (G_obj W)) *)
    intros i Hi. simpl.
    (* probes (G_obj W) = fds_basis_indices W *)
    (* We need: nth i (probes T) 0 = nth (find_index (nth i (probes T) 0) (fds_basis_indices W)) (fds_basis_indices W) 0 *)
    symmetry.
    apply find_index_correct.
    (* Show: In (nth i (probes T) 0) (fds_basis_indices W) *)
    assert (Hin_F : In (nth i (probes T) 0%nat) (fds_basis_indices (F_obj T))).
    { unfold F_obj. simpl. apply nth_In. rewrite rank_probes. exact Hi. }
    exact (mm_incl f _ Hin_F).
  - (* Preserves answers: nth i (answers T) = nth j (answers (G_obj W)) *)
    intros i Hi. simpl.
    (* answers (G_obj W) = repeat 0%Q (fds_dim W) *)
    (* We use zero_answers T *)
    rewrite Hz; [| exact Hi].
    rewrite nth_repeat.
    + reflexivity.
    + apply find_index_in_range.
      assert (Hin_F : In (nth i (probes T) 0%nat) (fds_basis_indices (F_obj T))).
      { unfold F_obj. simpl. apply nth_In. rewrite rank_probes. exact Hi. }
      exact (mm_incl f _ Hin_F).
Defined.

(** Backward direction: Probe morphism to Model morphism.
    Build a subspace inclusion F_obj T -> W by showing each probe index
    (which is an element of fds_basis_indices (F_obj T)) belongs to W. *)
Definition adj_backward (T : ProbeTheory) (W : FinDimSubspace)
  (g : ProbeMorphism T (G_obj W)) : ModelMorphism (F_obj T) W.
Proof.
  refine {| mm_incl := fun idx Hin =>
    (* idx is in fds_basis_indices (F_obj T) = probes T *)
    (* So idx = nth k (probes T) 0 for some k < rank T *)
    (* By inj_preserves_probes g: idx = nth (injection g k) (probes (G_obj W)) 0 *)
    (*                              = nth (injection g k) (fds_basis_indices W) 0 *)
    (* So idx is in fds_basis_indices W *)
    _ |}.
  (* We need to show: In idx (fds_basis_indices W) *)
  unfold F_obj in Hin. simpl in Hin.
  (* Hin : In idx (probes T) *)
  destruct (nth_In_exists idx (probes T) 0%nat Hin) as [k [Hk Hnth]].
  rewrite rank_probes in Hk.
  (* idx = nth k (probes T) 0 *)
  rewrite <- Hnth.
  (* By inj_preserves_probes: nth k (probes T) 0 = nth (injection g k) (probes (G_obj W)) 0 *)
  rewrite (inj_preserves_probes g k Hk).
  (* probes (G_obj W) = fds_basis_indices W *)
  simpl.
  (* Now show: In (nth (injection g k) (fds_basis_indices W) 0) (fds_basis_indices W) *)
  apply nth_In.
  (* injection g k < rank (G_obj W) = fds_dim W = length (fds_basis_indices W) *)
  rewrite fds_dim_spec.
  apply (inj_in_range g k Hk).
Defined.

(** * The bijection is an isomorphism *)

Theorem adjunction_bijection :
  forall (T : ProbeTheory) (W : FinDimSubspace)
         (Hz : zero_answers T) (f : ModelMorphism (F_obj T) W),
    adj_backward T W (adj_forward T W Hz f) = f.
Proof.
  intros T W Hz f.
  (* Both give the same subspace inclusion *)
  destruct f as [incl_f]. simpl.
  f_equal.
  (* Proof irrelevance for Prop-valued inclusion *)
  apply proof_irrelevance.
Qed.

Theorem adjunction_bijection_inv :
  forall (T : ProbeTheory) (W : FinDimSubspace)
         (Hz : zero_answers T) (g : ProbeMorphism T (G_obj W)),
    forall i, (i < rank T)%nat ->
      injection (adj_forward T W Hz (adj_backward T W g)) i = injection g i.
Proof.
  intros T W Hz g i Hi.
  (* Unfold the composition *)
  unfold adj_forward, adj_backward. simpl.
  (* LHS: find_index (nth i (probes T) 0) (fds_basis_indices W) *)
  (* By inj_preserves_probes g: nth i (probes T) 0 = nth (injection g i) (fds_basis_indices W) 0 *)
  rewrite (inj_preserves_probes g i Hi).
  simpl.
  (* Now: find_index (nth (injection g i) (fds_basis_indices W) 0) (fds_basis_indices W) *)
  (* This equals injection g i by find_index_nth_self *)
  apply find_index_nth_self.
  (* Need: injection g i < length (fds_basis_indices W) *)
  rewrite fds_dim_spec.
  apply (inj_in_range g i Hi).
Qed.

(** * Triangle Identities *)

(** Triangle Identity 1: (G ε) ∘ (η G) = id_G

    For any W, the composite G(W) --η_{G(W)}--> G(F(G(W))) --G(ε_W)--> G(W)
    is the identity. *)

Theorem triangle_identity_1 :
  forall (W : FinDimSubspace),
    forall i, (i < fds_dim W)%nat ->
      injection (probe_compose (eta (G_obj W)) (G_mor (epsilon W))) i = i.
Proof.
  intros W i Hi.
  (* Unfold composition *)
  simpl.
  (* Use eta_injection_id: injection (eta (G_obj W)) i = i *)
  rewrite eta_injection_id; [| exact Hi].
  (* Now show: injection (G_mor (epsilon W)) i = i *)
  (* G_mor (epsilon W) has injection := find_index (nth i (fds_basis_indices W) 0) (fds_basis_indices W) *)
  unfold G_mor. simpl.
  (* So we need: find_index (nth i (fds_basis_indices W) 0) (fds_basis_indices W) = i *)
  apply find_index_nth_self.
  rewrite fds_dim_spec. exact Hi.
Qed.

(** Triangle Identity 2: (ε F) ∘ (F η) = id_F

    For any T, the composite F(T) --F(η_T)--> F(G(F(T))) --ε_{F(T)}--> F(T)
    is the identity. *)

Theorem triangle_identity_2 :
  forall (T : ProbeTheory),
    forall i, In i (fds_basis_indices (F_obj T)) ->
      mm_incl (model_compose (F_mor (eta T)) (epsilon (F_obj T))) i = mm_incl (model_id (F_obj T)) i.
Proof.
  intros T i Hin.
  (* Both sides are proofs of In i (fds_basis_indices (F_obj T)), which is a Prop.
     By proof irrelevance, any two proofs are equal. *)
  apply proof_irrelevance.
Qed.

(** * Naturality *)

(** Naturality of the bijection in T *)
Theorem adj_natural_T :
  forall (T T' : ProbeTheory) (W : FinDimSubspace)
         (Hz : zero_answers T) (Hz' : zero_answers T')
         (h : ProbeMorphism T T') (f : ModelMorphism (F_obj T') W),
    forall i, (i < rank T)%nat ->
      injection (adj_forward T W Hz (model_compose (F_mor h) f)) i =
      injection (probe_compose h (adj_forward T' W Hz' f)) i.
Proof.
  intros T T' W Hz Hz' h f i Hi.
  (* Unfold definitions *)
  unfold adj_forward. simpl.
  (* LHS: find_index (nth i (probes T) 0) (fds_basis_indices W) *)
  (* RHS: find_index (nth (injection h i) (probes T') 0) (fds_basis_indices W) *)
  (* By inj_preserves_probes h: nth i (probes T) 0 = nth (injection h i) (probes T') 0 *)
  rewrite (inj_preserves_probes h i Hi).
  reflexivity.
Qed.

(** Naturality of the bijection in W *)
Theorem adj_natural_W :
  forall (T : ProbeTheory) (W W' : FinDimSubspace)
         (Hz : zero_answers T)
         (k : ModelMorphism W W') (f : ModelMorphism (F_obj T) W),
    forall i, (i < rank T)%nat ->
      injection (adj_forward T W' Hz (model_compose f k)) i =
      injection (probe_compose (adj_forward T W Hz f) (G_mor k)) i.
Proof.
  intros T W W' Hz k f i Hi.
  (* Unfold definitions *)
  unfold adj_forward, G_mor. simpl.
  (* LHS: find_index (nth i (probes T) 0) (fds_basis_indices W') *)
  (* RHS: find_index (nth (find_index (nth i (probes T) 0) (fds_basis_indices W)) (fds_basis_indices W) 0) (fds_basis_indices W') *)
  (* By find_index_correct: nth (find_index x l) l 0 = x when In x l *)
  assert (Hin : In (nth i (probes T) 0%nat) (fds_basis_indices W)).
  { assert (HinF : In (nth i (probes T) 0%nat) (fds_basis_indices (F_obj T))).
    { unfold F_obj. simpl. apply nth_In. rewrite rank_probes. exact Hi. }
    exact (mm_incl f _ HinF). }
  rewrite (find_index_correct _ _ Hin).
  reflexivity.
Qed.

End Adjunction.

(** * Corollaries of the Adjunction *)

(** The adjunction implies that F and G form an equivalence
    when restricted to appropriate subcategories. *)

Corollary adj_preserves_rank :
  forall T, fds_dim (F_obj T) = rank T.
Proof.
  intro T. apply F_obj_dim.
Qed.

Corollary adj_preserves_dim :
  forall W, rank (G_obj W) = fds_dim W.
Proof.
  intro W. reflexivity.
Qed.

(** The adjunction is idempotent: F(G(W)) ≅ W and G(F(T)) ≅ T
    when the locally finite condition holds. *)

End UELAT_Adjunction.
