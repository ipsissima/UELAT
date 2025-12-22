(** Functors.v — F and G functors between Probe and Model (Section 3)

    This module defines the functors F : Probe → Model and G : Model → Probe
    that form the adjunction F ⊣ G.

    Reference: UELAT Paper, Section 3
*)

From Coq Require Import Reals QArith List Arith Lia.
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
  intro T. reflexivity.
Qed.

(** F preserves composition *)
Lemma F_compose : forall T1 T2 T3 (f : ProbeMorphism T1 T2) (g : ProbeMorphism T2 T3),
  forall i, In i (fds_basis_indices (F_obj T1)) ->
    mm_incl (F_mor (probe_compose f g)) i =
    mm_incl (model_compose (F_mor f) (F_mor g)) i.
Proof.
  intros T1 T2 T3 f g i Hi.
  reflexivity.
Qed.

(** * Functor G : Model → Probe

    G(W) = (dim W, basis_indices W, evaluation at reference points)

    Takes a subspace and returns a probe theory with probes
    corresponding to the basis elements spanning W. *)

(** For G, we need a way to compute "answers" from a subspace.
    This requires evaluation data. For now, we use a placeholder. *)

Program Definition G_obj (W : FinDimSubspace) : ProbeTheory := {|
  rank := fds_dim W;
  probes := fds_basis_indices W;
  answers := repeat 0%Q (fds_dim W)
|}.
Next Obligation.
  symmetry. apply fds_dim_spec.
Qed.
Next Obligation.
  apply repeat_length.
Qed.

Definition G_mor {W W' : FinDimSubspace} (f : ModelMorphism W W') :
  ProbeMorphism (G_obj W) (G_obj W').
Proof.
  (* Need to find how each probe of G(W) maps into G(W') *)
  (* This is complex because we need the index, not just membership *)
  refine {| injection := fun i =>
    (* Find the position of (nth i probes_W) in probes_W' *)
    let p := nth i (fds_basis_indices W) 0%nat in
    (* Find index of p in W' *)
    match find (fun j => Nat.eqb (nth j (fds_basis_indices W') 0%nat) p)
               (seq 0 (fds_dim W')) with
    | Some j => j
    | None => 0  (* Should not happen if f is valid *)
    end
  |}.
  - (* Order preservation - complex, needs careful proof *)
    intros i j Hij.
    (* This requires that the inclusion respects ordering *)
    admit.
  - (* Range check *)
    intros i Hi.
    simpl in *. simpl.
    (* Need to show the found index is in range *)
    admit.
  - (* Probe preservation *)
    intros i Hi.
    simpl in *.
    (* The probe at position i in W equals the probe at injection i in W' *)
    admit.
  - (* Answer preservation *)
    intros i Hi.
    simpl in *.
    (* Both use 0%Q as placeholder *)
    rewrite !nth_repeat. reflexivity.
Admitted.

(** * Adjunction Unit η : Id → G ∘ F

    For a probe theory T, η_T : T → G(F(T)) *)

Definition eta (T : ProbeTheory) : ProbeMorphism T (G_obj (F_obj T)).
Proof.
  refine {| injection := fun i => i |}.
  - intros i j Hij. exact Hij.
  - intros i Hi. simpl. rewrite <- rank_probes. exact Hi.
  - intros i Hi. simpl. reflexivity.
  - intros i Hi. simpl.
    rewrite nth_repeat. reflexivity.
Defined.

(** * Adjunction Counit ε : F ∘ G → Id

    For a subspace W, ε_W : F(G(W)) → W *)

Definition epsilon (W : FinDimSubspace) : ModelMorphism (F_obj (G_obj W)) W.
Proof.
  refine {| mm_incl := _ |}.
  unfold subspace_incl, F_obj, G_obj. simpl.
  intros i Hi. exact Hi.
Defined.

(** * Naturality of η *)

Lemma eta_natural : forall T T' (f : ProbeMorphism T T'),
  forall i, (i < rank T)%nat ->
    injection (probe_compose (eta T) (G_mor (F_mor f))) i =
    injection (probe_compose f (eta T')) i.
Proof.
  intros T T' f i Hi.
  simpl. reflexivity.
Qed.

(** * Naturality of ε *)

Lemma epsilon_natural : forall W W' (f : ModelMorphism W W'),
  forall i, In i (fds_basis_indices (F_obj (G_obj W))) ->
    mm_incl (model_compose (F_mor (G_mor f)) (epsilon W')) i =
    mm_incl (model_compose (epsilon W) f) i.
Proof.
  intros W W' f i Hi.
  reflexivity.
Qed.

End UELAT_Functors.
