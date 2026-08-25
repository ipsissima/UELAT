(** * Presentation.v — v3 approximation-presentation interface (§2)

    Paper reference: Ballús Santacana, "Universal Gluing and Contextual
    Choice: Certificate-Carrying Approximation, Functorial Evidence, and
    Effective Descent", arXiv:2506.22693 v3, Definition 2.1.

    This revision restores the literal manuscript interface at the
    represented-space/checker level.  In particular:
      - CodeF is supplied with a finite-string coding and an effective
        enumeration which is complete for all codes;
      - rhoF has dense range in the ambient completed carrier F;
      - a represented domain D_F is explicit and deltaF is surjective
        onto it;
      - DistCheck is the manuscript's terminating whole-claim checker.

    Normalized spines remain the structural normal form of accepted
    distance proof trees.  Their leaves are now accepted DistCheck
    claims, rather than the stronger and non-manuscript primitive
    DistLeaf interface used by the previous revision. *)

From Stdlib Require Import Reals QArith Qreals Qcanon Lra Lia List.
From UELAT.V3 Require Import EvidenceSyntax.
Local Open Scope R_scope.

Module V3_Presentation.

Import V3_EvidenceSyntax.

Definition Qc2R (q : Qc) : R := Q2R (this q).

Lemma Qc2R_plus : forall p q : Qc, Qc2R (p + q)%Qc = Qc2R p + Qc2R q.
Proof.
  intros p q. unfold Qc2R. rewrite <- Q2R_plus.
  apply Qeq_eqR. apply Qred_correct.
Qed.

Lemma Qc2R_0 : Qc2R 0 = 0.
Proof.
  assert (H : Qc2R (0 + 0)%Qc = Qc2R 0 + Qc2R 0) by apply Qc2R_plus.
  rewrite qc_add_0_l in H. lra.
Qed.

Lemma Qc2R_le : forall p q : Qc, (p <= q)%Qc -> Qc2R p <= Qc2R q.
Proof. intros p q H. unfold Qc2R. apply Qle_Rle. exact H. Qed.

(** A Rocq record function is total/terminating by construction.  The
    finite-string representation below makes the manuscript's
    "effectively enumerable set of finite strings" explicit without
    forcing every concrete model to identify its semantic code type
    definitionally with [list bool]. *)
Record Presentation : Type := {
  (* --- analytic and syntactic carriers --- *)
  CodeF   : Type;
  NameF   : Type;
  F       : Type;
  distF   : F -> F -> R;

  (* --- pseudo-metric laws on the completion carrier --- *)
  distF_nonneg   : forall a b : F, 0 <= distF a b;
  distF_self0    : forall a : F, distF a a = 0;
  distF_sym      : forall a b : F, distF a b = distF b a;
  distF_triangle : forall a b c : F, distF a c <= distF a b + distF b c;

  (* --- effective finite-string code presentation, Def. 2.1(1) --- *)
  code_encode : CodeF -> list bool;
  code_decode : list bool -> option CodeF;
  code_decode_encode : forall p : CodeF, code_decode (code_encode p) = Some p;
  code_enum : nat -> option CodeF;
  code_enum_complete : forall p : CodeF, exists n : nat, code_enum n = Some p;

  (* --- decoders and density, Def. 2.1(1) --- *)
  rhoF : CodeF -> F;
  rhoF_dense : forall (x : F) (eps : R),
      0 < eps -> exists p : CodeF, distF x (rhoF p) < eps;

  (* --- represented domain of named points, Def. 2.1(2) --- *)
  D_F : F -> Prop;
  deltaF : NameF -> F;
  deltaF_in_domain : forall nu : NameF, D_F (deltaF nu);
  deltaF_surjective : forall x : F, D_F x -> exists nu : NameF, deltaF nu = x;

  (* --- canonical names, Def. 2.1(3) --- *)
  iotaF : CodeF -> NameF;
  canonical_name_ok : forall p : CodeF, deltaF (iotaF p) = rhoF p;

  (* --- finite code size, Def. 2.1(4) --- *)
  code_size : CodeF -> nat;
  code_size_encoding : forall p : CodeF, code_size p = length (code_encode p);

  (* --- terminating checkers, Def. 2.1(5)-(6) --- *)
  AppCheck : NameF -> CodeF -> Qc -> list bool -> bool;
  DistCheck : NameF -> NameF -> Qc -> list bool -> bool;

  (* --- checker soundness --- *)
  AppCheck_sound :
    forall (nu : NameF) (p : CodeF) (q : Qc) (V : list bool),
      AppCheck nu p q V = true -> distF (deltaF nu) (rhoF p) <= Qc2R q;
  DistCheck_sound :
    forall (nu mu : NameF) (q : Qc) (W : list bool),
      DistCheck nu mu q W = true -> distF (deltaF nu) (deltaF mu) <= Qc2R q
}.

(** Normalized distance evidence over the manuscript's DistCheck. *)
Definition PSpine (P : Presentation) (a b : NameF P) : Type :=
  Spine (DistCheck P) a b.

(** A flattened spine of accepted DistCheck leaves is sound by repeated
    triangle inequality.  This is the semantic bridge from the finite
    proof-tree normal form required in Def. 2.1 to the analytic metric. *)
Theorem spine_sound :
  forall (P : Presentation) (a b : NameF P) (W : PSpine P a b),
    distF P (deltaF P a) (deltaF P b) <= Qc2R (sp_bound W).
Proof.
  intros P a b W. induction W as [x | x m y s rest IH].
  - simpl. rewrite distF_self0, Qc2R_0. apply Rle_refl.
  - simpl. rewrite Qc2R_plus.
    eapply Rle_trans; [apply distF_triangle with (b := deltaF P m) |].
    apply Rplus_le_compat; [| exact IH].
    eapply DistCheck_sound. exact (ps_ok s).
Qed.

Definition certified_dist (P : Presentation) (nu mu : NameF P) (q : Qc) : Prop :=
  exists W : PSpine P nu mu, (sp_bound W <= q)%Qc.

Theorem certified_dist_sound :
  forall (P : Presentation) (nu mu : NameF P) (q : Qc),
    certified_dist P nu mu q ->
    distF P (deltaF P nu) (deltaF P mu) <= Qc2R q.
Proof.
  intros P nu mu q [W Hle].
  eapply Rle_trans; [apply spine_sound | apply Qc2R_le; exact Hle].
Qed.

Theorem certified_dist_refl :
  forall (P : Presentation) (nu : NameF P), certified_dist P nu nu 0.
Proof.
  intros P nu. exists (sp_nil nu). simpl. apply Qcle_refl.
Qed.

Theorem certified_dist_trans :
  forall (P : Presentation) (nu mu xi : NameF P) (q r : Qc),
    certified_dist P nu mu q ->
    certified_dist P mu xi r ->
    certified_dist P nu xi (q + r).
Proof.
  intros P nu mu xi q r [W1 H1] [W2 H2].
  exists (sp_app W1 W2). rewrite sp_bound_app.
  apply Qcplus_le_compat; assumption.
Qed.

Section WithPresentation.
Variable P : Presentation.

Lemma canonical_name_distF_zero : forall p,
  distF P (deltaF P (iotaF P p)) (rhoF P p) = 0.
Proof. intro p. rewrite canonical_name_ok. apply distF_self0. Qed.

Lemma canonical_name_in_domain : forall p,
  D_F P (rhoF P p).
Proof.
  intro p. rewrite <- canonical_name_ok. apply deltaF_in_domain.
Qed.

Lemma AppCheck_bound_nonneg :
  forall nu p q V, AppCheck P nu p q V = true -> 0 <= Qc2R q.
Proof.
  intros nu p q V H.
  eapply Rle_trans; [apply distF_nonneg | eapply AppCheck_sound; exact H].
Qed.

End WithPresentation.

(** Correspondence note.

    The fields above now encode items (1)--(6) of manuscript Def. 2.1:
    finite-string/effective code enumeration, dense decoding, represented
    domain and surjective naming, canonical names, code size, and the two
    terminating sound checkers.  The evidence-language closure operations
    listed in the paragraph following item (6) live in [Evidence] and
    [EvidenceClosureV3], while [PSpine] is the required flattened strict
    normal form.  A final status promotion must therefore audit those
    modules jointly rather than treating [Presentation] alone as the whole
    post-item-(6) closure paragraph. *)

End V3_Presentation.
