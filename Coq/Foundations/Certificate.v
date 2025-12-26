(** Certificate.v — Inductive certificate type (Appendix A of paper)

    This module defines the inductive grammar of certificates as first-class
    mathematical objects. Certificates serve as witnesses for ε-approximation
    claims, enabling machine-checkable proofs of approximation bounds.

    Reference: UELAT Paper, Appendix A
*)

From Coq Require Import Reals QArith List Arith Lia Lra.
Import ListNotations.
Local Open Scope R_scope.

Module UELAT_Certificate.

(** * Tail Bound Proof Types

    Different proof strategies for bounding the tail of a series expansion.
    Each constructor carries the data needed to verify the bound. *)

Inductive TailProof : Type :=
  | Parseval : R -> TailProof
      (** Parseval identity: norm bound for orthonormal expansions *)
  | Bessel : R -> TailProof
      (** Bessel inequality: basis constant for general frames *)
  | IntegralTest : (nat -> R) -> TailProof
      (** Integral test: decay function a(n) with Σa(n) convergent *)
  | GeometricDecay : R -> R -> TailProof
      (** |a_n| ≤ C * r^n for some C > 0 and 0 < r < 1 *).

(** * Compatibility Data for Gluing

    When gluing local certificates across overlapping patches, we need
    to verify compatibility on the overlaps. *)

Record CompatData := {
  overlap_indices : list (nat * nat);
    (** Pairs (i,j) of overlapping patch indices *)
  deltas : list R;
    (** Tolerance δ_{ij} for each overlap *)
  compat_witness : list nat
    (** Witness indices for compatibility verification *)
}.

Definition empty_compat : CompatData := {|
  overlap_indices := [];
  deltas := [];
  compat_witness := []
|}.

(** * Partition of Unity Data

    A partition of unity {ρ_i}_{i=1}^M subordinate to a cover {U_i}. *)

Record PartitionData := {
  num_patches : nat;
    (** Number M of patches in the cover *)
  lipschitz_bounds : list R;
    (** Lipschitz constant of each ρ_i *)
  support_data : list (R * R)
    (** Support interval (a_i, b_i) of each ρ_i *)
}.

Definition trivial_partition : PartitionData := {|
  num_patches := 1;
  lipschitz_bounds := [0];
  support_data := [(0, 1)]
|}.

(** * Main Certificate Inductive Type

    The grammar of certificates, as defined in Appendix A.
    Each constructor corresponds to a different proof strategy. *)

Inductive Cert : Type :=
  | CoeffCert :
      forall (n : nat),                  (** rank / degree *)
      list nat ->                        (** probe indices from countable set P *)
      list Q ->                          (** rational coefficients *)
      R ->                               (** claimed error bound ε *)
      Cert
      (** Finite rank certificate: g = Σ_{j=1}^n c_j b_{φ_j} with ‖f - g‖ < ε *)

  | TailBoundCert :
      nat ->                             (** truncation index N *)
      R ->                               (** tail estimate Σ_{n>N} |a_n|^2 *)
      TailProof ->                       (** proof witness for the tail bound *)
      Cert
      (** Tail bound certificate for series truncation error *)

  | GlueCert :
      nat ->                             (** number of patches M *)
      list Cert ->                       (** local certificates {C_i} *)
      CompatData ->                      (** compatibility data {D_{ij}} *)
      PartitionData ->                   (** partition of unity data *)
      Cert
      (** Glued certificate from local data (Theorem 9.3) *)

  | ModulusCert :
      (Q -> nat) ->                      (** modulus function N : Q_{>0} → ℕ *)
      (Q -> Cert) ->                     (** witness certificates *)
      Cert
      (** Modulus-indexed family for limit certificates (Theorem 7.1) *)

  | ComposeCert :
      Cert -> Cert ->                    (** two certificates to compose *)
      Cert
      (** Composition of certificates (Lemma 5.2) *).

(** * Certificate Size Function

    Computes the size |C| of a certificate, counting the total
    number of coefficients and auxiliary data. *)

Fixpoint cert_size (c : Cert) : nat :=
  match c with
  | CoeffCert n _ _ _ => n
  | TailBoundCert N _ _ => N
  | GlueCert M locals _ _ =>
      M + fold_right Nat.add O (map cert_size locals)
  | ModulusCert _ _ => 1%nat  (** Representative size; actual size is query-dependent *)
  | ComposeCert c1 c2 => cert_size c1 + cert_size c2
  end.

(** * Certificate Error Bound Extraction *)

Fixpoint cert_error (c : Cert) : R :=
  match c with
  | CoeffCert _ _ _ eps => eps
  | TailBoundCert _ tail_est _ => sqrt tail_est
  | GlueCert _ locals _ _ =>
      fold_right Rmax 0 (map cert_error locals)
  | ModulusCert _ _ => 0  (** Error is query-dependent *)
  | ComposeCert c1 c2 => cert_error c1 + cert_error c2
  end.

(** * Certificate Well-formedness Predicate *)

(* Inductive predicate avoids termination issues with nested recursion *)
Inductive cert_wf : Cert -> Prop :=
  | wf_coeff : forall n idxs coeffs eps,
      length idxs = n -> length coeffs = n -> eps >= 0 ->
      cert_wf (CoeffCert n idxs coeffs eps)
  | wf_tail : forall N tail_est proof,
      (N > 0)%nat -> tail_est >= 0 ->
      cert_wf (TailBoundCert N tail_est proof)
  | wf_glue : forall M locals compat part,
      (M > 0)%nat ->
      length locals = M ->
      Forall cert_wf locals ->
      cert_wf (GlueCert M locals compat part)
  | wf_modulus : forall f g,
      cert_wf (ModulusCert f g)
  | wf_compose : forall c1 c2,
      cert_wf c1 -> cert_wf c2 ->
      cert_wf (ComposeCert c1 c2).

(** * Auxiliary Lemmas *)

Lemma cert_size_nonneg : forall c, (cert_size c >= 0)%nat.
Proof.
  intro c; induction c; simpl; lia.
Qed.

Lemma fold_Rmax_nonneg : forall l,
  fold_right Rmax 0 l >= 0.
Proof.
  intro l; induction l as [|a l' IH]; simpl.
  - lra.
  - apply Rle_ge.
    apply Rle_trans with (fold_right Rmax 0 l').
    + apply Rge_le. lra.
    + apply Rmax_r.
Qed.

Lemma cert_error_nonneg : forall c, cert_wf c -> cert_error c >= 0.
Proof.
  intros c Hwf.
  induction Hwf; simpl.
  - (* CoeffCert *) exact H1.
  - (* TailBoundCert *) 
    apply Rle_ge. apply sqrt_pos.
  - (* GlueCert *) apply fold_Rmax_nonneg.
  - (* ModulusCert *) lra.
  - (* ComposeCert *) lra.
Qed.

(** * CoeffCert Constructors and Accessors *)

Definition mk_coeff_cert (n : nat) (idxs : list nat) (coeffs : list Q) (eps : R)
  (Hidxs : length idxs = n) (Hcoeffs : length coeffs = n) (Heps : eps >= 0)
  : Cert := CoeffCert n idxs coeffs eps.

Definition coeff_cert_rank (c : Cert) : nat :=
  match c with
  | CoeffCert n _ _ _ => n
  | _ => 0
  end.

Definition coeff_cert_indices (c : Cert) : list nat :=
  match c with
  | CoeffCert _ idxs _ _ => idxs
  | _ => []
  end.

Definition coeff_cert_coeffs (c : Cert) : list Q :=
  match c with
  | CoeffCert _ _ coeffs _ => coeffs
  | _ => []
  end.

(** * Certificate Refinement

    c1 refines c2 if c1 provides a tighter bound with at least as much detail. *)

Definition cert_refines (c1 c2 : Cert) : Prop :=
  cert_error c1 <= cert_error c2.

Lemma cert_refines_refl : forall c, cert_refines c c.
Proof.
  intro c; unfold cert_refines; lra.
Qed.

Lemma cert_refines_trans : forall c1 c2 c3,
  cert_refines c1 c2 -> cert_refines c2 c3 -> cert_refines c1 c3.
Proof.
  intros c1 c2 c3 H12 H23; unfold cert_refines in *; lra.
Qed.

End UELAT_Certificate.
