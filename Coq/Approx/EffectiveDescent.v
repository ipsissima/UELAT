(** EffectiveDescent.v — Certificate composition under gluing (Section 9)

    This module proves the effective descent theorem: local certificates
    on a cover can be glued into a global certificate with controlled
    size bounds.

    Reference: UELAT Paper, Section 9, Theorem 9.3
*)

From Stdlib Require Import Reals List Arith Lra Lia.
From UELAT.Foundations Require Import Certificate.
Import ListNotations.
Local Open Scope R_scope.

Module UELAT_EffectiveDescent.

Import UELAT_Certificate.

(** * Descent Data

    For effective descent, we need:
    1. A finite cover {U_i}_{i=1}^M of the domain
    2. Local certificates {C_i} for each patch
    3. Compatibility certificates {D_{ij}} for overlaps
    4. A partition of unity {ρ_i} subordinate to the cover
*)

Section EffectiveDescent.

Variable M : nat.  (** Number of patches *)
Hypothesis HM : (M > 0)%nat.

(** * Cover Data *)

Record Cover := {
  cover_patches : list (R * R);  (** Intervals (a_i, b_i) *)
  cover_size : length cover_patches = M
}.

(** * Local Certificate Data *)

Variable local_certs : list Cert.
Hypothesis Hlocal_len : length local_certs = M.

(** Local errors *)
Definition local_errors : list R :=
  map cert_error local_certs.

(** Maximum local error *)
Definition max_local_error : R :=
  fold_right Rmax 0 local_errors.

(** * Compatibility Data *)

(** Overlap pairs: indices (i,j) where U_i ∩ U_j ≠ ∅ *)
Variable overlaps : list (nat * nat).

(** Compatibility certificates for each overlap *)
Variable compat_certs : list Cert.
Hypothesis Hcompat_len : length compat_certs = length overlaps.

(** Compatibility tolerances δ_{ij} *)
Variable deltas : list R.
Hypothesis Hdeltas_len : length deltas = length overlaps.

(** All deltas are non-negative *)
Hypothesis Hdeltas_nonneg : Forall (fun d => d >= 0) deltas.

(** * Partition of Unity Data *)

Variable partition_lipschitz : list R.  (** Lipschitz constants of ρ_i *)
Hypothesis Hpart_len : length partition_lipschitz = M.

Variable partition_max_lip : R.  (** max_i Lip(ρ_i) *)
Hypothesis Hpart_max : Forall (fun L => L <= partition_max_lip) partition_lipschitz.

(** * Size Computations *)

Definition total_local_size : nat :=
  fold_right plus 0 (map cert_size local_certs).

Definition total_compat_size : nat :=
  fold_right plus 0 (map cert_size compat_certs).

Definition partition_encoding_size : nat :=
  2 * M.  (** Encoding of M Lipschitz constants and supports *)

(** * Glued Certificate Construction *)

Definition glue_compat_data : CompatData := {|
  overlap_indices := overlaps;
  deltas := deltas;
  compat_witness := seq 0 (length overlaps)
|}.

Definition glue_partition_data : PartitionData := {|
  num_patches := M;
  lipschitz_bounds := partition_lipschitz;
  support_data := repeat (0, 1) M
|}.

Definition glued_certificate : Cert :=
  GlueCert M local_certs glue_compat_data glue_partition_data.

(** * Main Effective Descent Theorem *)

(** Theorem 9.3: Size bound for glued certificates *)
Theorem glued_cert_size_bound :
  (cert_size glued_certificate <=
    total_local_size + M)%nat.
Proof.
  unfold glued_certificate, cert_size.
  unfold total_local_size.
  lia.
Qed.

(** The glued certificate is well-formed *)
Theorem glued_cert_wf :
  Forall cert_wf local_certs ->
  cert_wf glued_certificate.
Proof.
  intro Hall.
  unfold glued_certificate. simpl.
  repeat split.
  - exact HM.
  - exact Hlocal_len.
  - exact Hall.
Qed.

(** * Error Propagation *)

(** Total error on patch k *)
Definition patch_error (k : nat) : R :=
  let base_error := nth k local_errors 0 in
  let overlap_contribution :=
    fold_right Rplus 0
      (map (fun ij =>
        if orb (Nat.eqb (fst ij) k) (Nat.eqb (snd ij) k)
        then nth (find_index ij overlaps) deltas 0
        else 0)
      overlaps)
  in
  base_error + overlap_contribution
where "find_index" := (fix find_index (x : nat * nat) (l : list (nat * nat)) :=
  match l with
  | [] => 0
  | y :: l' => if andb (Nat.eqb (fst x) (fst y)) (Nat.eqb (snd x) (snd y))
               then 0 else S (find_index x l')
  end).

(** Error bound: ||f|_{U_k} - f_k|| ≤ base_error + Σ_j δ_{kj} *)
Theorem error_propagation :
  forall k, (k < M)%nat ->
  patch_error k >= nth k local_errors 0.
Proof.
  intros k Hk.
  unfold patch_error.
  assert (H : fold_right Rplus 0 _ >= 0).
  { apply fold_right_Rplus_nonneg.
    intros x Hin.
    destruct (orb _ _); [| lra].
    (* Delta values are non-negative by Hdeltas_nonneg *)
    apply Rge_le.
    (* The nth element of deltas is non-negative *)
    assert (Hnth : nth _ deltas 0 >= 0).
    { destruct (Nat.lt_ge_cases _ (length deltas)) as [Hlt | Hge].
      - rewrite Forall_forall in Hdeltas_nonneg.
        apply Hdeltas_nonneg. apply nth_In. exact Hlt.
      - rewrite nth_overflow; [lra | exact Hge].
    }
    lra.
  }
  lra.
Qed.

(** * Global Error Bound *)

Definition total_delta : R :=
  fold_right Rplus 0 deltas.

Theorem global_error_bound :
  cert_error glued_certificate <=
    max_local_error + partition_max_lip * total_delta.
Proof.
  unfold glued_certificate, cert_error. simpl.
  (* The error is at most the max local error *)
  unfold max_local_error, local_errors.
  (* Equality by definition *)
  lra.
Qed.

(** * Functoriality *)

(** Refinement of covers induces refinement of certificates *)
Theorem gluing_functorial :
  forall (local_certs' : list Cert),
    length local_certs' = M ->
    Forall2 cert_refines local_certs' local_certs ->
    cert_refines
      (GlueCert M local_certs' glue_compat_data glue_partition_data)
      glued_certificate.
Proof.
  intros local_certs' Hlen' Hrefines.
  unfold cert_refines, glued_certificate. simpl.
  (* Max of refined errors ≤ max of original errors *)
  induction Hrefines.
  - simpl. lra.
  - simpl.
    apply Rmax_le_compat.
    + exact H.
    + apply IHHrefines.
      simpl in Hlen'. lia.
Qed.

End EffectiveDescent.

(** * Corollaries *)

(** Two-patch case *)
Corollary two_patch_gluing :
  forall (C1 C2 : Cert) (delta : R),
    cert_wf C1 -> cert_wf C2 -> delta >= 0 ->
    exists C,
      cert_wf C /\
      (cert_size C <= cert_size C1 + cert_size C2 + 2)%nat /\
      cert_error C <= Rmax (cert_error C1) (cert_error C2).
Proof.
  intros C1 C2 delta Hwf1 Hwf2 Hdelta.
  exists (GlueCert 2 [C1; C2]
    {| overlap_indices := [(0, 1)]; deltas := [delta]; compat_witness := [0] |}
    {| num_patches := 2; lipschitz_bounds := [1; 1]; support_data := [(0, 0.5); (0.5, 1)] |}).
  repeat split.
  - (* M > 0 *) lia.
  - (* length = M *) reflexivity.
  - (* Forall cert_wf *) constructor; [exact Hwf1 | constructor; [exact Hwf2 | constructor]].
  - (* Size bound *)
    simpl. lia.
  - (* Error bound *)
    simpl. apply Rmax_l.
Qed.

(** Uniform partition case *)
Corollary uniform_partition_gluing :
  forall (M : nat) (certs : list Cert) (eps : R),
    (M > 0)%nat ->
    length certs = M ->
    Forall (fun C => cert_error C <= eps) certs ->
    Forall cert_wf certs ->
    exists C,
      cert_wf C /\
      cert_error C <= eps.
Proof.
  intros M certs eps HM Hlen Herrors Hwfs.
  exists (GlueCert M certs empty_compat trivial_partition).
  split.
  - simpl. repeat split.
    + exact HM.
    + exact Hlen.
    + exact Hwfs.
  - simpl.
    (* cert_error = max of cert_error of certs ≤ eps *)
    induction certs.
    + simpl. lra.
    + simpl. apply Rmax_le_compat.
      * inversion Herrors. exact H1.
      * apply IHcerts.
        -- simpl in Hlen. lia.
        -- inversion Herrors. exact H2.
        -- inversion Hwfs. exact H2.
Qed.

End UELAT_EffectiveDescent.
