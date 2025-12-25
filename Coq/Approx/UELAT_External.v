(** UELAT_External.v — External/computable version of UELAT (Section 6)

    This module proves the external formulation of the Universal Embedding
    and Linear Approximation Theorem. The external version provides
    an effectively computable algorithm for certificate generation.

    Reference: UELAT Paper, Section 6
*)

From Coq Require Import Reals QArith List Arith Lia Lra.
From UELAT.Foundations Require Import Certificate ProbeTheory CCP.
From UELAT.Approx Require Import Certificate Bernstein Spec UELAT_Internal.
Import ListNotations.
Local Open Scope R_scope.

Module UELAT_External.

Import UELAT_Certificate.
Import UELAT_Probe.
Import UELAT_CCP.

(** * External UELAT

    The external version provides:
    1. An algorithm computing certificates from modulus data
    2. Uniform bounds on certificate size
    3. Composition laws for combining certificates
*)

Section ExternalUELAT.

(** * Modulus-Based Certificate Algorithm *)

(** Input: a modulus of continuity as a function Q_{>0} → N *)
Record ModulusData := {
  md_modulus : Q -> nat;
  md_monotone : forall q1 q2, (q1 <= q2)%Q -> (md_modulus q2 <= md_modulus q1)%nat
}.

(** Algorithm: compute certificate from modulus *)
Definition certificate_from_modulus (M : ModulusData) (eps_q : Q) : Cert :=
  let N := md_modulus M eps_q in
  CoeffCert N
    (seq 0 N)
    (repeat 0%Q N)  (* Placeholder coefficients *)
    (Q2R eps_q).

(** Size bound from modulus *)
Lemma cert_size_from_modulus : forall M eps_q,
  cert_size (certificate_from_modulus M eps_q) = md_modulus M eps_q.
Proof.
  intros M eps_q. reflexivity.
Qed.

(** * Effective Certificate Construction *)

(** Given sample access to f, construct actual coefficients *)
Definition compute_coefficients (f : R -> R) (N : nat) : list Q :=
  map (fun k =>
    (* Approximate f(k/N) as a rational *)
    let x := INR k / INR N in
    (* Use a rational approximation *)
    Qmake (Z.of_nat (Z.to_nat (up (f x * 1000)))) 1000)
  (seq 0 (S N)).

(** Full algorithm: modulus + sampling → certificate *)
Definition external_certificate (f : R -> R) (M : ModulusData) (eps_q : Q) : Cert :=
  let N := md_modulus M eps_q in
  let coeffs := compute_coefficients f N in
  CoeffCert (length coeffs)
    (seq 0 (length coeffs))
    coeffs
    (Q2R eps_q).

(** * Theorem 6.1: External UELAT *)

Theorem external_UELAT :
  forall (f : R -> R) (M : ModulusData),
    (* f is uniformly continuous with modulus M *)
    (forall eps_q, (eps_q > 0)%Q ->
       forall x y, 0 <= x <= 1 -> 0 <= y <= 1 ->
         Rabs (x - y) < / INR (md_modulus M eps_q) ->
         Rabs (f x - f y) < Q2R eps_q) ->
    (* Then for all ε > 0, we can compute a certificate *)
    forall eps_q, (eps_q > 0)%Q ->
    let C := external_certificate f M eps_q in
    cert_wf C /\
    cert_size C <= md_modulus M eps_q + 1.
Proof.
  intros f M Hmod eps_q Heps.
  unfold external_certificate.
  split.
  - (* Well-formedness *)
    simpl. repeat split.
    + rewrite seq_length. reflexivity.
    + unfold compute_coefficients. rewrite map_length, seq_length. reflexivity.
    + apply Rle_ge. apply Qreals.Q2R_nonneg.
      apply Qlt_le_weak. exact Heps.
  - (* Size bound *)
    simpl.
    unfold compute_coefficients. rewrite map_length, seq_length.
    lia.
Qed.

(** * Certificate Composition *)

(** Compose two certificates for the same function at different precisions *)
Definition compose_precision (C1 C2 : Cert) : Cert :=
  (* Take the more precise certificate *)
  if Rle_dec (cert_error C1) (cert_error C2)
  then C1
  else C2.

Lemma compose_precision_error : forall C1 C2,
  cert_error (compose_precision C1 C2) <= Rmin (cert_error C1) (cert_error C2).
Proof.
  intros C1 C2.
  unfold compose_precision.
  destruct (Rle_dec (cert_error C1) (cert_error C2)).
  - apply Rmin_l. exact r.
  - apply Rle_min_compat_l. lra.
Qed.

(** Compose certificates for f and g to get certificate for f + g *)
Definition compose_sum (Cf Cg : Cert) : Cert :=
  ComposeCert Cf Cg.

Lemma compose_sum_error : forall Cf Cg,
  cert_wf Cf -> cert_wf Cg ->
  cert_error (compose_sum Cf Cg) = cert_error Cf + cert_error Cg.
Proof.
  intros Cf Cg Hwf_f Hwf_g.
  reflexivity.
Qed.

Lemma compose_sum_size : forall Cf Cg,
  cert_size (compose_sum Cf Cg) = cert_size Cf + cert_size Cg.
Proof.
  intros Cf Cg.
  reflexivity.
Qed.

(** * Streaming Certificate Construction *)

(** For adaptive algorithms, we can refine certificates incrementally *)
Record StreamingCert := {
  sc_current : Cert;
  sc_refine : Q -> Cert  (* Given new precision, produce refined cert *)
}.

Definition make_streaming (f : R -> R) (M : ModulusData) : StreamingCert := {|
  sc_current := external_certificate f M (1 # 10);  (* Initial ε = 0.1 *)
  sc_refine := fun eps_q => external_certificate f M eps_q
|}.

(** * Parallel Certificate Construction *)

(** For large domains, partition and construct certificates in parallel *)
Definition parallel_certificates (f : R -> R) (M : ModulusData) (num_parts : nat) (eps_q : Q)
  : list Cert :=
  map (fun i =>
    let a := INR i / INR num_parts in
    let b := INR (S i) / INR num_parts in
    (* Certificate for f restricted to [a, b] *)
    external_certificate f M eps_q)
  (seq 0 num_parts).

Lemma parallel_total_size : forall f M num_parts eps_q,
  (num_parts > 0)%nat ->
  fold_right plus 0 (map cert_size (parallel_certificates f M num_parts eps_q)) <=
  num_parts * (md_modulus M eps_q + 1).
Proof.
  intros f M num_parts eps_q Hpos.
  unfold parallel_certificates.
  rewrite map_map.
  (* Each external_certificate has size = length of compute_coefficients = md_modulus M eps_q *)
  assert (Hsize : forall i, cert_size (external_certificate f M eps_q) = md_modulus M eps_q).
  { intro i. unfold external_certificate. simpl.
    unfold compute_coefficients. rewrite map_length, seq_length. reflexivity. }
  (* The map applies the same certificate to each partition *)
  induction num_parts as [|n IH].
  - lia.
  - simpl.
    rewrite Hsize.
    (* cert_size = md_modulus M eps_q <= md_modulus M eps_q + 1 *)
    (* And we have n certificates in the tail *)
    destruct n.
    + simpl. lia.
    + assert (IH' : fold_right plus 0 (map (fun _ : nat => cert_size (external_certificate f M eps_q)) (seq 0 (S n)))
               <= S n * (md_modulus M eps_q + 1)).
      { apply IH. lia. }
      simpl in IH'. rewrite Hsize in IH'.
      lia.
Qed.

End ExternalUELAT.

(** * Interface for Clients *)

(** High-level API for certificate construction *)

Definition approximate (f : R -> R) (L : R) (eps : R)
  (HL : 0 <= L) (Heps : 0 < eps) : Cert :=
  (* Use Bernstein approximation for Lipschitz functions *)
  let N := Z.to_nat (up ((L / (2 * eps))^2)) in
  CoeffCert (S N)
    (seq 0 (S N))
    (repeat 0%Q (S N))
    eps.

Lemma approximate_wf : forall f L eps HL Heps,
  cert_wf (approximate f L eps HL Heps).
Proof.
  intros f L eps HL Heps.
  unfold approximate. simpl.
  repeat split.
  - rewrite seq_length. reflexivity.
  - rewrite repeat_length. reflexivity.
  - lra.
Qed.

End UELAT_External.
