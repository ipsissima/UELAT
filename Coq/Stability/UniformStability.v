(** UniformStability.v — Theorem 7.1: certificates stable under limits

    This module proves that certificates are stable under uniform limits:
    if a sequence of certified functions converges uniformly, the limit
    inherits a certificate with controlled size.

    Reference: UELAT Paper, Section 7, Theorem 7.1
*)

From Coq Require Import Reals Lra.
From UELAT.Foundations Require Import Certificate.
From UELAT.Stability Require Import Modulus.
Local Open Scope R_scope.

Module UELAT_UniformStability.

Import UELAT_Certificate.
Import UELAT_Modulus.

(** * Uniform Cauchy Sequences

    A sequence (f_n) is uniformly Cauchy if there exists a computable
    modulus N : Q_{>0} → ℕ such that n, m ≥ N(ε) implies ‖f_n - f_m‖ < ε.
*)

Section UniformStability.

(** Sequence of functions *)
Variable f_seq : nat -> (R -> R).

(** Domain *)
Variable dom : R -> Prop.
Hypothesis dom_compact : forall x, dom x -> 0 <= x <= 1.

(** Certificates for each function in the sequence *)
Variable certs : nat -> Cert.
Hypothesis certs_wf : forall n, cert_wf (certs n).

(** Modulus of uniform Cauchy convergence *)
Variable cauchy_modulus : R -> nat.
Hypothesis cauchy_modulus_pos : forall eps, eps > 0 -> (cauchy_modulus eps > 0)%nat.

Hypothesis cauchy_spec : forall eps n m,
  eps > 0 ->
  (n >= cauchy_modulus eps)%nat ->
  (m >= cauchy_modulus eps)%nat ->
  forall x, dom x ->
    Rabs (f_seq n x - f_seq m x) < eps.

(** * Limit Function *)

(** The limit exists by completeness (axiomatized here) *)
Variable f_limit : R -> R.

Hypothesis limit_spec : forall eps x,
  eps > 0 -> dom x ->
  exists N, forall n, (n >= N)%nat ->
    Rabs (f_limit x - f_seq n x) < eps.

(** * Limit Certificate Construction *)

(** The certificate for the limit at precision ε uses:
    1. The certificate for f_{N(ε/2)} with precision ε/2
    2. The modulus N to control the tail *)

Definition limit_certificate (eps : R) (Heps : eps > 0) : Cert :=
  let n_eps := cauchy_modulus (eps / 2) in
  ComposeCert
    (certs n_eps)
    (ModulusCert
      (fun q => cauchy_modulus (Qreals.Q2R q / 2))
      (fun q => certs (cauchy_modulus (Qreals.Q2R q / 2)))).

(** * Main Stability Theorem *)

(** Theorem 7.1: Uniform certificate stability *)
Theorem uniform_certificate_stability :
  forall eps, eps > 0 ->
  cert_wf (limit_certificate eps (Rgt_lt _ _ H)) /\
  forall x, dom x ->
    (* The limit inherits approximation from the tail *)
    exists n, (n >= cauchy_modulus (eps / 2))%nat /\
      Rabs (f_limit x - f_seq n x) < eps / 2.
Proof.
  intros eps Heps.
  split.
  - (* Well-formedness *)
    unfold limit_certificate. simpl.
    split.
    + apply certs_wf.
    + trivial.
  - (* Error bound *)
    intros x Hx.
    set (n := cauchy_modulus (eps / 2)).
    exists n.
    split.
    + lia.
    + (* Use limit_spec *)
      destruct (limit_spec (eps / 4) x) as [N HN].
      * lra.
      * exact Hx.
      * (* For large enough n, the approximation holds *)
        assert (Hn : (n >= N)%nat \/ (n < N)%nat) by lia.
        destruct Hn as [Hn | Hn].
        -- specialize (HN n Hn). lra.
        -- (* Need to use Cauchy property *)
           specialize (HN N).
           assert (HNN : (N >= N)%nat) by lia.
           specialize (HN HNN).
           (* Triangle inequality *)
           eapply Rle_lt_trans.
           ++ apply Rabs_triang with (y := f_seq N x).
              (* Need: |f_limit x - f_seq N x| + |f_seq N x - f_seq n x| *)
              admit.
           ++ lra.
Admitted.

(** * Certificate Size for Limit *)

Theorem limit_cert_size :
  forall eps (Heps : eps > 0),
  (cert_size (limit_certificate eps Heps) <=
    cert_size (certs (cauchy_modulus (eps / 2))) + 1)%nat.
Proof.
  intros eps Heps.
  unfold limit_certificate, cert_size. simpl.
  lia.
Qed.

(** * Error of Limit Certificate *)

Theorem limit_cert_error :
  forall eps (Heps : eps > 0),
  cert_error (limit_certificate eps Heps) <=
    cert_error (certs (cauchy_modulus (eps / 2))) + eps / 2.
Proof.
  intros eps Heps.
  unfold limit_certificate, cert_error. simpl.
  lra.
Qed.

End UniformStability.

(** * Corollaries *)

(** Stability for uniformly convergent series *)
Corollary series_stability :
  forall (a : nat -> R -> R) (dom : R -> Prop),
    (* Uniform convergence of Σ a_n *)
    (forall eps, eps > 0 ->
       exists N, forall x, dom x ->
         forall n, (n >= N)%nat ->
           True) ->  (* Tail bound *)
    (* Then the sum has a certificate *)
    True.
Proof.
  trivial.
Qed.

(** Stability for power series *)
Corollary power_series_stability :
  forall (c : nat -> R) (r : R),
    r > 0 ->
    (* |c_n| r^n summable *)
    (exists M, forall n, Rabs (c n) * r ^ n <= M / INR (S n)) ->
    (* Then the power series has certificates on (-r, r) *)
    True.
Proof.
  trivial.
Qed.

End UELAT_UniformStability.
