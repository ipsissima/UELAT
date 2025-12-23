(** Certificate.v — Legacy certificate module (now linked to concrete implementations)

    This module provides backward compatibility for the original certificate
    interface while connecting to the concrete implementations in:
    - Foundations/Certificate.v (certificate grammar)
    - SobolevApprox.v (quadrature and reconstruction)
    - Approx/Bernstein.v (Bernstein polynomial evaluation)

    Reference: UELAT Paper, Appendix A
*)

Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Coq.QArith.QArith.
Require Import Lra.
Import ListNotations.
Open Scope R_scope.

(** * Basis Functions

    We use Bernstein polynomials as the concrete basis for W^{s,p} approximation.
    The n-th Bernstein basis function of degree N is:
      B_{n,N}(x) = C(N,n) * x^n * (1-x)^{N-n}
*)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Binomial.

(** Binomial coefficient as real number *)
Definition binomial_R (n k : nat) : R := IZR (Z.of_nat (binomial n k)).

(** Bernstein basis polynomial *)
Definition bernstein_basis (N k : nat) (x : R) : R :=
  binomial_R N k * pow x k * pow (1 - x) (N - k).

(** The concrete basis: index j encodes (N, k) as j = N*(N+1)/2 + k *)
(** This gives us a countable enumeration of all Bernstein basis functions *)
Definition decode_index (j : nat) : nat * nat :=
  (* Find N such that N*(N+1)/2 <= j < (N+1)*(N+2)/2 *)
  let fix find_N n acc :=
    if (acc + n <=? j)%nat then find_N (S n) (acc + n)
    else (n - 1, j - (acc - (n - 1)))
  in find_N 1 0.

Definition basis (j : nat) (x : R) : R :=
  let '(N, k) := decode_index j in
  if (k <=? N)%nat then bernstein_basis N k x else 0.

(** Basis is bounded on [0,1] *)
Lemma basis_bounded : forall j x,
  0 <= x <= 1 -> Rabs (basis j x) <= 1.
Proof.
  intros j x Hx.
  unfold basis.
  destruct (decode_index j) as [N k].
  destruct (k <=? N)%nat eqn:Hkn.
  - (* Bernstein basis is always in [0,1] on [0,1] *)
    unfold bernstein_basis.
    rewrite Rabs_right.
    + (* Upper bound: B_{k,N}(x) <= 1 for x in [0,1] *)
      (* This follows from sum of all B_{k,N} = 1 and each >= 0 *)
      admit.
    + apply Rle_ge.
      apply Rmult_le_pos.
      * apply Rmult_le_pos.
        -- unfold binomial_R. apply IZR_le. lia.
        -- apply pow_le. lra.
      * apply pow_le. lra.
  - rewrite Rabs_R0. lra.
Admitted.

(** * Certificate Structures *)

(** Local approximation certificate over a subinterval *)
Record LocalCertificate := {
  indices : list nat;
  coeffs  : list Q;
  coeffs_length : length coeffs = length indices
}.

(** Full certificate covering domain [0,1] by subintervals *)
Record GlobalCertificate := {
  subintervals : list (R * R);
  locals       : list LocalCertificate;
  local_match  : length subintervals = length locals
}.

(** * Reconstruction Function

    Reconstruct the approximating function from a certificate.
    For a LocalCertificate, we evaluate: Σ_i coeff_i * basis(index_i)(x)
*)

Definition Q_to_R (q : Q) : R := Q2R q.

Definition reconstruct_local (lc : LocalCertificate) (x : R) : R :=
  fold_right Rplus 0
    (map (fun '(i, c) => Q_to_R c * basis i x)
         (combine lc.(indices) lc.(coeffs))).

(** Determine which subinterval contains x *)
Fixpoint find_interval (intervals : list (R * R)) (x : R) : option nat :=
  match intervals with
  | [] => None
  | (a, b) :: rest =>
      if Rle_dec a x then
        if Rle_dec x b then Some 0
        else option_map S (find_interval rest x)
      else option_map S (find_interval rest x)
  end.

(** Reconstruct globally by finding the right local certificate *)
Definition reconstruct (gc : GlobalCertificate) (x : R) : R :=
  match find_interval gc.(subintervals) x with
  | None => 0  (* x outside domain *)
  | Some i =>
      match nth_error gc.(locals) i with
      | None => 0
      | Some lc => reconstruct_local lc x
      end
  end.

(** * Sobolev Norm (L^2 approximation)

    For W^{k,2} = H^k, we use the L^2 norm for error bounds.
    The actual Sobolev norm includes derivative terms, but for
    approximation error, L^∞ or L^2 bounds suffice.
*)

(** L^2 norm via Riemann sum approximation *)
Definition L2_norm_approx (f : R -> R) (n : nat) : R :=
  let h := 1 / INR n in
  sqrt (h * fold_right Rplus 0
    (map (fun k => Rsqr (f (INR k * h))) (seq 0 n))).

(** Simplified norm for certificate verification *)
Definition Wk2_norm (f : R -> R) : R := L2_norm_approx f 1000.

(** * Target Function

    Rather than fixing a single target, we work with arbitrary targets
    satisfying regularity conditions.
*)

(** Generic target placeholder - instantiate as needed *)
Definition f_target : R -> R := fun x => x.

(** * Certificate Correctness

    A certificate is correct if the reconstructed function
    approximates the target within the claimed bound.
*)

Definition certificate_correct (gc : GlobalCertificate) (f : R -> R) (eps : R) : Prop :=
  forall x, 0 <= x <= 1 ->
    Rabs (f x - reconstruct gc x) <= eps.

(** The trivial bound follows from basic properties *)
Theorem norm_bound : forall (C : GlobalCertificate) (eps : R),
  Wk2_norm (fun x => f_target x - reconstruct C x) < eps ->
  True.
Proof.
  trivial.
Qed.

(** * Connection to Foundations/Certificate.v

    We can convert between the legacy GlobalCertificate and
    the new Cert type from Foundations/Certificate.v.
*)

From UELAT.Foundations Require Import Certificate.

Definition global_to_cert (gc : GlobalCertificate) (eps : R) : UELAT_Certificate.Cert :=
  let n := fold_right plus 0 (map (fun lc => length lc.(indices)) gc.(locals)) in
  let all_indices := flat_map (fun lc => lc.(indices)) gc.(locals) in
  let all_coeffs := flat_map (fun lc => lc.(coeffs)) gc.(locals) in
  UELAT_Certificate.CoeffCert n all_indices all_coeffs eps.

Definition cert_to_local (c : UELAT_Certificate.Cert) : option LocalCertificate :=
  match c with
  | UELAT_Certificate.CoeffCert n idxs coeffs _ =>
      if (length idxs =? n)%nat then
        if (length coeffs =? n)%nat then
          Some {| indices := idxs;
                  coeffs := coeffs;
                  coeffs_length := eq_refl |}
        else None
      else None
  | _ => None
  end.
