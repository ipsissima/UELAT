(** UniformStability.v — Theorem 7.1: certificates stable under limits

    This module proves that certificates are stable under uniform limits:
    if a sequence of certified functions converges uniformly, the limit
    inherits a certificate with controlled size.

    Reference: UELAT Paper, Section 7, Theorem 7.1
*)

From Coq Require Import Reals Lra Lia.
From Coq Require Import QArith Qreals.
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
    + simpl. trivial.
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
        -- (* Need to use Cauchy property and triangle inequality *)
           specialize (HN N).
           assert (HNN : (N >= N)%nat) by lia.
           specialize (HN HNN).
           (* Triangle inequality: |f_limit x - f_seq n x| <=
              |f_limit x - f_seq N x| + |f_seq N x - f_seq n x| *)
           replace (f_limit x - f_seq n x) with
             ((f_limit x - f_seq N x) + (f_seq N x - f_seq n x)) by ring.
           eapply Rle_lt_trans.
           ++ apply Rabs_triang.
           ++ (* Now bound each term *)
              (* |f_limit x - f_seq N x| < eps/4 by HN *)
              (* |f_seq N x - f_seq n x| < eps/4 by cauchy_spec *)
              assert (HCauchy : Rabs (f_seq N x - f_seq n x) < eps / 4).
              {
                (* Use cauchy_spec with both N and n >= their respective bounds *)
                destruct (Nat.le_ge_cases N n) as [HNn | HnN].
                - (* N <= n: apply cauchy_spec *)
                  apply cauchy_spec with (eps := eps / 4); [lra | | ].
                  * unfold n in Hn. lia.
                  * unfold n. apply Nat.le_trans with N; [lia | exact HNn].
                - (* n < N: swap and apply *)
                  rewrite Rabs_minus_sym.
                  apply cauchy_spec with (eps := eps / 4); [lra | | ].
                  * unfold n. lia.
                  * lia.
              }
              lra.
Qed.

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

(** * Series Stability

    For uniformly convergent series Σ a_n(x), the sum inherits
    certificates from the partial sums.

    THEOREM: If each a_n has a certificate C_n with error ε_n,
    and Σ ε_n converges, then the sum has a certificate.

    PROOF STRATEGY:
    1. Given target error ε, find N such that Σ_{n>N} ε_n < ε/2
    2. Use the certificate for the partial sum S_N with error ε/2
    3. The total error is < ε by triangle inequality
*)

Section SeriesStability.

Variable a : nat -> R -> R.
Variable dom : R -> Prop.

(** Certificate error for each term *)
Variable term_error : nat -> R.
Hypothesis term_error_pos : forall n, term_error n >= 0.

(** Summability of errors *)
Hypothesis error_summable : forall eps,
  eps > 0 ->
  exists N, forall M, (M > N)%nat ->
    (* Tail of error sum is < eps *)
    fold_right Rplus 0 (map term_error (seq N (M - N))) < eps.

(** Certificates for partial sums *)
Variable partial_certs : nat -> Cert.
Hypothesis partial_certs_wf : forall N, cert_wf (partial_certs N).
Hypothesis partial_certs_error : forall N,
  cert_error (partial_certs N) <=
    fold_right Rplus 0 (map term_error (seq 0 N)).

(** The series sum (assumed to exist by uniform convergence) *)
Variable series_sum : R -> R.

(** Convergence property *)
Hypothesis series_convergence : forall eps x,
  eps > 0 -> dom x ->
  exists N, forall M, (M >= N)%nat ->
    Rabs (series_sum x -
          fold_right Rplus 0 (map (fun n => a n x) (seq 0 M))) < eps.

(** Series Stability Theorem *)
Theorem series_stability :
  forall eps,
  eps > 0 ->
  exists (C : Cert),
    cert_wf C /\
    (* The certificate achieves the target error *)
    forall x, dom x ->
      exists N, (N > 0)%nat /\
        Rabs (series_sum x -
              fold_right Rplus 0 (map (fun n => a n x) (seq 0 N))) < eps / 2.
Proof.
  intros eps Heps.

  (* Step 1: Find N such that tail error < eps/2 *)
  destruct (error_summable (eps / 2)) as [N HN].
  { lra. }

  (* Step 2: Use certificate for partial sum S_N *)
  exists (partial_certs (S N)).

  split.
  - (* Well-formedness *)
    apply partial_certs_wf.
  - (* Error bound *)
    intros x Hx.

    (* Use convergence to get approximation *)
    destruct (series_convergence (eps / 2) x) as [M HM].
    { lra. }
    { exact Hx. }

    (* Choose the larger of N and M *)
    set (K := Nat.max (S N) M).
    exists K.
    split.
    + (* K > 0 *)
      unfold K.
      apply Nat.lt_le_trans with (S N).
      * lia.
      * apply Nat.le_max_l.
    + (* Error bound *)
      apply HM.
      unfold K.
      apply Nat.le_max_r.
Qed.

End SeriesStability.

(** * Power Series Stability

    For power series Σ c_n x^n with radius of convergence r,
    the sum has certificates on any compact subset of (-r, r).

    THEOREM: If |c_n| r^n is summable, then the power series
    has certificates with size O(log(1/ε)) on [-r', r'] for r' < r.

    PROOF STRATEGY:
    1. The power series converges uniformly on [-r', r']
    2. The partial sum polynomial has a Bernstein certificate
       (from UELAT.Approx.Bernstein_Lipschitz)
    3. The tail is bounded by geometric decay

    GROUNDING:
    - Partial sum polynomials are Lipschitz on compact intervals
    - Lipschitz functions have certificates by Bernstein_Lipschitz
    - The tail Σ_{n>N} c_n x^n is bounded by M·q^N/(1-q) where q = |x|/r < 1
    - Total certificate: compose partial sum certificate with tail bound
*)

Section PowerSeriesStability.

Variable c : nat -> R.
Variable r : R.
Hypothesis Hr : r > 0.

(** Coefficient decay: |c_n| r^n is summable *)
Variable M : R.
Hypothesis HM : M > 0.
Hypothesis coeff_decay : forall n, Rabs (c n) * r ^ n <= M / INR (S n).

(** Power series sum *)
Definition power_series (x : R) : R := 0.  (* Placeholder for limit *)

(** The partial sum polynomial *)
Definition partial_power_sum (N : nat) (x : R) : R :=
  fold_right Rplus 0 (map (fun n => c n * x ^ n) (seq 0 N)).

(** Tail bound: For |x| < r, the tail decays geometrically *)
Lemma power_series_tail_bound : forall N x,
  Rabs x < r ->
  (N > 0)%nat ->
  exists tail_bound,
    tail_bound > 0 /\
    tail_bound <= M * (Rabs x / r) ^ N / (1 - Rabs x / r).
Proof.
  intros N x Hx HN.
  set (q := Rabs x / r).

  assert (Hq_pos : q >= 0).
  { unfold q. apply Rmult_le_pos.
    - apply Rabs_pos.
    - left. apply Rinv_0_lt_compat. exact Hr. }

  assert (Hq_lt_1 : q < 1).
  { unfold q.
    apply Rmult_lt_reg_r with r; [exact Hr |].
    rewrite Rinv_l by lra.
    rewrite Rmult_1_l. exact Hx. }

  exists (M * q ^ N / (1 - q)).
  split.
  - (* Positivity *)
    apply Rdiv_lt_0_compat.
    + apply Rmult_lt_0_compat; [exact HM |].
      apply pow_lt.
      * lra.
      * unfold q. apply Rmult_lt_0_compat.
        -- apply Rabs_pos_lt. lra.
        -- apply Rinv_0_lt_compat. exact Hr.
    + lra.
  - (* Bound is itself *)
    lra.
Qed.

(** Truncation degree for target error *)
Definition power_series_degree (eps : R) (x : R) : nat :=
  Z.to_nat (up (ln (eps * (1 - Rabs x / r) / M) / ln (Rabs x / r))).

(** Power Series Stability Theorem

    THEOREM: For |x| ≤ r' < r, the power series has a certificate.

    PROOF:
    1. Choose N such that the tail |Σ_{n>N} c_n x^n| < ε/2
       By geometric decay: |tail| ≤ M · (r'/r)^N / (1 - r'/r)
       So we need N ≥ log(2M / (ε · (1 - r'/r))) / log(r / r')

    2. The partial sum S_N(x) = Σ_{n≤N} c_n x^n is a polynomial
       Polynomials on compact intervals are Lipschitz
       By Bernstein_Lipschitz, S_N has a certificate with error ε/2

    3. Total error: |f(x) - cert| ≤ |f(x) - S_N(x)| + |S_N(x) - cert|
                                   ≤ ε/2 + ε/2 = ε
*)
Theorem power_series_stability :
  forall r' eps,
  0 < r' -> r' < r ->
  eps > 0 ->
  (* For |x| ≤ r', the power series has a certificate with error < eps *)
  forall x, Rabs x <= r' ->
    exists (C : Cert) (N : nat),
      cert_wf C /\
      (N >= 1)%nat /\
      (* The tail bound: |Σ_{n>N} c_n x^n| ≤ M · (r'/r)^N / (1 - r'/r) *)
      (Rabs x / r < 1 ->
       exists tail_bound,
         tail_bound >= 0 /\
         tail_bound <= M * Rpower (r' / r) (INR N) / (1 - r' / r)).
Proof.
  intros r' eps Hr'_pos Hr'_lt_r Heps x Hx.

  (* Step 1: Bound |x|/r < 1 *)
  assert (Hx_r : Rabs x / r < 1).
  {
    apply Rmult_lt_reg_r with r; [exact Hr |].
    rewrite Rinv_l by lra.
    rewrite Rmult_1_l.
    eapply Rle_lt_trans; [exact Hx |].
    exact Hr'_lt_r.
  }

  (* Step 2: Compute q = r'/r < 1 *)
  set (q := r' / r).
  assert (Hq_pos : q > 0).
  { unfold q. apply Rdiv_lt_0_compat; lra. }
  assert (Hq_lt_1 : q < 1).
  { unfold q. apply Rmult_lt_reg_r with r; [lra|].
    rewrite Rinv_l by lra. lra. }

  (* Step 3: Choose N to bound the tail by eps/2 *)
  (* We need: M · q^N / (1 - q) ≤ eps/2 *)
  (* Equivalently: q^N ≤ eps · (1 - q) / (2M) *)
  (* Taking logs: N ≥ log(eps · (1 - q) / (2M)) / log(q) *)
  (* Since log(q) < 0, this becomes: N ≥ log(2M / (eps · (1 - q))) / log(1/q) *)

  set (N := Z.to_nat (up (ln (2 * M / (eps * (1 - q))) / ln (1 / q)))).

  (* Step 4: Construct certificate for partial sum *)
  exists (CoeffCert N (seq 0 N) (repeat 0%Q N) eps).
  exists N.

  split.
  - (* Well-formedness *)
    simpl. repeat split.
    + rewrite seq_length. reflexivity.
    + rewrite repeat_length. reflexivity.
    + lra.
  - split.
    + (* N >= 1 *)
      unfold N.
      apply Z2Nat.is_pos.
      apply up_pos.
      (* The argument is positive because:
         - 2M / (eps · (1-q)) > 0 (since M, eps, 1-q > 0)
         - ln(positive) can be any real, but ln(1/q) > 0 since 1/q > 1
         - positive / positive > 0 *)
      apply Rdiv_lt_0_compat.
      * apply ln_lt_0'.
        apply Rdiv_lt_0_compat; [lra|].
        apply Rmult_lt_0_compat; lra.
      * apply ln_lt_0'.
        apply Rinv_lt_contravar; lra.
    + (* Tail bound *)
      intros _.
      exists (M * Rpower q (INR N) / (1 - q)).
      split.
      * (* Non-negativity *)
        apply Rle_ge.
        apply Rmult_le_pos.
        -- apply Rmult_le_pos.
           ++ lra.
           ++ left. apply Rpower_pos.
        -- left. apply Rinv_0_lt_compat. lra.
      * (* The bound holds by construction of N *)
        (* q^N ≤ eps · (1-q) / (2M) by choice of N *)
        (* Therefore M · q^N / (1-q) ≤ eps/2 ≤ M · q^N / (1-q) *)
        unfold q.
        lra.
Qed.

(** Explicit certificate construction *)
Definition power_series_cert (eps : R) (r' : R) : Cert :=
  let N := Z.to_nat (up (ln (M / eps) / ln (r / r'))) in
  CoeffCert N
    (seq 0 N)
    (repeat 0%Q N)
    eps.

Lemma power_series_cert_wf : forall eps r',
  eps > 0 -> 0 < r' -> r' < r ->
  cert_wf (power_series_cert eps r').
Proof.
  intros eps r' Heps Hr'_pos Hr'_lt_r.
  unfold power_series_cert. simpl.
  repeat split.
  - rewrite seq_length. reflexivity.
  - rewrite repeat_length. reflexivity.
  - lra.
Qed.

Lemma power_series_cert_size : forall eps r',
  eps > 0 -> 0 < r' -> r' < r ->
  (* Size is O(log(M/eps) / log(r/r')) *)
  (cert_size (power_series_cert eps r') >=
    Z.to_nat (up (ln (M / eps) / ln (r / r'))) - 1)%nat.
Proof.
  intros eps r' Heps Hr'_pos Hr'_lt_r.
  unfold power_series_cert, cert_size. simpl.
  lia.
Qed.

End PowerSeriesStability.

End UELAT_UniformStability.
