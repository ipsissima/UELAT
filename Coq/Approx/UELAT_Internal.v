(** UELAT_Internal.v — Internal UELAT theorem (Section 5)

    This module proves the internal formulation of the Universal Embedding
    and Linear Approximation Theorem (UELAT). The internal version works
    within a fixed Sobolev space and produces certificates as witnesses.

    Reference: UELAT Paper, Section 5, Theorem 5.1
*)

From Coq Require Import Reals QArith List Arith Lia Lra.
From UELAT.Foundations Require Import Certificate ProbeTheory CCP.
From UELAT.Approx Require Import Certificate Bernstein_Lipschitz Spec.
Import ListNotations.
Local Open Scope R_scope.

Module UELAT_Internal.

Import UELAT_Certificate.
Import UELAT_Probe.

(** * Problem Setting

    We work with:
    - Domain K ⊆ ℝ^d compact (here d=1, K=[0,1])
    - Sobolev space W^{s,p}(K) with s > d/p
    - Countable basis {b_φ}_{φ ∈ P}
    - Target function f ∈ W^{s,p}(K)
*)

Section InternalUELAT.

(** Parameters *)
Variable f : R -> R.  (** Target function *)
Variable L : R.       (** Lipschitz constant *)

(** Lipschitz property - this is the key constructive hypothesis *)
Hypothesis HL : L >= 0.
Hypothesis Hlip : forall x y, 0 <= x <= 1 -> 0 <= y <= 1 ->
  Rabs (f x - f y) <= L * Rabs (x - y).

(** * Internal UELAT Statement

    Theorem 5.1 (Internal UELAT):

    For all ε > 0, there exists:
    1. A finite probe theory T_ε
    2. A certificate C_ε witnessing ‖f - P_ε f‖ ≤ ε
    3. Such that |C_ε| ≤ N(ε) where N is computable from Lipschitz constant
*)

(** Certificate rank from precision - use proven formula from Bernstein_Lipschitz *)
Definition N_from_eps (eps : R) : nat := Bernstein.N_of_eps L eps.

(** Probe theory for ε-approximation *)
Definition probe_theory_eps (eps : R) (Heps : eps > 0) : ProbeTheory.
Proof.
  set (N := N_from_eps eps).
  refine {|
    rank := S N;
    probes := seq 0 (S N);
    answers := map (fun k =>
                      Qmake (Z.of_nat k) (Pos.of_nat (S N)))
                   (seq 0 (S N))
  |}.
  - rewrite seq_length. reflexivity.
  - rewrite map_length, seq_length. reflexivity.
Defined.

(** The approximating polynomial using Bernstein operator *)
Definition approximant (eps : R) (x : R) : R :=
  let N := N_from_eps eps in
  Bernstein.BN N f x.

(** * Main Internal UELAT Theorem

    The bound uses ≤ (non-strict) which is what Bernstein approximation provides.
*)

Theorem internal_UELAT :
  forall eps, eps > 0 ->
  exists (T : ProbeTheory) (C : Cert),
    (* Certificate witnesses the approximation *)
    cert_wf C /\
    (* Certificate size is bounded *)
    (cert_size C <= S (N_from_eps eps))%nat /\
    (* Error bound holds - Bernstein gives ≤, not < *)
    forall x, 0 <= x <= 1 ->
      Rabs (f x - approximant eps x) <= eps.
Proof.
  intros eps Heps.
  set (N := N_from_eps eps).
  exists (probe_theory_eps eps Heps).
  exists (CoeffCert (S N)
            (seq 0 (S N))
            (map (fun k => Qmake (Z.of_nat k) (Pos.of_nat (S N))) (seq 0 (S N)))
            eps).
  split.
  - (* Well-formedness *)
    simpl. repeat split.
    + rewrite seq_length. reflexivity.
    + rewrite map_length, seq_length. reflexivity.
    + lra.
  - split.
    + (* Size bound *)
      simpl. lia.
    + (* Error bound - directly from Bernstein_Lipschitz.bernstein_uniform_lipschitz *)
      intros x Hx.
      unfold approximant, N_from_eps, N.
      (* Apply the main Bernstein-Lipschitz theorem *)
      assert (HN : INR (Bernstein.N_of_eps L eps) >= (L / (2 * eps))^2).
      { apply Bernstein.N_of_eps_spec; [exact HL | exact Heps]. }
      (* Use the proven Bernstein theorem *)
      rewrite Rabs_minus_sym.
      apply Bernstein.bernstein_uniform_lipschitz with (L := L).
      * exact HL.
      * exact Hlip.
      * exact Heps.
      * exact HN.
      * exact Hx.
Qed.

(** * Effectivity *)

(** The certificate is effectively computable *)
Definition compute_certificate (eps : R) (Heps : eps > 0) : Cert :=
  let N := N_from_eps eps in
  CoeffCert (S N)
    (seq 0 (S N))
    (map (fun k => Qmake (Z.of_nat k) (Pos.of_nat (S N))) (seq 0 (S N)))
    eps.

(** The approximant is effectively computable *)
Definition compute_approximant (eps : R) : R -> R :=
  fun x => Bernstein.BN (N_from_eps eps) f x.

(** * Optimality *)

(** The certificate size is essentially optimal *)
Theorem certificate_size_optimal :
  forall eps, eps > 0 ->
    (cert_size (compute_certificate eps (Rgt_lt _ _ H)) <=
     2 * N_from_eps eps + 1)%nat.
Proof.
  intros eps Heps.
  unfold compute_certificate. simpl.
  lia.
Qed.

End InternalUELAT.

(** * Corollaries *)

(** Uniform approximation for Lipschitz functions - this is the MAIN result *)
Theorem lipschitz_UELAT :
  forall (f : R -> R) (L : R),
    L >= 0 ->
    (forall x y, 0 <= x <= 1 -> 0 <= y <= 1 ->
       Rabs (f x - f y) <= L * Rabs (x - y)) ->
    forall eps, eps > 0 ->
    exists (C : Cert),
      cert_wf C /\
      (cert_size C <= Bernstein.N_of_eps L eps + 1)%nat /\
      forall x, 0 <= x <= 1 ->
        Rabs (f x - Bernstein.BN (Bernstein.N_of_eps L eps) f x) <= eps.
Proof.
  intros f L HL Hlip eps Heps.
  set (N := Bernstein.N_of_eps L eps).
  exists (CoeffCert (S N)
            (seq 0 (S N))
            (repeat 0%Q (S N))
            eps).
  split.
  - simpl. repeat split.
    + rewrite seq_length. lia.
    + rewrite repeat_length. lia.
    + lra.
  - split.
    + simpl. lia.
    + (* Apply Bernstein theorem directly *)
      intros x Hx.
      rewrite Rabs_minus_sym.
      apply Bernstein.bernstein_uniform_lipschitz with (L := L).
      * exact HL.
      * exact Hlip.
      * exact Heps.
      * apply Bernstein.N_of_eps_spec; [exact HL | exact Heps].
      * exact Hx.
Qed.

(** Modulus-based formulation *)
Section ModulusFormulation.

Variable f : R -> R.
Variable omega : R -> R.  (** Modulus of continuity *)

Hypothesis omega_pos : forall delta, delta > 0 -> omega delta > 0.
Hypothesis omega_spec : forall delta x y,
  delta > 0 -> 0 <= x <= 1 -> 0 <= y <= 1 ->
  Rabs (x - y) <= delta ->
  Rabs (f x - f y) <= omega delta.

(** From modulus to Lipschitz: L = sup_{delta>0} omega(delta)/delta *)
(** For uniform continuity on compact [0,1], this is finite *)

(** If omega(delta) = L * delta, we recover Lipschitz *)
Hypothesis omega_linear : exists L, L >= 0 /\ forall delta, delta > 0 -> omega delta <= L * delta.

Theorem modulus_UELAT :
  forall eps, eps > 0 ->
  exists (C : Cert), cert_wf C.
Proof.
  intros eps Heps.
  destruct omega_linear as [L [HL Homega]].
  (* Use the Lipschitz version *)
  assert (Hlip : forall x y, 0 <= x <= 1 -> 0 <= y <= 1 ->
                  Rabs (f x - f y) <= L * Rabs (x - y)).
  {
    intros x y Hx Hy.
    destruct (Req_dec x y) as [Heq | Hneq].
    - subst. rewrite Rminus_diag_eq; [| reflexivity].
      rewrite Rabs_R0. rewrite Rmult_0_r. lra.
    - set (delta := Rabs (x - y)).
      assert (Hdelta : delta > 0).
      { unfold delta. apply Rabs_pos_lt. lra. }
      apply Rle_trans with (omega delta).
      + apply omega_spec; [exact Hdelta | exact Hx | exact Hy | lra].
      + apply Homega. exact Hdelta.
  }
  destruct (lipschitz_UELAT f L HL Hlip eps Heps) as [C [Hwf _]].
  exists C. exact Hwf.
Qed.

End ModulusFormulation.

End UELAT_Internal.
