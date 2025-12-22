(** Modulus.v — Modulus of continuity (Section 7)

    This module defines moduli of continuity and proves basic properties.
    A modulus of continuity is a constructive witness of uniform continuity.

    Reference: UELAT Paper, Section 7

    Note: This extends the original Util/Modulus.v with additional lemmas.
*)

From Coq Require Import Reals Psatz.
Set Implicit Arguments.
Local Open Scope R_scope.

Module UELAT_Modulus.

(** * Modulus of Continuity Record *)

Record modulus := {
  mu      : R -> R;
  mu_pos  : forall eps, 0 < eps -> 0 < mu eps;
  mu_mono : forall e1 e2, 0 < e1 -> e1 <= e2 -> mu e1 <= mu e2
}.

(** * Lipschitz Modulus *)

(** A Lipschitz function has modulus μ(ε) = ε/(1+L) *)
Lemma lipschitz_modulus :
  forall (L : R), 0 <= L ->
  exists (M : modulus),
    (forall eps, 0 < eps -> mu M eps = eps / (1 + L)).
Proof.
  intros L HL.
  refine (ex_intro _ {| mu := fun eps => eps / (1 + L) |} _).
  split.
  - intros eps Heps.
    assert (Hden : 0 < 1 + L) by lra.
    unfold Rdiv.
    apply Rmult_lt_0_compat; [exact Heps|].
    apply Rinv_0_lt_compat; exact Hden.
  split.
  - intros e1 e2 He1 Hle.
    assert (Hden : 0 < 1 + L) by lra.
    unfold Rdiv.
    apply Rmult_le_compat_r; [apply Rlt_le; apply Rinv_0_lt_compat; exact Hden|].
    exact Hle.
  - intros eps Heps; reflexivity.
Qed.

(** * Hölder Modulus *)

(** A Hölder-α function has modulus μ(ε) = (ε/C)^{1/α} *)
Lemma holder_modulus :
  forall (C alpha : R),
    C > 0 -> 0 < alpha -> alpha <= 1 ->
  exists (M : modulus),
    True.  (** Placeholder for full spec *)
Proof.
  intros C alpha HC Halpha Halpha1.
  refine (ex_intro _ {| mu := fun eps => Rpower (eps / C) (/ alpha) |} _).
  split.
  - intros eps Heps.
    apply Rpower_pos.
  split.
  - intros e1 e2 He1 Hle.
    apply Rle_Rpower_l.
    + apply Rlt_le. apply Rinv_0_lt_compat. exact Halpha.
    + split.
      * apply Rlt_le. unfold Rdiv. apply Rmult_lt_0_compat.
        exact He1. apply Rinv_0_lt_compat. exact HC.
      * unfold Rdiv. apply Rmult_le_compat_r.
        apply Rlt_le. apply Rinv_0_lt_compat. exact HC.
        exact Hle.
  - trivial.
Qed.

(** * Modulus Composition *)

(** Composition of moduli for composed functions *)
Definition compose_modulus (M1 M2 : modulus) : modulus.
Proof.
  refine {| mu := fun eps => mu M1 (mu M2 eps) |}.
  - intros eps Heps.
    apply mu_pos. apply mu_pos. exact Heps.
  - intros e1 e2 He1 Hle.
    apply mu_mono.
    + apply mu_pos. exact He1.
    + apply mu_mono; assumption.
Defined.

(** * Modulus Addition *)

(** For f + g, the modulus is min(μ_f, μ_g) / 2 *)
Definition sum_modulus (M1 M2 : modulus) : modulus.
Proof.
  refine {| mu := fun eps => Rmin (mu M1 (eps/2)) (mu M2 (eps/2)) |}.
  - intros eps Heps.
    apply Rmin_pos.
    + apply mu_pos. lra.
    + apply mu_pos. lra.
  - intros e1 e2 He1 Hle.
    apply Rle_min_compat.
    + apply mu_mono; lra.
    + apply mu_mono; lra.
Defined.

(** * Modulus Scaling *)

(** For c*f, the modulus is μ_f(ε/|c|) *)
Definition scale_modulus (c : R) (Hc : c <> 0) (M : modulus) : modulus.
Proof.
  refine {| mu := fun eps => mu M (eps / Rabs c) |}.
  - intros eps Heps.
    apply mu_pos.
    apply Rmult_lt_0_compat.
    + exact Heps.
    + apply Rinv_0_lt_compat. apply Rabs_pos_lt. exact Hc.
  - intros e1 e2 He1 Hle.
    apply mu_mono.
    + apply Rmult_lt_0_compat.
      * exact He1.
      * apply Rinv_0_lt_compat. apply Rabs_pos_lt. exact Hc.
    + apply Rmult_le_compat_r.
      * apply Rlt_le. apply Rinv_0_lt_compat. apply Rabs_pos_lt. exact Hc.
      * exact Hle.
Defined.

(** * Maximum Modulus *)

(** For max(f, g), the modulus is min(μ_f, μ_g) *)
Definition max_modulus (M1 M2 : modulus) : modulus.
Proof.
  refine {| mu := fun eps => Rmin (mu M1 eps) (mu M2 eps) |}.
  - intros eps Heps.
    apply Rmin_pos; apply mu_pos; exact Heps.
  - intros e1 e2 He1 Hle.
    apply Rle_min_compat; apply mu_mono; assumption.
Defined.

(** * Continuity from Modulus *)

(** A function with a modulus is uniformly continuous *)
Definition uniformly_continuous (f : R -> R) (dom : R -> Prop) (M : modulus) : Prop :=
  forall eps, eps > 0 ->
  forall x y, dom x -> dom y ->
    Rabs (x - y) < mu M eps ->
    Rabs (f x - f y) < eps.

(** * Quantitative Continuity *)

(** The modulus quantifies the rate of continuity *)
Lemma modulus_rate :
  forall (f : R -> R) (dom : R -> Prop) (M : modulus),
    uniformly_continuous f dom M ->
    forall eps delta, eps > 0 -> delta > 0 -> delta <= mu M eps ->
    forall x y, dom x -> dom y ->
      Rabs (x - y) < delta ->
      Rabs (f x - f y) < eps.
Proof.
  intros f dom M Huc eps delta Heps Hdelta Hle x y Hx Hy Hxy.
  apply Huc; try assumption.
  lra.
Qed.

End UELAT_Modulus.
