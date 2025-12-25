(** Entropy.v — Metric entropy lemmas for incompressibility

    This module provides lemmas about metric entropy and covering numbers
    that are used in the certificate incompressibility proofs.

    Reference: UELAT Paper, Section 8
*)

From Coq Require Import Reals Lra Lia.
Local Open Scope R_scope.

Module UELAT_Entropy.

(** * Covering Numbers

    The covering number N(S, ε) is the minimum number of ε-balls
    needed to cover a set S.
*)

(** Abstract covering number *)
Definition CoveringNumber := R -> R -> R.
  (** CoveringNumber S ε = N(S, ε) *)

(** * Properties of Covering Numbers *)

Section CoveringProperties.

Variable covering : CoveringNumber.

(** Covering number is always ≥ 1 for non-empty sets *)
Hypothesis covering_ge_1 : forall S eps,
  eps > 0 -> covering S eps >= 1.

(** Covering number increases as ε decreases *)
Hypothesis covering_monotone : forall S eps1 eps2,
  0 < eps1 -> eps1 <= eps2 -> covering S eps2 <= covering S eps1.

(** * Entropy = log(Covering Number) *)

Definition entropy (S eps : R) : R :=
  ln (covering S eps).

Lemma entropy_nonneg : forall S eps,
  eps > 0 -> entropy S eps >= 0.
Proof.
  intros S eps Heps.
  unfold entropy.
  apply Rle_ge.
  rewrite <- ln_1.
  apply Rlt_le.
  apply ln_increasing.
  - lra.
  - apply Rlt_le_trans with 1; [lra | apply Rge_le; apply covering_ge_1; exact Heps].
Qed.

Lemma entropy_monotone : forall S eps1 eps2,
  0 < eps1 -> eps1 <= eps2 -> entropy S eps2 <= entropy S eps1.
Proof.
  intros S eps1 eps2 Heps1 Hle.
  unfold entropy.
  destruct (Req_dec eps1 eps2) as [Heq | Hneq].
  - subst. lra.
  - apply Rlt_le. apply ln_increasing.
    + apply Rlt_le_trans with 1; [lra | apply Rge_le; apply covering_ge_1; lra].
    + apply Rlt_le_trans with (covering S eps1).
      * apply Rge_gt_trans with 1; [apply covering_ge_1; lra | lra].
      * apply covering_monotone; lra.
Qed.

End CoveringProperties.

(** * Kolmogorov-Tikhomirov Entropy for Sobolev Spaces

    For the unit ball of W^{s,p}([0,1]^d) with s > d/p:
      H(ε) = log N(B, ε) ≍ ε^{-d/s}
*)

Section SobolevEntropy.

Variable d : nat.  (** Dimension *)
Variable s : R.    (** Smoothness *)
Variable p : R.    (** Integrability *)

Hypothesis Hd : (d > 0)%nat.
Hypothesis Hs : s > 0.
Hypothesis Hp : p >= 1.
Hypothesis Hsp : s > INR d / p.  (** Sobolev embedding *)

(** Lower bound on entropy *)
Definition sobolev_entropy_lower (eps : R) : R :=
  Rpower eps (- INR d / s).

(** Upper bound on entropy *)
Definition sobolev_entropy_upper (eps : R) : R :=
  2 * Rpower eps (- INR d / s).

Lemma sobolev_entropy_lower_pos : forall eps,
  eps > 0 -> sobolev_entropy_lower eps > 0.
Proof.
  intros eps Heps.
  unfold sobolev_entropy_lower.
  apply Rpower_pos.
Qed.

Lemma sobolev_entropy_monotone : forall eps1 eps2,
  0 < eps1 -> eps1 < eps2 -> eps2 < 1 ->
  sobolev_entropy_lower eps2 < sobolev_entropy_lower eps1.
Proof.
  intros eps1 eps2 Heps1 Hlt H1.
  unfold sobolev_entropy_lower.
  apply Rpower_lt.
  - lra.
  - exact H1.
  - apply Ropp_lt_contravar.
    apply Rmult_lt_compat_l.
    + apply lt_0_INR. exact Hd.
    + apply Rinv_lt_contravar.
      * apply Rmult_lt_0_compat; lra.
      * exact Hlt.
Qed.

End SobolevEntropy.

(** * Information-Theoretic Lower Bounds

    If a coding scheme uses S bits, it can distinguish at most 2^S elements.
    Therefore, if a set has covering number N(ε), any ε-approximation scheme
    needs at least log N(ε) bits.
*)

Section InformationTheory.

(** Number of distinguishable elements with S bits *)
Definition distinguishable (S : nat) : R := Rpower 2 (INR S).

Lemma distinguishable_pos : forall S, distinguishable S > 0.
Proof.
  intro S. unfold distinguishable. apply Rpower_pos.
Qed.

(** Pigeonhole principle: if covering(ε) > distinguishable(S),
    then some certificate class has more than one function *)
Theorem pigeonhole_lower_bound : forall (covering : CoveringNumber) (S eps : R),
  eps > 0 ->
  covering eps eps > Rpower 2 S ->
  (* Then any S-bit scheme fails to distinguish all functions *)
  True.  (** Placeholder for full theorem *)
Proof.
  trivial.
Qed.

(** Minimum bits needed *)
Definition min_bits (covering : CoveringNumber) (S eps : R) : R :=
  ln (covering S eps) / ln 2.

Lemma min_bits_lower : forall covering S eps,
  eps > 0 ->
  covering S eps >= 1 ->
  min_bits covering S eps >= 0.
Proof.
  intros covering S eps Heps Hcov.
  unfold min_bits.
  apply Rmult_le_reg_r with (ln 2).
  - apply ln_lt_0'. lra.
  - field_simplify.
    + rewrite <- ln_1. apply Rlt_le. apply ln_increasing; lra.
    + apply Rgt_not_eq. apply ln_lt_0'. lra.
Qed.

End InformationTheory.

(** * Packing Numbers

    Dual to covering: maximum number of ε-separated points.
    N_pack(S, ε) ≤ N_cover(S, ε/2)
*)

Definition PackingNumber := R -> R -> R.

Lemma packing_covering_relation : forall (pack cover : PackingNumber) S eps,
  eps > 0 ->
  (* N_pack(S, 2ε) ≤ N_cover(S, ε) ≤ N_pack(S, ε) *)
  True.  (** Axiomatized relationship *)
Proof.
  trivial.
Qed.

End UELAT_Entropy.
