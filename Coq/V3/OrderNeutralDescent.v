(** OrderNeutralDescent.v -- quantitative resource core of authoritative
    Section 7. Geometric dyadic refinement makes earlier proof payloads
    summable relative to the finest relevant level.
*)

From Coq Require Import Arith Lia List.

Module UELAT_V3_OrderNeutralDescent.

Fixpoint nsum_upto (f : nat -> nat) (n : nat) : nat :=
  match n with | O => f 0 | S k => nsum_upto f k + f (S k) end.

Lemma nsum_upto_le : forall f g n,
  (forall j, j <= n -> f j <= g j) ->
  nsum_upto f n <= nsum_upto g n.
Proof.
  intros f g n H. induction n as [|n IH].
  - simpl. apply H. lia.
  - simpl. apply Nat.add_le_mono.
    + apply IH. intros j Hj. apply H. lia.
    + apply H. lia.
Qed.

Lemma nsum_upto_scale : forall c f n,
  nsum_upto (fun j => c * f j) n = c * nsum_upto f n.
Proof. intros c f n. induction n; simpl; nia. Qed.

Definition pow2 (n : nat) : nat := Nat.pow 2 n.

Lemma pow2_positive : forall n, 0 < pow2 n.
Proof.
  intro n. unfold pow2. induction n; simpl; nia.
Qed.

Lemma sum_pow2 : forall n,
  nsum_upto pow2 n = pow2 (S n) - 1.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - simpl nsum_upto. rewrite IH.
    pose proof (pow2_positive (S n)) as Hpos.
    unfold pow2 in *.
    simpl Nat.pow.
    nia.
Qed.

Section DyadicGeometry.
  Variable M0 : nat.
  Hypothesis HM0 : 0 < M0.
  Definition M (n : nat) : nat := M0 * pow2 n.

  Lemma M_positive : forall n, 0 < M n.
  Proof. intro n. unfold M. pose proof (pow2_positive n). nia. Qed.

  Lemma sum_M_exact : forall n,
    nsum_upto M n = M0 * (pow2 (S n) - 1).
  Proof. intro n. unfold M. rewrite nsum_upto_scale, sum_pow2. reflexivity. Qed.

  Theorem dyadic_patch_sum : forall n,
    nsum_upto M n <= 2 * M n.
  Proof.
    intro n. rewrite sum_M_exact. unfold M.
    pose proof (pow2_positive n) as Hp. unfold pow2 in *. simpl Nat.pow. nia.
  Qed.

  Variables beta payload_bits : nat -> nat.
  Variable c_payload : nat.
  Hypothesis beta_positive : forall n, 0 < beta n.
  Hypothesis beta_monotone : forall j n, j <= n -> beta j <= beta n.
  Hypothesis payload_level_bound : forall n,
      payload_bits n <= c_payload * M n * beta n.

  Lemma payload_sum_bound_by_patch_sum : forall n,
    nsum_upto payload_bits n <= c_payload * beta n * nsum_upto M n.
  Proof.
    intro n. eapply Nat.le_trans.
    - apply nsum_upto_le. intros j Hj.
      eapply Nat.le_trans.
      + apply payload_level_bound.
      + replace (c_payload * beta n * M j)
          with ((c_payload * M j) * beta n) by nia.
        apply Nat.mul_le_mono_l.
        apply beta_monotone. exact Hj.
    - change (nsum_upto (fun j => (c_payload * beta n) * M j) n
              <= c_payload * beta n * nsum_upto M n).
      rewrite nsum_upto_scale. reflexivity.
  Qed.

  Theorem genealogy_sums_to_finest_level : forall n,
    nsum_upto payload_bits n <= 2 * c_payload * M n * beta n.
  Proof.
    intro n. eapply Nat.le_trans.
    - apply payload_sum_bound_by_patch_sum.
    - pose proof (dyadic_patch_sum n). nia.
  Qed.

  Variable ordinary_bits : nat -> nat.
  Variable base_factor : nat.
  Hypothesis baseline_dominates : forall n,
    M n * beta n <= base_factor * ordinary_bits n.

  Theorem order_neutral_relative_to_baseline : forall n,
    nsum_upto payload_bits n <= 2 * c_payload * base_factor * ordinary_bits n.
  Proof.
    intro n. pose proof (genealogy_sums_to_finest_level n) as Hg.
    pose proof (baseline_dominates n) as Hb. nia.
  Qed.

  Variable beta_factor : nat.
  Hypothesis beta_linear : forall n,
    beta n <= beta_factor * S n.

  Corollary standard_rational_depth_bound : forall n,
    nsum_upto payload_bits n
      <= 2 * c_payload * M0 * beta_factor * pow2 n * S n.
  Proof.
    intro n. pose proof (genealogy_sums_to_finest_level n) as Hg.
    specialize (beta_linear n) as Hb. unfold M in Hg. nia.
  Qed.
End DyadicGeometry.

Definition descent_target_query : nat := 0.
Theorem descent_target_query_zero : descent_target_query = 0.
Proof. reflexivity. Qed.

End UELAT_V3_OrderNeutralDescent.
