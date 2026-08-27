(** DescentAssembly.v -- represented-limit and resource assembly for
    authoritative Section 7.
*)

From Coq Require Import Reals Arith Lia Nia Lra.
From UELAT.V3 Require Import
  CertificateEnrichment RepresentedSpace OrderNeutralDescent.

Module UELAT_V3_DescentAssembly.
Import UELAT_V3_CertificateEnrichment.
Import UELAT_V3_RepresentedSpace.
Import UELAT_V3_OrderNeutralDescent.

Lemma dyadic_step_le : forall n, dyadic (S n) <= dyadic n.
Proof.
  intro n. simpl. pose proof (dyadic_nonnegative n). lra.
Qed.

Lemma dyadic_antitone : forall n m,
  n <= m -> dyadic m <= dyadic n.
Proof.
  intros n m Hnm. induction Hnm.
  - lra.
  - eapply Rle_trans.
    + apply dyadic_step_le.
    + exact IHHnm.
Qed.

Section RepresentedLimit.
  Context {X : MetricPresentation}.
  Variable f : carrier X.
  Variable p : nat -> carrier X.
  Variable mu : nat -> nat.
  Hypothesis scheduled_error : forall s,
    distance f (p (mu s)) <= dyadic s / 2.

  Definition descent_fast_name : FastCauchyName X.
  Proof.
    refine {| approximant := fun s => p (mu s) |}.
    intros m n Hnm.
    eapply Rle_trans.
    - apply distance_triangle with (y := f).
    - rewrite distance_symmetric with (x := p (mu m)) (y := f).
      pose proof (scheduled_error m) as Hm.
      pose proof (scheduled_error n) as Hn.
      pose proof (dyadic_antitone n m Hnm) as Hdy.
      nra.
  Defined.

  Definition descent_represented_point : RepresentedPoint X.
  Proof.
    refine {| represented_value := f;
              represented_name := descent_fast_name;
              represented_tail := _ |}.
    intro s. specialize (scheduled_error s).
    pose proof (dyadic_nonnegative s). lra.
  Defined.

  Theorem descent_name_stage : forall s,
    approximant (represented_name descent_represented_point) s = p (mu s).
  Proof. reflexivity. Qed.

  Definition represented_limit_target_queries : nat := 0.
  Theorem represented_limit_target_query_zero :
    represented_limit_target_queries = 0.
  Proof. reflexivity. Qed.
End RepresentedLimit.

Section ResourceAssembly.
  Variable M0 : nat.
  Hypothesis HM0 : 0 < M0.
  Variables beta payload_bits ordinary_bits : nat -> nat.
  Variables c_payload base_factor : nat.

  Hypothesis beta_positive : forall n, 0 < beta n.
  Hypothesis beta_monotone : forall j n, j <= n -> beta j <= beta n.
  Hypothesis payload_level_bound : forall n,
    payload_bits n <= c_payload * (M0 * pow2 n) * beta n.
  Hypothesis baseline_dominates : forall n,
    (M0 * pow2 n) * beta n <= base_factor * ordinary_bits n.

  Theorem assembled_genealogy_size : forall n,
    nsum_upto payload_bits n
      <= 2 * c_payload * base_factor * ordinary_bits n.
  Proof.
    intro n.
    exact (@order_neutral_relative_to_baseline
      M0 HM0 beta payload_bits c_payload
      beta_positive beta_monotone payload_level_bound
      ordinary_bits base_factor baseline_dominates n).
  Qed.

  Variable A : nat -> nat.
  Hypothesis A_monotone : forall a b, a <= b -> A a <= A b.
  Variable level_verification : nat -> nat.
  Variable c_verify : nat.
  Hypothesis verification_level_bound : forall n,
    level_verification n <= c_verify * (M0 * pow2 n) * A (beta n).

  Lemma verification_scale_monotone : forall j n,
    j <= n -> A (beta j) <= A (beta n).
  Proof. intros j n Hjn. apply A_monotone. now apply beta_monotone. Qed.

  Lemma verification_sum_bound_by_patches : forall n,
    nsum_upto level_verification n
      <= c_verify * A (beta n)
           * nsum_upto (fun j => M0 * pow2 j) n.
  Proof.
    intro n. eapply Nat.le_trans.
    - apply nsum_upto_le. intros j Hj.
      specialize (verification_level_bound j) as Hv.
      specialize (verification_scale_monotone j n Hj) as HA. nia.
    - change (nsum_upto
                (fun j => (c_verify * A (beta n)) * (M0 * pow2 j)) n
              <= c_verify * A (beta n)
                 * nsum_upto (fun j => M0 * pow2 j) n).
      rewrite nsum_upto_scale. reflexivity.
  Qed.

  Theorem assembled_verification_bound : forall n,
    nsum_upto level_verification n
      <= 2 * c_verify * (M0 * pow2 n) * A (beta n).
  Proof.
    intro n. eapply Nat.le_trans.
    - apply verification_sum_bound_by_patches.
    - pose proof (@dyadic_patch_sum M0 HM0 n) as Hsum.
      unfold M in Hsum. nia.
  Qed.

  Variable source_lookahead : nat -> nat.
  Variable c_source beta_factor : nat.
  Hypothesis source_level_bound : forall n,
    source_lookahead n <= c_source * beta n.
  Hypothesis beta_linear : forall n,
    beta n <= beta_factor * S n.

  Theorem assembled_source_lookahead : forall n,
    source_lookahead n <= c_source * beta_factor * S n.
  Proof.
    intro n. pose proof (source_level_bound n).
    pose proof (beta_linear n). nia.
  Qed.

  Definition assembled_target_lookahead : nat := 0.
  Theorem assembled_target_lookahead_zero : assembled_target_lookahead = 0.
  Proof. reflexivity. Qed.
End ResourceAssembly.

End UELAT_V3_DescentAssembly.
