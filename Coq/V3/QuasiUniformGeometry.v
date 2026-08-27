(** QuasiUniformGeometry.v -- H1 geometric summability for authoritative
    Theorem 7.4.
*)

From Coq Require Import Arith Lia Lia.
From UELAT.V3 Require Import OrderNeutralDescent.

Module UELAT_V3_QuasiUniformGeometry.
Import UELAT_V3_OrderNeutralDescent.

Section Geometry.
  Variable M : nat -> nat.
  Variables c_num c_den C_num C_den : nat.

  Hypothesis c_num_pos : 0 < c_num.
  Hypothesis c_den_pos : 0 < c_den.
  Hypothesis C_num_pos : 0 < C_num.
  Hypothesis C_den_pos : 0 < C_den.

  Hypothesis quasi_lower : forall n,
    c_num * pow2 n <= c_den * M n.
  Hypothesis quasi_upper : forall n,
    C_den * M n <= C_num * pow2 n.

  Lemma scaled_patch_sum_upper : forall n,
    C_den * nsum_upto M n <= C_num * nsum_upto pow2 n.
  Proof.
    intro n. rewrite <- nsum_upto_scale. rewrite <- nsum_upto_scale.
    apply nsum_upto_le. intros j Hj. apply quasi_upper.
  Qed.

  Lemma sum_pow2_le_twice_finest : forall n,
    nsum_upto pow2 n <= 2 * pow2 n.
  Proof.
    intro n. rewrite sum_pow2. pose proof (pow2_positive n) as Hp.
    unfold pow2 in *. simpl Nat.pow. nia.
  Qed.

  Theorem quasi_uniform_patch_sum : forall n,
    c_num * C_den * nsum_upto M n
      <= 2 * c_den * C_num * M n.
  Proof.
    intro n.
    pose proof (scaled_patch_sum_upper n) as Hsum.
    pose proof (sum_pow2_le_twice_finest n) as Hpow.
    pose proof (quasi_lower n) as Hlow.
    nia.
  Qed.

  Variables beta payload_bits : nat -> nat.
  Variable c_payload : nat.
  Hypothesis beta_monotone : forall j n, j <= n -> beta j <= beta n.
  Hypothesis payload_level_bound : forall n,
    payload_bits n <= c_payload * M n * beta n.

  Lemma payload_sum_scaled : forall n,
    c_num * C_den * nsum_upto payload_bits n
      <= 2 * c_payload * c_den * C_num * M n * beta n.
  Proof.
    intro n.
    assert (Hraw : nsum_upto payload_bits n
              <= c_payload * beta n * nsum_upto M n).
    { eapply Nat.le_trans.
      - apply nsum_upto_le. intros j Hj.
        specialize (payload_level_bound j) as Hp.
        specialize (beta_monotone j n Hj) as Hb. nia.
      - change (nsum_upto (fun j => (c_payload * beta n) * M j) n
                  <= c_payload * beta n * nsum_upto M n).
        rewrite nsum_upto_scale. reflexivity. }
    pose proof (quasi_uniform_patch_sum n) as Hgeom.
    nia.
  Qed.
End Geometry.

End UELAT_V3_QuasiUniformGeometry.
