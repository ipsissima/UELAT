(** DescentCertificateSize.v -- full certificate-size conclusion for
    authoritative Theorem 7.4 from the H1--H7 resource assembly. *)

From Coq Require Import Arith Lia Ring.
From UELAT.V3 Require Import OrderNeutralDescent H1H7Descent.

Module UELAT_V3_DescentCertificateSize.
Import UELAT_V3_OrderNeutralDescent.
Import UELAT_V3_H1H7Descent.

Section Size.
  Context {X : MetricPresentation}.
  Context {Payload Rule : Type}.
  Variable f : carrier X.
  Variable p : nat -> carrier X.
  Variable H : H1H7Data (Payload:=Payload) (Rule:=Rule) f p.

  Definition precision_proof_bits (s : nat) : nat :=
    nsum_upto (h_new_payload_bits H) (h_mu H s).

  Definition precision_certificate_bits (s : nat) : nat :=
    h_ordinary_bits H (h_mu H s) + precision_proof_bits s.

  Definition size_denominator : nat := h_cnum H * h_Cden H.
  Definition proof_factor : nat :=
    2 * h_cpayload H * h_cden H * h_Cnum H * h_base_factor H.
  Definition total_factor : nat := size_denominator + proof_factor.

  Theorem precision_proof_size_relative_to_B : forall s,
    size_denominator * precision_proof_bits s
      <= proof_factor * h_ordinary_bits H (h_mu H s).
  Proof.
    intro s. unfold size_denominator, precision_proof_bits, proof_factor.
    apply h1h7_genealogy_size.
  Qed.

  Theorem precision_certificate_size_relative_to_B : forall s,
    size_denominator * precision_certificate_bits s
      <= total_factor * h_ordinary_bits H (h_mu H s).
  Proof.
    intro s.
    pose proof (precision_proof_size_relative_to_B s) as Hproof.
    unfold precision_certificate_bits, total_factor.
    unfold precision_proof_bits in Hproof.
    pose proof
      (Nat.mul_le_mono_l size_denominator
        (Nat.le_add_r
          (h_ordinary_bits H (h_mu H s))
          (precision_proof_bits s))) as Hbase.
    ring_nf in Hbase Hproof |- *.
    lia.
  Qed.

  Lemma size_denominator_positive : 0 < size_denominator.
  Proof.
    unfold size_denominator.
    apply Nat.mul_pos_pos.
    - exact (h_cnum_pos H).
    - exact (h_Cden_pos H).
  Qed.
End Size.

End UELAT_V3_DescentCertificateSize.
