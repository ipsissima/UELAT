(** H6EncodingRegime.v -- the two-sided finite-encoding part of manuscript H6. *)

From Coq Require Import Arith Nia.
From UELAT.V3 Require Import H1H7Descent.

Module UELAT_V3_H6EncodingRegime.
Import UELAT_V3_H1H7Descent.

Section Encoding.
  Context {X : MetricPresentation}.
  Context {Payload Rule : Type}.
  Variable f : carrier X.
  Variable p : nat -> carrier X.
  Variable H : H1H7Data (Payload:=Payload) (Rule:=Rule) f p.

  Record TwoSidedEncoding := {
    ordinary_upper_factor : nat;
    ordinary_upper : forall n,
      h_ordinary_bits H n
        <= ordinary_upper_factor * h_M H n * h_beta H n
  }.

  Variable E : TwoSidedEncoding.

  Theorem ordinary_bits_two_sided : forall n,
    h_M H n * h_beta H n
      <= h_base_factor H * h_ordinary_bits H n
    /\
    h_ordinary_bits H n
      <= ordinary_upper_factor E * h_M H n * h_beta H n.
  Proof.
    intro n. split.
    - apply h_baseline_dominates.
    - apply ordinary_upper.
  Qed.
End Encoding.

End UELAT_V3_H6EncodingRegime.
