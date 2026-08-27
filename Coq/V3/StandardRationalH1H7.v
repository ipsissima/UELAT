(** StandardRationalH1H7.v -- authoritative Corollary 7.5 on the H1--H7 path.

    Under B_n=O(M_n beta_n), beta_n=O(n+1), and quasi-uniform M_n=O(2^n),
    the ordinary encoding is O(2^n(n+1)); the proof-carrying theorem has the
    same selected-level order. The selected level is linear in the dyadic
    precision exponent, hence logarithmic in epsilon after EpsilonPrecision.
*)

From Coq Require Import Arith Lia Nia.
From UELAT.V3 Require Import
  OrderNeutralDescent H1H7Descent DescentCertificateSize H6EncodingRegime.

Module UELAT_V3_StandardRationalH1H7.
Import UELAT_V3_OrderNeutralDescent.
Import UELAT_V3_H1H7Descent.
Import UELAT_V3_DescentCertificateSize.
Import UELAT_V3_H6EncodingRegime.

Section StandardRegime.
  Context {X : MetricPresentation}.
  Context {Payload Rule : Type}.
  Variable f : carrier X.
  Variable p : nat -> carrier X.
  Variable H : H1H7Data (Payload:=Payload) (Rule:=Rule) f p.
  Variable E : TwoSidedEncoding H.

  Theorem ordinary_encoding_standard_depth_bound : forall n,
    h_Cden H * h_ordinary_bits H n
      <= ordinary_upper_factor E * h_Cnum H * h_beta_factor H
           * pow2 n * S n.
  Proof.
    intro n.
    pose proof (ordinary_upper E n) as HB.
    pose proof (h_quasi_upper H n) as HM.
    pose proof (h_beta_linear H n) as Hbeta.
    nia.
  Qed.

  Theorem full_certificate_standard_depth_bound : forall s,
    size_denominator H * h_Cden H * precision_certificate_bits H s
      <= total_factor H * ordinary_upper_factor E
           * h_Cnum H * h_beta_factor H
           * pow2 (h_mu H s) * S (h_mu H s).
  Proof.
    intro s.
    pose proof (precision_certificate_size_relative_to_B H s) as Hcert.
    pose proof (ordinary_encoding_standard_depth_bound (h_mu H s)) as HB.
    nia.
  Qed.

  Theorem selected_level_linear_in_precision_exponent : forall s,
    h_mu H s <= S (s + 1 + h_offset H).
  Proof.
    intro s.
    unfold h_mu, geometric_precision_schedule.
    assert (Halpha0 : h_alpha H <> 0) by
      (pose proof (h_alpha_positive H); lia).
    assert (Hdiv :
      (s + 1 + h_offset H) / h_alpha H <= s + 1 + h_offset H).
    { apply Nat.div_le_upper_bound.
      - exact Halpha0.
      - pose proof (h_alpha_positive H). nia. }
    lia.
  Qed.
End StandardRegime.

End UELAT_V3_StandardRationalH1H7.
