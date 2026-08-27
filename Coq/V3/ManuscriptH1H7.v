(** ManuscriptH1H7.v -- semantic strengthening of the H1--H7 interface for
    authoritative Theorem 7.4.

    H1H7Descent.v contains the resource/refinement proof, but its H2/H3
    certificate fields are intentionally abstract. This file records the
    mathematical content required by manuscript H2--H4: rational partition
    bounds, local order-r L2/derivative approximation rates, and the global
    geometric scale estimate. The theorem remains conditional on supplied
    local approximation evidence; no approximation oracle is invented here.
*)

From Coq Require Import Reals Arith List Lia Lra.
Import ListNotations.
From UELAT.V3 Require Import
  CertificateEnrichment RepresentedSpace H1H7Descent
  RationalSobolev RationalPUFEM OrderNeutralEpsilonDescent.

Module UELAT_V3_ManuscriptH1H7.
Import UELAT_V3_CertificateEnrichment.
Import UELAT_V3_RepresentedSpace.
Import UELAT_V3_H1H7Descent.
Import UELAT_V3_RationalSobolev.
Import UELAT_V3_RationalPUFEM.
Import UELAT_V3_OrderNeutralEpsilonDescent.

Section StrengthenedHypotheses.
  Context {X : MetricPresentation}.
  Context {Payload Rule : Type}.
  Variable f : carrier X.
  Variable p : nat -> carrier X.
  Variable H : H1H7Data (Payload:=Payload) (Rule:=Rule) f p.

  Variable Cchi C0 C1 Rbound : R.
  Variable r : nat.

  Record H2PartitionEvidence (n : nat) := {
    h2_terms : list PartitionDatum;
    h2_patch_count : length h2_terms = h_M H n;
    h2_sup_at_most_one :
      Forall (fun psi => partition_sup_bound psi <= 1) h2_terms;
    h2_derivative_scale :
      Forall (fun psi => partition_deriv_bound psi * dyadic n <= Cchi) h2_terms;
    h2_certificate : h_partition_certificate H n
  }.

  Record H3LocalApproximationEvidence (n a : nat) := {
    h3_code : RationalPiecewiseCode;
    h3_local_seminorm : R;
    h3_local_seminorm_nonnegative : 0 <= h3_local_seminorm;
    h3_l2_error : R;
    h3_deriv_error : R;
    h3_l2_error_nonnegative : 0 <= h3_l2_error;
    h3_deriv_error_nonnegative : 0 <= h3_deriv_error;
    h3_l2_rate :
      h3_l2_error <= C0 * (dyadic n) ^ r * h3_local_seminorm;
    h3_deriv_rate :
      h3_deriv_error <= C1 * (dyadic n) ^ (Nat.pred r) * h3_local_seminorm;
    h3_certificate : h_local_certificate H n a
  }.

  Record H4SynthesisEvidence (n : nat) := {
    h4_certificate : h_synthesis_certificate H n;
    h4_scale_bound :
      distance f (p n) <= h_K H * dyadic (h_alpha H * n)
  }.

  Record ManuscriptH1H7Data := {
    mh_r_ge_2 : 2 <= r;
    mh_alpha_is_r_minus_1 : h_alpha H = Nat.pred r;
    mh_Cchi_nonnegative : 0 <= Cchi;
    mh_C0_nonnegative : 0 <= C0;
    mh_C1_nonnegative : 0 <= C1;
    mh_R_nonnegative : 0 <= Rbound;
    mh_partition : forall n, H2PartitionEvidence n;
    mh_local : forall n a,
      a < h_M H n -> H3LocalApproximationEvidence n a;
    mh_synthesis : forall n, H4SynthesisEvidence n
  }.

  Variable MH : ManuscriptH1H7Data.

  Theorem manuscript_h4_agrees_with_core : forall n,
    distance f (p n) <= h_K H * dyadic (h_alpha H * n).
  Proof. intro n. exact (h4_scale_bound (mh_synthesis MH n)). Qed.

  Theorem manuscript_alpha_positive : 0 < Nat.pred r.
  Proof. pose proof (mh_r_ge_2 MH). lia. Qed.

  Theorem manuscript_partition_count : forall n,
    length (h2_terms (mh_partition MH n)) = h_M H n.
  Proof. intro n. apply h2_patch_count. Qed.

  Theorem manuscript_local_evidence_exists : forall n a,
    a < h_M H n -> exists c : RationalPiecewiseCode,
      exists e0 e1 seminorm : R,
        0 <= e0 /\ 0 <= e1 /\ 0 <= seminorm
        /\ e0 <= C0 * (dyadic n)^r * seminorm
        /\ e1 <= C1 * (dyadic n)^(Nat.pred r) * seminorm.
  Proof.
    intros n a Ha.
    pose (E := mh_local MH n a Ha).
    exists (h3_code E), (h3_l2_error E), (h3_deriv_error E),
      (h3_local_seminorm E).
    repeat split.
    - apply h3_l2_error_nonnegative.
    - apply h3_deriv_error_nonnegative.
    - apply h3_local_seminorm_nonnegative.
    - apply h3_l2_rate.
    - apply h3_deriv_rate.
  Qed.
End StrengthenedHypotheses.

End UELAT_V3_ManuscriptH1H7.
