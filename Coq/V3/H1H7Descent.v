(** H1H7Descent.v -- manuscript-shaped assembly for the authoritative v3
    encoding-cost evidence-transport theorem (Theorem 7.4).

    The core record contains only H1--H7. The manuscript's additional linear
    beta schedule and source-lookahead hypothesis are represented separately.
*)

From Coq Require Import Reals Arith Lia Nia List.
Import ListNotations.
From UELAT.V3 Require Import
  CertificateEnrichment RepresentedSpace ProofDAG
  OrderNeutralDescent QuasiUniformGeometry DescentAssembly
  GeometricPrecisionSchedule.

Module UELAT_V3_H1H7Descent.
Import UELAT_V3_CertificateEnrichment.
Import UELAT_V3_RepresentedSpace.
Import UELAT_V3_ProofDAG.
Import UELAT_V3_OrderNeutralDescent.
Import UELAT_V3_QuasiUniformGeometry.
Import UELAT_V3_DescentAssembly.
Import UELAT_V3_GeometricPrecisionSchedule.

Definition history_extends {Payload Rule}
    (H H' : ProofDAG Payload Rule) : Prop :=
  forall i node,
    nth_error (dag_nodes H) i = Some node ->
    nth_error (dag_nodes H') i = Some node.

Section FullInterface.
  Context {X : MetricPresentation}.
  Context {Payload Rule : Type}.
  Variable f : carrier X.
  Variable p : nat -> carrier X.

  Record H1H7Data := {
    (** H1 -- quasi-uniform geometry and bounded incidence. *)
    h_M : nat -> nat;
    h_cnum : nat; h_cden : nat; h_Cnum : nat; h_Cden : nat;
    h_cnum_pos : 0 < h_cnum;
    h_cden_pos : 0 < h_cden;
    h_Cnum_pos : 0 < h_Cnum;
    h_Cden_pos : 0 < h_Cden;
    h_quasi_lower : forall n,
      h_cnum * pow2 n <= h_cden * h_M n;
    h_quasi_upper : forall n,
      h_Cden * h_M n <= h_Cnum * pow2 n;
    h_overlap h_neighbor_degree h_refinement_degree : nat;
    h_overlap_pos : 0 < h_overlap;
    h_neighbor_degree_pos : 0 < h_neighbor_degree;
    h_refinement_degree_pos : 0 < h_refinement_degree;
    h_refinement_incidences : nat -> nat;
    h_refinement_incidence_bound : forall n,
      h_refinement_incidences n <= h_refinement_degree * h_M (S n);

    (** H2/H3 -- supplied finite certified partition/local data. *)
    h_partition_certificate : nat -> Type;
    h_partition_supplied : forall n, h_partition_certificate n;
    h_local_certificate : nat -> nat -> Type;
    h_local_supplied : forall n a, a < h_M n -> h_local_certificate n a;

    (** H4 -- exact synthesis and the geometric scale law. *)
    h_synthesis_certificate : nat -> Type;
    h_synthesis_supplied : forall n, h_synthesis_certificate n;
    h_alpha : nat;
    h_alpha_positive : 0 < h_alpha;
    h_offset : nat;
    h_K : R;
    h_K_nonnegative : 0 <= h_K;
    h_offset_absorbs_K : h_K * dyadic h_offset <= 1;
    h_geometric_level_error : forall n,
      distance f (p n) <= h_K * dyadic (h_alpha * n);

    (** H5 -- persistent evidence-local genealogy and Q_target=0. *)
    h_history : nat -> ProofDAG Payload Rule;
    h_history_persistent : forall n,
      history_extends (h_history n) (h_history (S n));
    h_target_queries : nat;
    h_no_target_recertification : h_target_queries = 0;

    (** H6 -- coefficient-wise encoding and new proof payload. *)
    h_beta : nat -> nat;
    h_beta_positive : forall n, 0 < h_beta n;
    h_beta_monotone : forall j n, j <= n -> h_beta j <= h_beta n;
    h_ordinary_bits : nat -> nat;
    h_new_payload_bits : nat -> nat;
    h_cpayload h_base_factor : nat;
    h_payload_level_bound : forall n,
      h_new_payload_bits n <= h_cpayload * h_M n * h_beta n;
    h_baseline_dominates : forall n,
      h_M n * h_beta n <= h_base_factor * h_ordinary_bits n;

    (** H7 -- fixed-arity arithmetic verification model. *)
    h_A : nat -> nat;
    h_A_monotone : forall a b, a <= b -> h_A a <= h_A b;
    h_level_verification : nat -> nat;
    h_cverify : nat;
    h_verification_level_bound : forall n,
      h_level_verification n <= h_cverify * h_M n * h_A (h_beta n)
  }.

  (** Additional assumption used for the explicit standard-rational asymptotic
      in Theorem 7.4 / Corollary 7.5. *)
  Record LinearBitRegime (H : H1H7Data) := {
    lb_beta_factor : nat;
    lb_beta_linear : forall n,
      h_beta H n <= lb_beta_factor * S n
  }.

  (** Additional source-generation hypothesis for the conditional Q_source
      clause. It is separate even from the linear-bit assumption. *)
  Record SourceLookaheadRegime (H : H1H7Data) (LB : LinearBitRegime H) := {
    sr_source_lookahead : nat -> nat;
    sr_csource : nat;
    sr_source_level_bound : forall n,
      sr_source_lookahead n <= sr_csource * h_beta H n
  }.

  Section Consequences.
    Variable H : H1H7Data.

    Definition h_mu (s : nat) : nat :=
      geometric_precision_schedule (h_alpha H) (h_offset H) s.

    Lemma h_scheduled_error : forall s,
      distance f (p (h_mu s)) <= dyadic s / 2.
    Proof.
      intro s.
      exact (@scheduled_geometric_error
        X f p (h_alpha H) (h_offset H) (h_K H)
        (h_alpha_positive H) (h_K_nonnegative H)
        (h_offset_absorbs_K H) (h_geometric_level_error H) s).
    Qed.

    Definition h1h7_fast_name : FastCauchyName X :=
      descent_fast_name f p h_mu h_scheduled_error.

    Definition h1h7_represented_limit : RepresentedPoint X :=
      descent_represented_point f p h_mu h_scheduled_error.

    Theorem h1h7_limit_is_f :
      represented_value h1h7_represented_limit = f.
    Proof. reflexivity. Qed.

    Theorem h1h7_name_stage : forall s,
      approximant (represented_name h1h7_represented_limit) s = p (h_mu s).
    Proof. reflexivity. Qed.

    Theorem h_mu_exponent_dominates : forall s,
      s + 1 + h_offset H <= h_alpha H * h_mu s.
    Proof.
      intro s.
      apply geometric_precision_exponent_dominates.
      exact (h_alpha_positive H).
    Qed.

    Record PrecisionGenealogy (s : nat) := {
      pg_level : nat;
      pg_level_is_schedule : pg_level = h_mu s;
      pg_approximant : carrier X;
      pg_approximant_is_level : pg_approximant = p pg_level;
      pg_history : ProofDAG Payload Rule;
      pg_history_is_level : pg_history = h_history H pg_level
    }.

    Definition precision_genealogy (s : nat) : PrecisionGenealogy s :=
      {| pg_level := h_mu s;
         pg_level_is_schedule := eq_refl;
         pg_approximant := p (h_mu s);
         pg_approximant_is_level := eq_refl;
         pg_history := h_history H (h_mu s);
         pg_history_is_level := eq_refl |}.

    Lemma h1h7_patch_sum : forall n,
      h_cnum H * h_Cden H * nsum_upto (h_M H) n
        <= 2 * h_cden H * h_Cnum H * h_M H n.
    Proof.
      intro n.
      exact (@quasi_uniform_patch_sum
        (h_M H)
        (h_cnum H) (h_cden H) (h_Cnum H) (h_Cden H)
        (h_cnum_pos H) (h_cden_pos H) (h_Cnum_pos H) (h_Cden_pos H)
        (h_quasi_lower H) (h_quasi_upper H) n).
    Qed.

    Theorem h1h7_genealogy_size : forall n,
      h_cnum H * h_Cden H * nsum_upto (h_new_payload_bits H) n
        <= 2 * h_cpayload H * h_cden H * h_Cnum H
             * h_base_factor H * h_ordinary_bits H n.
    Proof.
      intro n.
      pose proof (@payload_sum_scaled
        (h_M H)
        (h_cnum H) (h_cden H) (h_Cnum H) (h_Cden H)
        (h_cnum_pos H) (h_cden_pos H) (h_Cnum_pos H) (h_Cden_pos H)
        (h_quasi_lower H) (h_quasi_upper H)
        (h_beta H) (h_new_payload_bits H) (h_cpayload H)
        (h_beta_monotone H) (h_payload_level_bound H) n) as Hpayload.
      pose proof (h_baseline_dominates H n) as Hbase.
      nia.
    Qed.

    Lemma verification_scale_monotone_h1h7 : forall j n,
      j <= n -> h_A H (h_beta H j) <= h_A H (h_beta H n).
    Proof.
      intros j n Hjn.
      apply h_A_monotone.
      now apply h_beta_monotone.
    Qed.

    Theorem h1h7_verification_bound : forall n,
      h_cnum H * h_Cden H * nsum_upto (h_level_verification H) n
        <= 2 * h_cverify H * h_cden H * h_Cnum H
             * h_M H n * h_A H (h_beta H n).
    Proof.
      intro n.
      assert (Hsum : nsum_upto (h_level_verification H) n
               <= h_cverify H * h_A H (h_beta H n)
                    * nsum_upto (h_M H) n).
      { eapply Nat.le_trans.
        - apply nsum_upto_le.
          intros j Hj.
          pose proof (h_verification_level_bound H j) as Hv.
          pose proof (verification_scale_monotone_h1h7 j n Hj) as HA.
          nia.
        - change (nsum_upto
                    (fun j => (h_cverify H * h_A H (h_beta H n)) * h_M H j) n
                  <= h_cverify H * h_A H (h_beta H n)
                     * nsum_upto (h_M H) n).
          rewrite nsum_upto_scale. reflexivity. }
      pose proof (h1h7_patch_sum n) as Hgeom.
      nia.
    Qed.

    Theorem h1h7_target_query_zero : h_target_queries H = 0.
    Proof. exact (h_no_target_recertification H). Qed.

    Theorem h1h7_order_neutral_at_precision : forall s,
      represented_value h1h7_represented_limit = f
      /\ approximant (represented_name h1h7_represented_limit) s = p (h_mu s)
      /\ h_cnum H * h_Cden H
           * nsum_upto (h_new_payload_bits H) (h_mu s)
           <= 2 * h_cpayload H * h_cden H * h_Cnum H
                * h_base_factor H * h_ordinary_bits H (h_mu s)
      /\ h_cnum H * h_Cden H
           * nsum_upto (h_level_verification H) (h_mu s)
           <= 2 * h_cverify H * h_cden H * h_Cnum H
                * h_M H (h_mu s) * h_A H (h_beta H (h_mu s))
      /\ h_target_queries H = 0.
    Proof.
      intro s.
      repeat split.
      - apply h1h7_limit_is_f.
      - apply h1h7_name_stage.
      - apply h1h7_genealogy_size.
      - apply h1h7_verification_bound.
      - apply h1h7_target_query_zero.
    Qed.

    Section LinearBits.
      Variable LB : LinearBitRegime H.

      Theorem h1h7_beta_linear_at_level : forall n,
        h_beta H n <= lb_beta_factor LB * S n.
      Proof. intro n. apply lb_beta_linear. Qed.

      Section OptionalSourceLookahead.
        Variable SR : SourceLookaheadRegime H LB.

        Theorem h1h7_source_lookahead_bound : forall n,
          sr_source_lookahead SR n
            <= sr_csource SR * lb_beta_factor LB * S n.
        Proof.
          intro n.
          pose proof (sr_source_level_bound SR n).
          pose proof (lb_beta_linear LB n).
          nia.
        Qed.

        Theorem h1h7_source_lookahead_at_precision : forall s,
          sr_source_lookahead SR (h_mu s)
            <= sr_csource SR * lb_beta_factor LB * S (h_mu s).
        Proof. intro s. apply h1h7_source_lookahead_bound. Qed.
      End OptionalSourceLookahead.
    End LinearBits.
  End Consequences.
End FullInterface.

End UELAT_V3_H1H7Descent.
