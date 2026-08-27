(** SobolevPUFEMAnalyticInterface.v -- standard analytic boundary for v3
    Theorem 5.6. *)

From Coq Require Import Reals List Lra Lra.
Import ListNotations.
From UELAT.V3 Require Import LocalizedPUFEMEvidence.

Module UELAT_V3_SobolevPUFEMAnalyticInterface.
Import UELAT_V3_LocalizedPUFEMEvidence.

Record AnalyticIncidence (Cinf : R) := {
  ai_defect : PairwiseDefectDatum;
  ai_l2_term_sq : R;
  ai_deriv_term_sq : R;
  ai_l2_nonnegative : 0 <= ai_l2_term_sq;
  ai_deriv_nonnegative : 0 <= ai_deriv_term_sq;
  ai_multiplier_bound :
    ai_l2_term_sq <= Cinf^2 * delta0_sq ai_defect;
  ai_product_rule_bound :
    ai_deriv_term_sq <= 2 *
      (Ldelta0_sq ai_defect + Cinf^2 * delta1_sq ai_defect)
}.
Arguments ai_defect {Cinf} _.
Arguments ai_l2_term_sq {Cinf} _.
Arguments ai_deriv_term_sq {Cinf} _.

Fixpoint analytic_defects {Cinf : R} (xs : list (AnalyticIncidence Cinf)) : list PairwiseDefectDatum :=
  match xs with | [] => [] | x :: rest => ai_defect x :: analytic_defects rest end.
Fixpoint sum_l2_terms {Cinf : R} (xs : list (AnalyticIncidence Cinf)) : R :=
  match xs with | [] => 0 | x :: rest => ai_l2_term_sq x + sum_l2_terms rest end.
Fixpoint sum_deriv_terms {Cinf : R} (xs : list (AnalyticIncidence Cinf)) : R :=
  match xs with | [] => 0 | x :: rest => ai_deriv_term_sq x + sum_deriv_terms rest end.

Lemma analytic_sum_l2_bound : forall Cinf xs,
  sum_l2_terms xs <= Cinf^2 * sum_delta0_sq (analytic_defects xs).
Proof.
  intros Cinf xs. induction xs as [|x rest IH]; simpl.
  - nra.
  - pose proof (ai_multiplier_bound x). unfold sum_delta0_sq in *; simpl in *. nra.
Qed.
Lemma analytic_sum_deriv_bound : forall Cinf xs,
  sum_deriv_terms xs <=
    2 * (sum_Ldelta0_sq (analytic_defects xs)
         + Cinf^2 * sum_delta1_sq (analytic_defects xs)).
Proof.
  intros Cinf xs. induction xs as [|x rest IH]; simpl.
  - nra.
  - pose proof (ai_product_rule_bound x).
    unfold sum_Ldelta0_sq, sum_delta1_sq in *; simpl in *. nra.
Qed.
Lemma analytic_sum_l2_nonnegative : forall Cinf xs, 0 <= sum_l2_terms xs.
Proof.
  intros Cinf xs. induction xs as [|x rest IH]; simpl; [lra|].
  pose proof (ai_l2_nonnegative x). lra.
Qed.
Lemma analytic_sum_deriv_nonnegative : forall Cinf xs, 0 <= sum_deriv_terms xs.
Proof.
  intros Cinf xs. induction xs as [|x rest IH]; simpl; [lra|].
  pose proof (ai_deriv_nonnegative x). lra.
Qed.

Record BoundedOverlapAssembly
    (kappa Cinf : R) (xs : list (AnalyticIncidence Cinf)) := {
  boa_global_l2_sq : R;
  boa_global_deriv_sq : R;
  boa_global_l2_nonnegative : 0 <= boa_global_l2_sq;
  boa_global_deriv_nonnegative : 0 <= boa_global_deriv_sq;
  boa_l2_overlap : boa_global_l2_sq <= kappa * sum_l2_terms xs;
  boa_deriv_overlap : boa_global_deriv_sq <= kappa * sum_deriv_terms xs
}.
Arguments boa_global_l2_sq {kappa Cinf xs} _.
Arguments boa_global_deriv_sq {kappa Cinf xs} _.

Section Derivation.
  Variables kappa Cinf : R.
  Hypothesis Hkappa : 0 <= kappa.
  Hypothesis HCinf : 0 <= Cinf.
  Variable xs : list (AnalyticIncidence Cinf).
  Variable A : BoundedOverlapAssembly kappa Cinf xs.

  Definition derived_component_evidence :
      ComponentEvidence kappa Cinf (analytic_defects xs).
  Proof.
    refine {| component_l2_sq := boa_global_l2_sq A;
              component_deriv_sq := boa_global_deriv_sq A;
              component_l2_nonnegative := boa_global_l2_nonnegative A;
              component_deriv_nonnegative := boa_global_deriv_nonnegative A |}.
    - eapply Rle_trans; [apply boa_l2_overlap|].
      apply Rmult_le_compat_l; [exact Hkappa|]. apply analytic_sum_l2_bound.
    - eapply Rle_trans; [apply boa_deriv_overlap|].
      apply Rmult_le_compat_l; [exact Hkappa|]. apply analytic_sum_deriv_bound.
  Defined.

  Definition compiled_analytic_localized_defect :
      CompiledLocalizedDefect kappa Cinf (analytic_defects xs)
        derived_component_evidence :=
    compile_localized_defect kappa Cinf Hkappa HCinf
      (analytic_defects xs) derived_component_evidence.

  Theorem localized_pufem_from_standard_analytic_primitives :
    boa_global_l2_sq A + boa_global_deriv_sq A
      <= manuscript_R kappa Cinf (analytic_defects xs).
  Proof. exact (cld_total_defect_bound compiled_analytic_localized_defect). Qed.

  Theorem localized_pufem_bound_is_corrected_formula :
    cld_bound compiled_analytic_localized_defect
      = manuscript_R kappa Cinf (analytic_defects xs).
  Proof. apply cld_bound_is_manuscript_R. Qed.
End Derivation.

End UELAT_V3_SobolevPUFEMAnalyticInterface.
