(** WeightedSynthesisBudget.v -- authoritative Proposition 6.3 as one package.

    RationalSynthesis.v supplies exact finite code/evidence synthesis and
    PUFEMCompiler.v supplies the current manuscript weight

      w_i^2 = max { C_inf^2 + 2 L_i^2, 2 C_inf^2 }.

    The local hypothesis is the genuine squared W12 budget A_i+D_i<=alpha_i^2.
*)

From Coq Require Import Reals List Lra.
Import ListNotations.
From UELAT.V3 Require Import RationalSobolev RationalSynthesis PUFEMCompiler.

Module UELAT_V3_WeightedSynthesisBudget.
Import UELAT_V3_RationalSobolev.
Import UELAT_V3_RationalSynthesis.
Import UELAT_V3_PUFEMCompiler.

Section Package.
  Variable Rules : SynthesisRuleSystem.
  Variable xs : SynthesisInput Rules.
  Variables kappa Cinf epsilon : R.
  Hypothesis Hkappa : 0 <= kappa.
  Hypothesis Hepsilon : 0 < epsilon.
  Variables Ls l2s derivs alphas : list R.
  Hypothesis Hlocal : local_w12_error_budget l2s derivs alphas.
  Hypothesis Hlength : length Ls = length alphas.
  Variable global_error_sq : R.
  Hypothesis Hglobal_nonnegative : 0 <= global_error_sq.
  Hypothesis Hanalytic_components :
    global_error_sq <= kappa * local_component_sum Cinf Ls l2s derivs.
  Hypothesis Hlocal_evidence :
    Forall (fun t => synth_valid Rules (snd t)) (synthesis_evidence_terms xs).

  Definition weighted_synthesis_output : ExactSynthesisOutput Rules :=
    compile_exact_synthesis Rules xs.

  Theorem weighted_synthesis_code_is_exact :
    synthesized_code Rules weighted_synthesis_output
      = synthesize_raw (synthesis_code_terms xs).
  Proof. reflexivity. Qed.

  Theorem weighted_synthesis_evidence_is_valid :
    synth_valid Rules (synthesized_evidence Rules weighted_synthesis_output).
  Proof.
    unfold weighted_synthesis_output. simpl.
    now apply compiled_synthesis_evidence_is_valid.
  Qed.

  Theorem proposition_6_3_global_bound :
    global_error_sq <= kappa * manuscript_weighted_sum Cinf Ls alphas.
  Proof.
    eapply proposition_6_3_weighted_global_bound; eauto.
  Qed.

  Theorem proposition_6_3_epsilon_certificate :
    kappa * manuscript_weighted_sum Cinf Ls alphas < epsilon^2 ->
    global_error_sq < epsilon^2
    /\ synthesized_code Rules weighted_synthesis_output
         = synthesize_raw (synthesis_code_terms xs)
    /\ synth_valid Rules (synthesized_evidence Rules weighted_synthesis_output).
  Proof.
    intro Hallocation. repeat split.
    - pose proof proposition_6_3_global_bound. lra.
    - apply weighted_synthesis_code_is_exact.
    - apply weighted_synthesis_evidence_is_valid.
  Qed.
End Package.

End UELAT_V3_WeightedSynthesisBudget.
