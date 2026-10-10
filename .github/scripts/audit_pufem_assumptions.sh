#!/usr/bin/env bash
# Fail-closed Rocq 9.2 Print Assumptions audit for candidate 5.6/7.2.
# Allow *only* known Stdlib dependencies already in docs/assumptions/.
# Raw reports are always preserved as build artifacts for review.
set -euo pipefail
ROOT="$(git rev-parse --show-toplevel)"
OUT="${ROOT}/docs/pufem_assumptions"
mkdir -p "$OUT"
find "$OUT" -maxdepth 1 -type f -name '*.txt' -delete
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
MODULES=(
  PUFEMPointwiseCore
  PUFEMIntegralBridge
  PUFEMScaleBridge
  PUFEMLimitBridge
  RationalPolynomialSemantic
  RationalHatProductSemantic
  RationalRealPolynomialSemantics
  ConcretePolynomialSobolev
  ConcretePiecewiseSobolev
  ConcretePolynomialFTC
  ConcretePolynomialWeakTest
  ConcretePiecewiseWeakTest
  ConcreteUnitIntervalSobolev
)
for module in "${MODULES[@]}"; do
  source="${ROOT}/Coq/V3/${module}.v"
  if [ ! -f "$source" ]; then echo "::error::Missing $source" >&2; exit 1; fi
  if grep -nE '^[[:space:]]*(Admitted[[:space:]]*\.|Axiom[[:space:]]|Parameter[[:space:]])' "$source"; then
    echo "::error::Unproved declaration in $source" >&2
    exit 1
  fi
done
AUDIT=(
  'PUFEMPointwiseCore|finite_cauchy_overlap'
  'PUFEMPointwiseCore|bounded_overlap_squared'
  'PUFEMPointwiseCore|localized_integrand_56'
  'PUFEMPointwiseCore|finite_quadrature_localized_56'
  'PUFEMIntegralBridge|integrated_localized_56'
  'PUFEMIntegralBridge|finite_positive_integrated_56'
  'PUFEMScaleBridge|weighted_energy_bound'
  'PUFEMScaleBridge|scale_sensitive_squared_72'
  'PUFEMScaleBridge|norm_scale_sensitive_72'
  'PUFEMScaleBridge|one_power_loss_squared'
  'PUFEMScaleBridge|inverse_squared_exactly_consumes_two_powers'
  'PUFEMLimitBridge|sequence_order_limit'
  'PUFEMLimitBridge|integrated_localized_56_from_quadrature_limits'
  'PUFEMLimitBridge|scale_sensitive_72_from_quadrature_limits'
  'RationalPolynomialSemantic|qpoly_eval_mul_sound'
  'RationalPolynomialSemantic|qpoly_deriv_mul_eval'
  'RationalPolynomialSemantic|affine_hat_product_derivative'
  'RationalPolynomialSemantic|qpoly_integral_add_sound'
  'RationalPolynomialSemantic|qpoly_integral_scale_sound'
  'RationalHatProductSemantic|concrete_hat_partition_identity'
  'RationalHatProductSemantic|concrete_left_hat_product_derivative'
  'RationalHatProductSemantic|concrete_right_hat_product_derivative'
  'RationalHatProductSemantic|concrete_left_hat_product_value'
  'RationalHatProductSemantic|concrete_right_hat_product_value'
  'RationalRealPolynomialSemantics|rpoly_rational_stage_agrees'
  'RationalRealPolynomialSemantics|rpoly_eval_add_sound'
  'RationalRealPolynomialSemantics|rpoly_eval_scale_sound'
  'RationalRealPolynomialSemantics|rpoly_eval_mul_sound'
  'ConcretePolynomialSobolev|polynomial_has_concrete_real_derivative'
  'ConcretePolynomialSobolev|polynomial_is_continuous'
  'ConcretePolynomialSobolev|polynomial_energy_is_actual_squared_norm_integrand'
  'ConcretePolynomialSobolev|concrete_polynomial_w12_energy_nonnegative'
  'ConcretePiecewiseSobolev|real_cell_w12_energy_nonnegative'
  'ConcretePiecewiseSobolev|every_well_formed_code_has_finite_nonnegative_real_energy'
  'ConcretePiecewiseSobolev|adjacent_piece_endpoints_match_over_reals'
  'ConcretePiecewiseSobolev|adjacent_piece_values_match_over_reals'
  'ConcretePolynomialFTC|rational_polynomial_C1_derivative'
  'ConcretePolynomialFTC|real_polynomial_coded_FTC'
  'ConcretePolynomialWeakTest|real_polynomial_product_has_correct_derivative'
  'ConcretePolynomialWeakTest|real_polynomial_product_FTC'
  'ConcretePolynomialWeakTest|rational_polynomial_interval_integration_by_parts'
  'ConcretePolynomialWeakTest|rational_polynomial_weak_derivative_test'
  'ConcretePiecewiseWeakTest|piecewise_Riemann_integration_by_parts'
  'ConcretePiecewiseWeakTest|adjacent_product_value_match'
  'ConcretePiecewiseWeakTest|piecewise_seams_telescope'
  'ConcretePiecewiseWeakTest|piecewise_polynomial_weak_test_endpoint_zero'
  'ConcreteUnitIntervalSobolev|unit_code_real_start'
  'ConcreteUnitIntervalSobolev|unit_code_real_end'
  'ConcreteUnitIntervalSobolev|unit_piecewise_real_energy_nonnegative'
  'ConcreteUnitIntervalSobolev|unit_code_polynomial_test_weak_derivative'
)
count=0
for entry in "${AUDIT[@]}"; do
  module="${entry%%|*}"
  theorem="${entry#*|}"
  probe="${TMP}/check_${module}_${theorem}.v"
  raw="${OUT}/${module}__${theorem}.txt"
  printf 'From UELAT.V3 Require Import %s.\nPrint Assumptions UELAT_V3_%s.%s.\n' "$module" "$module" "$theorem" > "$probe"
  if ! (cd "$ROOT" && coqc -R Coq UELAT "$probe") > "$raw" 2>&1; then
    echo "::error::Cannot inspect ${module}.${theorem}" >&2; cat "$raw" >&2; exit 1
  fi
  if grep -q '^Axioms:' "$raw"; then
    names="$(sed -n '/^Axioms:/,$p' "$raw" | grep -E '^[A-Za-z_][A-Za-z_0-9.]*[[:space:]]*:' | sed -E 's/[[:space:]]*:.*$//' || true)"
    if [ -z "$names" ]; then echo "::error::Unparseable axiom list: ${module}.${theorem}" >&2; cat "$raw" >&2; exit 1; fi
    while IFS= read -r name; do
      case "$name" in
        ClassicalDedekindReals.sig_forall_dec|FunctionalExtensionality.functional_extensionality_dep) ;;
        *) echo "::error::Unexpected axiom $name in ${module}.${theorem}" >&2; cat "$raw" >&2; exit 1 ;;
      esac
    done <<< "$names"
  elif ! grep -q '^Closed under the global context' "$raw"; then
    echo "::error::No Print Assumptions verdict for ${module}.${theorem}" >&2; cat "$raw" >&2; exit 1
  fi
  count=$((count + 1))
  echo "Audited: ${module}.${theorem}"
done
echo "Completed ${count} theorem assumption reports in ${OUT}"
