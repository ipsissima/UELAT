#!/usr/bin/env bash
# print_assumptions.sh — capture `Print Assumptions` for each theorem
# named in the AUDIT_LIST below, writing one file per theorem under
# docs/assumptions/.
#
# The AUDIT_LIST is the source of truth. Each entry has the form
#
#   <output_stem>|<From … Require Import path>|<qualified theorem name>
#
# When a v3 module reaches CHECKED-EXACT and a Rocq theorem name is
# added to docs/FORMALIZATION_STATUS.md, add the corresponding entry
# here. CI diffs the generated files against what is committed under
# docs/assumptions/; a mismatch fails the job.

set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
OUT_DIR="${REPO_ROOT}/docs/assumptions"
mkdir -p "${OUT_DIR}"

# --------------------------------------------------------------------
# Audit list — one entry per Rocq theorem the correspondence table in
# docs/FORMALIZATION_STATUS.md advertises as CHECKED-EXACT or
# CHECKED-RESTRICTED. The section-5 entries below are deliberately
# added before promotion: CI must establish their assumption footprint
# before the status table is allowed to call them checked.
# --------------------------------------------------------------------
AUDIT_LIST=(
  "comp_evidence_id_l|From UELAT.V3 Require Import Presentation Evidence|V3_Evidence.comp_evidence_id_l"
  "comp_evidence_id_r|From UELAT.V3 Require Import Presentation Evidence|V3_Evidence.comp_evidence_id_r"
  "comp_evidence_assoc|From UELAT.V3 Require Import Presentation Evidence|V3_Evidence.comp_evidence_assoc"
  "prop_3_3_lower_bound|From UELAT.V3 Require Import Presentation Evidence MetricReflection|V3_MetricReflection.prop_3_3_lower_bound"
  "lawvere_bounds_analytic|From UELAT.V3 Require Import Presentation Evidence MetricReflection|V3_MetricReflection.lawvere_bounds_analytic"
  "extensional_collapse|From UELAT.V3 Require Import Presentation Evidence MetricReflection|V3_MetricReflection.extensional_collapse"
  "principal_evidence_dense|From UELAT.V3 Require Import Presentation Evidence MetricReflection EffectiveCompleteness|V3_EffectiveCompleteness.principal_evidence_dense"
  "principal_evidence_dense_analytic|From UELAT.V3 Require Import Presentation Evidence MetricReflection EffectiveCompleteness|V3_EffectiveCompleteness.principal_evidence_dense_analytic"
  "rm_app_transport_ok|From UELAT.V3 Require Import Presentation Evidence RealizableMap|V3_RealizableMap.rm_app_transport_ok"
  "lift_underlying|From UELAT.V3 Require Import GenericLift|V3_GenericLift.lift_underlying"
  "lift_morphism_id|From UELAT.V3 Require Import GenericLift|V3_GenericLift.lift_morphism_id"
  "lift_morphism_comp|From UELAT.V3 Require Import GenericLift|V3_GenericLift.lift_morphism_comp"
  "lift_lawvere_lipschitz|From UELAT.V3 Require Import GenericLift|V3_GenericLift.lift_lawvere_lipschitz"
  "compose_realizable_lambda|From UELAT.V3 Require Import Composition|V3_Composition.compose_realizable_lambda"
  "compose_realizable_map|From UELAT.V3 Require Import Composition|V3_Composition.compose_realizable_map"
  "composed_lift_underlying|From UELAT.V3 Require Import Composition|V3_Composition.composed_lift_underlying"
  "composed_lift_id|From UELAT.V3 Require Import Composition|V3_Composition.composed_lift_id"
  "composed_lift_comp|From UELAT.V3 Require Import Composition|V3_Composition.composed_lift_comp"
  "proposition73_level_package|From UELAT.V3 Require Import Proposition73CompilerBound|UELAT_V3_Proposition73CompilerBound.proposition73_level_package"
  "proposition73_geometric_patch_sum|From UELAT.V3 Require Import Proposition73CompilerBound|UELAT_V3_Proposition73CompilerBound.proposition73_geometric_patch_sum"
  "proposition73_accumulated_node_count|From UELAT.V3 Require Import Proposition73CompilerBound|UELAT_V3_Proposition73CompilerBound.proposition73_accumulated_node_count"
  "theorem74_manuscript_core|From UELAT.V3 Require Import Theorem74Manuscript|UELAT_V3_Theorem74Manuscript.theorem74_manuscript_core"
  "theorem74_level_exponent_control|From UELAT.V3 Require Import Theorem74Manuscript|UELAT_V3_Theorem74Manuscript.theorem74_level_exponent_control"
  "theorem74_level_dyadic_depth_bound|From UELAT.V3 Require Import Theorem74Manuscript|UELAT_V3_Theorem74Manuscript.theorem74_level_dyadic_depth_bound"
  "theorem74_level_canonical_paper_k_bound|From UELAT.V3 Require Import Theorem74Manuscript|UELAT_V3_Theorem74Manuscript.theorem74_level_canonical_paper_k_bound"
  "theorem74_linear_bit_schedule|From UELAT.V3 Require Import Theorem74Manuscript|UELAT_V3_Theorem74Manuscript.theorem74_linear_bit_schedule"
  "corollary75_standard_rational_package|From UELAT.V3 Require Import Theorem74Manuscript|UELAT_V3_Theorem74Manuscript.corollary75_standard_rational_package"
  "corollary75_canonical_paper_k_package|From UELAT.V3 Require Import Theorem74Manuscript|UELAT_V3_Theorem74Manuscript.corollary75_canonical_paper_k_package"
  "theorem74_manuscript_source_lookahead|From UELAT.V3 Require Import Theorem74Manuscript|UELAT_V3_Theorem74Manuscript.theorem74_manuscript_source_lookahead"
  "theorem74_manuscript_preserves_ancestry|From UELAT.V3 Require Import Theorem74Manuscript|UELAT_V3_Theorem74Manuscript.theorem74_manuscript_preserves_ancestry"
)

# The old CI island (_CoqProject) compiles only the first 18 v3
# theorems. Its audit must not try to import authoritative-only modules;
# the authoritative-v3 workflow independently builds and audits all 30.
case "${1:-}" in
  --core-only)
    if [ "${#AUDIT_LIST[@]}" -lt 18 ] ||
       [[ "${AUDIT_LIST[17]}" != composed_lift_comp\|* ]]; then
      echo "::error::Unexpected audit-list layout; refusing core subset" >&2
      exit 1
    fi
    AUDIT_LIST=("${AUDIT_LIST[@]:0:18}")
    ;;
  "") ;; # authoritative full surface is the default
  *) echo "::error::Unknown audit mode: $1" >&2; exit 1 ;;
esac

if [ "${#AUDIT_LIST[@]}" -eq 0 ]; then
  echo "print_assumptions: audit list empty — nothing to check yet."
  exit 0
fi

TMPDIR="$(mktemp -d)"
trap 'rm -rf "${TMPDIR}"' EXIT

for entry in "${AUDIT_LIST[@]}"; do
  stem="${entry%%|*}"
  rest="${entry#*|}"
  reqline="${rest%%|*}"
  thmname="${rest#*|}"

  probe="${TMPDIR}/probe_${stem}.v"
  cat > "${probe}" <<EOF
${reqline}.
Print Assumptions ${thmname}.
EOF

  raw="${TMPDIR}/${stem}.raw"
  if ! ( cd "${REPO_ROOT}/Coq" && coqc -R . UELAT "${probe}" ) > "${raw}" 2>&1; then
    echo "::error::print_assumptions: coqc failed for ${thmname}" >&2
    echo "--- probe file ---" >&2
    cat "${probe}" >&2
    echo "--- coqc output ---" >&2
    cat "${raw}" >&2
    exit 1
  fi

  if grep -q '^Closed under the global context' "${raw}"; then
    verdict="$(grep '^Closed under the global context' "${raw}")"
  else
    verdict="$(sed -n '/^Axioms:/,$p' "${raw}")"
  fi

  if [ -z "${verdict}" ]; then
    echo "::error::print_assumptions: no verdict block found for ${thmname}" >&2
    echo "--- coqc output ---" >&2
    cat "${raw}" >&2
    exit 1
  fi

  out="${OUT_DIR}/${stem}.txt"
  {
    echo "# Print Assumptions ${thmname}"
    echo "# generated by .github/scripts/print_assumptions.sh -- do not edit by hand"
    echo "#"
    echo "# Only the Print Assumptions verdict is retained; coqc warnings are"
    echo "# dropped because they quote a per-run temporary path."
    echo ""
    echo "${verdict}"
  } > "${out}"

  echo "===== BEGIN ${stem}.txt ====="
  cat "${out}"
  echo "===== END ${stem}.txt ====="
done
