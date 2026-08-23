#!/usr/bin/env bash
# local_v3_check.sh — fast local type-check of the Coq/V3/ chain.
#
# WHY THIS EXISTS. The CI Coq job spends ~35 minutes building an opam
# switch before it compiles anything, so a single wrong lemma name costs
# most of an hour. The V3 modules depend only on the Coq standard
# library (no mathcomp), so they can be checked against a distro Coq in
# seconds:
#
#   apt-get install -y --no-install-recommends coq
#   bash .github/scripts/local_v3_check.sh
#
# WHAT IT DOES NOT PROVE. The distro Coq is 8.18, not Rocq 9. The only
# source change made is the import prefix (`From Stdlib` -> `From Coq`),
# which is exactly the 8.x/9.x stdlib rename. So a green run here is
# strong evidence about proof scripts, lemma names, scopes, implicit
# arguments and dependent matches -- but it is NOT a substitute for CI.
# Only the CI job builds against the pinned Rocq 9 toolchain and runs
# coqchk. Never promote a status label on the strength of this script.
set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel)"
WORK="$(mktemp -d)"
trap 'rm -rf "${WORK}"' EXIT
mkdir -p "${WORK}/V3"

for f in "${REPO_ROOT}"/Coq/V3/*.v; do
  sed 's/^From Stdlib Require/From Coq Require/' "$f" > "${WORK}/V3/$(basename "$f")"
done

# Dependency order.
MODULES=(EvidenceSyntax Presentation Evidence MetricReflection
         EffectiveCompleteness RealizableMap)

cd "${WORK}"
rc=0
for m in "${MODULES[@]}"; do
  if coqc -q -Q . UELAT "V3/${m}.v" > "${WORK}/${m}.out" 2>&1; then
    echo "OK   ${m}"
  else
    echo "FAIL ${m}"
    grep -vE '^(Warning|.*deprecated|[[:space:]]*$)' "${WORK}/${m}.out" | head -30
    rc=1
    break
  fi
done

if [ "${rc}" -eq 0 ]; then
  echo "=== all V3 modules type-check under $(coqc --version | head -1) ==="
fi
exit "${rc}"
