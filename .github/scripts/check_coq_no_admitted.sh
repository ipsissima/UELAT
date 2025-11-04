#!/usr/bin/env bash
set -euo pipefail
echo "Scanning Coq sources for Axiom or Admitted..."
if [ ! -d Coq ]; then
  echo "No Coq directory found to scan."
  exit 0
fi
hits=$(grep -RIn --color=never -E '\<(Axiom|Admitted)\>' Coq || true)
if [ -n "$hits" ]; then
  echo "ERROR: Found uses of Axiom or Admitted in Coq sources. CI will fail so these can be inspected."
  echo "$hits"
  echo
  echo "If this is expected, whitelist files in .github/scripts/check_coq_no_admitted.sh or justify in the PR."
  exit 1
fi
echo "No Axiom/Admitted found."
