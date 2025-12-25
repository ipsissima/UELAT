#!/usr/bin/env bash
set -euo pipefail

LOG_DIR=".github/logs"
mkdir -p "$LOG_DIR"
OUT="$LOG_DIR/coq_admitted_hits.txt"
: > "$OUT"

echo "Scanning Coq sources for Axiom or Admitted..."
if [ ! -d "Coq" ]; then
  echo "No Coq directory found to scan."
  exit 0
fi

# Use word boundaries to avoid false positives.
grep -RIn --color=never -E '\<(Axiom|Admitted)\>' Coq || true > /dev/null

# Save hits (with filenames and line numbers) into the output file
grep -RIn --color=never -E '\<(Axiom|Admitted)\>' Coq > "$OUT" || true

if [ -s "$OUT" ]; then
  echo "ERROR: Found uses of Axiom or Admitted in Coq sources. CI will fail so these can be inspected."
  echo
  echo "Matches written to $OUT"
  echo
  # Print a short preview for logs
  head -n 200 "$OUT" || true
  echo
  echo "If this is expected, whitelist files in .github/scripts/check_coq_no_admitted.sh or justify in the PR."
  exit 1
fi

echo "No Axiom/Admitted found."
exit 0
