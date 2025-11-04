#!/usr/bin/env bash
set -eu -o pipefail
# Fail if forbidden patterns are found in Coq sources.
# Adjust the directory globs if your .v files live elsewhere.
if grep -RIn --include='*.v' -E '\bAdmitted\.' Coq; then
  echo "Error: Found Admitted. in Coq sources."; exit 1
fi
# Allowlisted axioms can be whitelisted by editing the regex below.
if grep -RIn --include='*.v' -E '^\s*Axiom\s+' Coq; then
  echo "Error: Found bare Axiom declarations in Coq sources."; exit 1
fi
echo "No forbidden Admitted/Axiom found."
