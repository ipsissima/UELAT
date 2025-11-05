#!/usr/bin/env bash
set -euo pipefail

# Generates Coq/_CoqProject with the project namespace if it doesn't exist.
# Safe to run repeatedly.

ROOT="Coq"
OUT="$ROOT/_CoqProject"

if [ ! -d "$ROOT" ]; then
  echo "No Coq/ directory; nothing to do."
  exit 0
fi

mkdir -p "$ROOT"

if [ -f "$OUT" ]; then
  echo "_CoqProject already exists; leaving as-is."
  exit 0
fi

# Map the Coq/ directory to the logical namespace UELAT. The file list is
# provided explicitly when invoking coq_makefile, so we do not enumerate it
# here.
cat <<'EON' > "$OUT"
-Q Coq UELAT
EON

echo "Wrote $OUT"
