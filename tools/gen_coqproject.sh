#!/usr/bin/env bash
set -euo pipefail

# Generates Coq/_CoqProject by enumerating .v files if it doesn't exist.
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

# Heuristic logical path: map Coq/ to logical root UELAT
# Adjust if you have a different namespace layout.
echo "-Q . UELAT" > "$OUT"

# Enumerate .v files relative to Coq/
# _CoqProject expects relative paths from its own directory
(
  cd "$ROOT"
  # List all .v files, sorted, relative to Coq/
  git ls-files '*.v' 2>/dev/null || true
  find . -type f -name '*.v' 2>/dev/null
) | sed 's|^\./||' | sort -u >> "$OUT"

echo "Wrote $OUT"
