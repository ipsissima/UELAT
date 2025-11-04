#!/usr/bin/env bash
set -euo pipefail

LOG_DIR=".github/logs"
mkdir -p "$LOG_DIR"
LOG="$LOG_DIR/coq-build.log"
rm -f "$LOG"
echo "Starting Coq build; output going to $LOG"

if [ -f "Coq/Makefile" ]; then
  echo "Using Coq/Makefile"
  (cd Coq && make) 2>&1 | tee "$LOG"
  EXIT_CODE=${PIPESTATUS[0]}
  if [ "$EXIT_CODE" -ne 0 ]; then
    echo "Coq build failed (Makefile). See $LOG"
    exit "$EXIT_CODE"
  fi
else
  if [ -f "Coq/_CoqProject" ]; then
    echo "_CoqProject found—generating Makefile and building"
    pushd Coq > /dev/null
    coq_makefile -f _CoqProject -o Makefile
    make 2>&1 | tee "../$LOG"
    EXIT_CODE=${PIPESTATUS[0]}
    popd > /dev/null
    if [ "$EXIT_CODE" -ne 0 ]; then
      echo "Coq build failed (coq_makefile). See $LOG"
      exit "$EXIT_CODE"
    fi
  else
    echo "No Makefile or _CoqProject: compiling .v files directly"
    set +e
    find Coq -name '*.v' -print0 | xargs -0 -n1 -I{} bash -lc 'echo "Compiling {}"; coqc "{}"' 2>&1 | tee "$LOG"
    EXIT_CODE=${PIPESTATUS[0]}
    set -e
    if [ "$EXIT_CODE" -ne 0 ]; then
      echo "Coq build failed when compiling .v files. See $LOG"
      exit "$EXIT_CODE"
    fi
  fi
fi

echo "Coq build succeeded."
exit 0
