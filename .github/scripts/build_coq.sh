#!/usr/bin/env bash
set -euo pipefail
LOG="coq-build.log"
rm -f "$LOG"
echo "Starting Coq build; output going to $LOG"
if [ -f Coq/Makefile ]; then
  make -C Coq 2>&1 | tee "$LOG"
else
  if [ -f Coq/_CoqProject ]; then
    pushd Coq > /dev/null
    coq_makefile -f _CoqProject -o Makefile
    make 2>&1 | tee "../$LOG"
    popd > /dev/null
  else
    find Coq -name '*.v' -print0 | xargs -0 -n1 -I{} bash -lc 'echo "Compiling {}"; coqc "{}"' 2>&1 | tee "$LOG"
  fi
fi
