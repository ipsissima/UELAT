# docs/assumptions/

This directory holds the `Print Assumptions` output for every Rocq
theorem that `docs/FORMALIZATION_STATUS.md` advertises as
`CHECKED-EXACT`. One `<stem>.txt` file per theorem.

Files here are **generator output** produced by
`.github/scripts/print_assumptions.sh`. Do NOT edit them by hand. Add
a theorem to the generator's `AUDIT_LIST` when it reaches
`CHECKED-EXACT` in `FORMALIZATION_STATUS.md`, run the script, and
commit the resulting files.

CI runs the generator and diffs the freshly generated output against
what is committed — a mismatch fails the build. This is the
"assumptions have been captured and reviewed" requirement of the
status vocabulary made mechanical: the assumption footprint of every
advertised checked theorem is visible in the tree and moves in
lockstep with the source.

The directory is currently empty because nothing has yet reached
`CHECKED-EXACT`. When the first theorem lands, it gets both a status
row and an `.txt` file here.
