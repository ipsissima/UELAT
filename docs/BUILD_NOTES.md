# Phase 1 Build Notes: Coq 8.19 → Rocq 9 migration

Purpose: record every toolchain / build-config change made during the
Phase 1 migration, so any behavioral surprise can be traced back to a
specific edit rather than a silent drift.

## Baseline (before migration)

- `Coq/` source uses Rocq 9 conventions: `From Stdlib Require …`,
  post-8.20 stdlib names (`length_app`, etc.). `Coq/Makefile` header
  is literally *"GNUMakefile for Rocq 9.0.1"*.
- `uelat.opam` pinned `coq {>= "8.18" & < "8.20"}`, i.e. Coq 8.18 / 8.19.
- CI on `main` has been red since 2025-12-31 (run 20609761616) for
  exactly this mismatch.
- **New failure mode observed on 2026-08-12** (PR #32, head e4baa0b,
  runs 31603623287 / 31603690679): under the old pin the opam solver
  picks `coq-mathcomp-*` versions whose transitive deps include
  `rocq-hierarchy-builder.1.9.1` and `coq-elpi.2.2.3`, both of which
  invoke the `rocq` binary that only exists in Rocq 9:
  ```
  /bin/sh: 1: rocq: not found
  rocq makefile -f _CoqProject -o Makefile.coq
  make: rocq: No such file or directory
  ```
  → The pre-migration `uelat.opam` is now literally unresolvable
  against the current `coq-released` opam repo, independent of any
  source-style question.

## Baseline inventory (locked, must not regress)

Recorded in `docs/INVENTORY.md` (commit e4baa0b). Totals across the
36 `.v` files:

| item          | count |
| ---           | ---   |
| Theorem       | 67    |
| Lemma         | 327   |
| Corollary     | 11    |
| Definition    | 241   |
| Example       | 1     |
| Qed           | 378   |
| Defined       | 29    |
| **Admitted**  | **3** |
| `admit.`      | 0     |
| **Axiom**     | **6** |
| **Parameter** | **15**|
| Hypothesis    | 75    |

The 3 Admitted are exactly:
`Coq/Util/Entropy.v:486`, `Coq/Util/Entropy.v:680`, `Coq/Adjunction/Probe.v:122`
— matching `docs/AXIOMS_AND_ADMISSIONS.md`.

## Changes in this phase

### 1. `uelat.opam`
- Replaced `"coq" {>= "8.18" & < "8.20"}` with
  `"rocq-prover" {>= "9.0.0"}`. Forces the opam solver to pick a
  Rocq-9 toolchain, which is what the source already speaks.
- Dropped `"coq-coquelicot"`. **Rationale:** grep of `Coq/` confirms
  no source file imports Coquelicot — the string only appears inside
  comments in `Coq/Examples/ChebyshevProof.v`. Removing the unused
  dep both shortens the build and removes a place where a
  Coquelicot-vs-Rocq-9 version conflict could hold up the switch.
  No proof depends on it.
- Kept `coq-mathcomp-{ssreflect,algebra,analysis}` under their
  legacy `coq-` prefix — those packages are still published on the
  Rocq-9 opam channel under that name (as `coq-elpi.2.2.3` and
  `rocq-hierarchy-builder.1.9.1` co-installing in the failure log
  demonstrates). Let the solver pick versions.

### 2. CI workflow (`.github/workflows/ci.yml`)
- No changes. `coq_makefile` and `coqchk` are still the correct
  binary names under Rocq 9, and the switch/install/build steps
  are already generic (`opam install . --deps-only`, then
  `coq_makefile … && make`). The switch's install step will now
  resolve `rocq-prover.9.x.y` because that's what `uelat.opam`
  asks for.

## Not changed in this phase

- **No `.v` file was edited.** The whole point of the migration is
  to move the toolchain forward to match the sources, not the other
  way around. Any source-level Rocq-9 incompatibility that CI
  surfaces will be recorded in a new section below with file, line,
  cause, and fix.
- **No theorem statement, `Axiom`, `Parameter`, `Admitted`, or
  `admit.` was added, deleted, or altered.**

## Iteration log

- **Round 1** (this commit): switch opam pin only. Expected
  outcome: opam resolves Rocq 9, mathcomp stack builds against it,
  `coq_makefile … && make` builds all 36 files without source
  edits. If any file breaks, its error goes in a new "Round 2"
  subsection with file/line/cause/fix.
