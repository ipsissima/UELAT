# AXIOMS_AND_ADMISSIONS.md — dependency and status report

This document lists every `Admitted`, `Axiom`, `Parameter`, and
significant `Hypothesis` currently in the repository. It is a
**descriptive dependency report**, not an endorsement. Earlier
versions of this file described the formalization as "scientifically
complete" and "publication-quality"; those phrases were removed in the
v3 documentation reset because they were not supported by an actual
theorem-correspondence audit against the v3 manuscript.

For the machine-checkedness status of each v3 paper theorem, consult
`docs/FORMALIZATION_STATUS.md`. For the audit conclusions on legacy
modules, consult `docs/LEGACY_AUDIT.md`. This file only records the
raw dependencies.

## Counts (as of the current commit)

| kind | count | notes |
| --- | --- | --- |
| `Admitted` | 3 | see §Admitted below |
| `Axiom` | 6 | see §Axiom below |
| `Parameter` | 15 | mostly section variables for hypothesis-parametric development |
| `Hypothesis` | 75 | inside `Section`s, discharged when sections close |

`Parameter` and `Hypothesis` become meaningful for downstream users
only when they leak into a `Print Assumptions` output for an
advertised theorem. Currently no v3 theorem is `CHECKED-EXACT`
(`docs/FORMALIZATION_STATUS.md`), so no such report exists yet. When
one lands, its `Print Assumptions` will be committed under
`docs/assumptions/<theorem>.txt`.

## Policy

New `Admitted`, `Axiom`, or `Parameter` MUST NOT be introduced solely
to make a build green or a theorem appear checked. Additions require:

1. an entry in this file with the exact file:line;
2. a paragraph in the commit message stating what the assumption is
   and why it cannot yet be proved;
3. a row update in `docs/FORMALIZATION_STATUS.md` reflecting the
   dependency (typically downgrading affected theorems from
   `CHECKED-EXACT` to `CHECKED-RESTRICTED`).

Silently changing a theorem statement to avoid these obligations is
the specific failure mode this document exists to prevent.

## Admitted statements

### 1. `probe_coprod_univ` — `Coq/Adjunction/Probe.v:122`

- **Kind**: universal property of coproducts in the Probe category.
- **Uses**: none in `Coq/V3/`; local to the legacy Probe/Model
  infrastructure. See `docs/LEGACY_AUDIT.md` §Probe.v/Model.v.
- **v3 relevance**: none. v3 does not use the probes–models
  categorical setup (Remark 5.5 of the paper withdraws that story).
- **Removal path**: LEGACY-V2 marker; may remain admitted indefinitely
  or be relocated with the rest of the legacy adjunction material.

### 2. `entropy_to_discrete_pigeonhole` — `Coq/Util/Entropy.v:486`

- **Kind**: pigeonhole/counting lemma for a bespoke `Entropy.v`
  presentation.
- **Uses**: legacy incompressibility exposition. `Util/Entropy.v` is
  excluded from CI (transitively depends on `Incompressibility.v`).
- **v3 relevance**: none. v3 Thm 12.1 (non-certifiability) is a
  different theorem with a different proof; it does not use this
  lemma. See `docs/LEGACY_AUDIT.md`.

### 3. `packing_le_covering` — `Coq/Util/Entropy.v:680`

- **Kind**: standard `N_pack(2ε) ≤ N_cover(ε)` metric-geometry step.
- **Uses**: only the legacy `Util/Entropy.v` exposition.
- **v3 relevance**: none.

## Axiom declarations

The six `Axiom` declarations live in the legacy `Adjunction/Functors.v`
and `Foundations/Certificate.v` chain (`find_index`-style helpers and
list-decoding stubs). None are on a dependency path of anything in
`Coq/V3/`, and none should ever be reachable from a v3 `CHECKED-EXACT`
theorem. If a future v3 module needs the corresponding functionality,
it should reprove it as a real Rocq lemma, not import through the
legacy axiom.

Exact enumerations are best obtained by searching the tree:

```bash
grep -rn --include='*.v' -E '^\s*Axiom\b' Coq/
```

The full list will be captured programmatically once CI has a
"dependency of advertised checked theorems" scan; today it is not, so
this document does not enumerate them by name — the enumeration is
grep-reproducible and any change is visible in the commit diff.

## Section-level `Hypothesis` count

75 `Hypothesis` declarations exist across `Coq/`, almost all inside
`Section` blocks that close cleanly (so the hypothesis is discharged
into the resulting lambda). These are not axioms in the
`Print Assumptions` sense. They will appear in a checked-theorem's
type signature and are meaningful there.

## Historical wording removed

For record: earlier versions of this file said

> "The UELAT formalization is scientifically complete. All main
> theorems are proven, and all axioms/admissions are either …
> The formalization represents a rigorous, publication-quality
> verification of the UELAT theory."

Those sentences do not accurately describe the current repository
against the v3 manuscript, and are not compatible with the paper's own
Section 18 ("Formalization status") position. They were removed in
the same commit that added `docs/FORMALIZATION_STATUS.md`. They are
mentioned here so that anyone finding them quoted elsewhere can see
that they are not this repository's current claim.
