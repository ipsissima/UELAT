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

The six `Axiom` declarations at the current commit are, by file:

| file | line | name | notes |
| --- | --- | --- | --- |
| `Coq/Adjunction/Functors.v` | 158 | `find_index_preserves_order` | Legacy list-indexing helper used by the v1–v2 probes/models adjunction. Not reachable from any `Coq/V3/` module. |
| `Coq/Adjunction/Functors.v` | 169 | `find_index_nth_self` | Same. |
| `Coq/Example.v` | 77 | `error_bound_example` | Legacy demo file. `LegacyV2`. |
| `Coq/Examples/ChebyshevProof.v` | 67 | `rolle` | Rolle's theorem — legacy analytic axiom used by the withdrawn Chebyshev example. `LegacyV2`. |
| `Coq/Examples/ChebyshevProof.v` | 2108 | `chebyshev_nodal_identity_axiom` | Same. |
| `Coq/ErrorBound.v` | 714 | `parseval_identity_integration` | Parseval identity — legacy analytic axiom used by the withdrawn Fourier/Chebyshev material. `LegacyV2`. |

`Coq/Foundations/Certificate.v` declares **zero** axioms; an earlier
version of this document wrongly grouped it into the axiom-holding
files.

None of these axioms is on a dependency path of anything in
`Coq/V3/`, and none should ever be reachable from a v3
`CHECKED-EXACT` theorem. When a future v3 module needs the
corresponding mathematical fact, it should reprove it as a real Rocq
lemma, not import through the legacy axiom.

Regenerate the enumeration at any commit with:

```bash
grep -rn --include='*.v' -E '^\s*Axiom\b' Coq/
```

The table above must be updated in the same commit as any change in
that grep output; a future CI check will diff the two.

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
