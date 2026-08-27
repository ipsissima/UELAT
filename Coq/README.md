# Rocq/Coq layout

The `Coq/` tree contains current-paper formalization, reusable checked infrastructure, and preserved historical material. These roles are intentionally separated.

## Authoritative v3 surface

For the current manuscript, start with exactly two files:

- [`_CoqProject.authoritative-v3`](./_CoqProject.authoritative-v3) — the declared build surface.
- [`UELATAuthoritativeV3.v`](./UELATAuthoritativeV3.v) — the public aggregate checked by `coqchk` after a successful build.

A module's mere presence under `V3/` does not make it authoritative. The build surface plus [`../docs/FORMALIZATION STATUS.md`](../docs/FORMALIZATION%20STATUS.md) control verification claims.

## `V3/` organization by manuscript section

The directory remains intentionally flat for stable Rocq import paths, but the conceptual grouping is:

- **§2 — represented objects and evidence:** presentation, certificate enrichment, strict-slack search/collapse, evidence category.
- **§3 — effective linear universality:** computable Banach structure, approximate Hahn–Banach interfaces, norming families, coordinate dual ball, effective compactness, range inversion, `C([0,1])` representation.
- **§4 — proof-relevant transport:** realizable maps, chosen lifts, reindexing, Grothendieck organization, resource profile.
- **§§5–6 — exact rational reconstruction:** rational Sobolev codes, mesh refinement, interval covers, hats/POU, synthesis, PUFEM compiler, proof DAG, encoding/bit budgets.
- **§7 — refinement and descent:** quasi-uniform geometry, precision schedules, H1–H7 assembly, certificate-size bounds, standard rational regime, manuscript wrapper for Theorem 7.4.
- **§§8–9 — generated semantics and boundaries:** Contextual Choice, finite-measure boundary, information obstruction, extensional sheaf placement.

See [`../docs/REVIEWER_GUIDE.md`](../docs/REVIEWER_GUIDE.md) for a reviewer-oriented audit path.

## Build

With Rocq 9.2 installed:

```sh
coq_makefile -f _CoqProject.authoritative-v3 -o Makefile.authoritative-v3
make -f Makefile.authoritative-v3 -j2
coqchk -R . UELAT UELAT.UELATAuthoritativeV3
```

The GitHub Actions workflow `.github/workflows/authoritative-v3.yml` is the pinned reference environment.

## Historical material

Older v1–v2 modules are preserved for auditability and lemma reuse. The pre-authoritative repository state is also preserved at tag/branch `legacy-pre-authoritative-v3-2026-08-27`. No historical module is counted as a v3 theorem unless the status ledger explicitly says so.