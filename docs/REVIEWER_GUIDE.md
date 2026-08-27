# Reviewer guide

This page is the shortest path from the manuscript to the formal artifacts.

The manuscript is the controlling mathematical source:

> Andreu Ballús Santacana, *Proof-Carrying Analytic Approximation: Local-to-Global Evidence Transport at Encoding Cost*, arXiv:2506.22693 v3.

## Five-minute audit

1. Read [`FORMALIZATION STATUS.md`](./FORMALIZATION%20STATUS.md). It is the authoritative theorem-by-theorem correspondence table.
2. Inspect [`../Coq/_CoqProject.authoritative-v3`](../Coq/_CoqProject.authoritative-v3). Only files on this project surface are candidates for current-paper verification.
3. Inspect [`../Coq/UELATAuthoritativeV3.v`](../Coq/UELATAuthoritativeV3.v). This is the public aggregate entry point used for `coqchk`.
4. Check the **Authoritative v3** GitHub Actions workflow. Its job builds the pinned current-paper project, then runs `coqchk`, then rejects proof admissions on the authoritative surface.
5. Treat a theorem as machine-checked only if its row in `FORMALIZATION STATUS.md` is `CHECKED-EXACT` at a recorded commit.

A green broad repository build is useful engineering evidence, but it is not itself a current-paper theorem claim. Conversely, legacy or experimental modules outside the authoritative project are not part of the audited theorem surface.

## Status meanings

- `CHECKED-EXACT`: manuscript statement matched at the same strength, authoritative build succeeds, `coqchk` succeeds, and reachable assumptions are audited at the recorded commit.
- `SOURCE-MATCHED`: a substantive current-paper formal statement or implementation exists, but the complete build/check/audit contract has not yet been discharged.
- `PARTIAL`: a real formalization exists, but a mathematical construction, effective realization, or concrete analytic instantiation remains.
- `OLDER-SNAPSHOT-CHECKED`: checked infrastructure from an earlier v3 snapshot; reusable, but not evidence for the authoritative theorem by itself.
- `WITHDRAWN` / `LEGACY-V2`: historical claims not asserted by v3.

## Current-paper architecture

The formalization follows the manuscript rather than the repository's historical chronology.

| Manuscript layer | Main formal area |
| --- | --- |
| §2 represented spaces and evidence | `CertificateEnrichment.v`, `RepresentedSpace.v`, `ComputableBanach.v`, slack/evidence-category modules |
| §3 effective linear universality | norming, coordinate-dual-ball, compactness, range-inverse and finite-representation modules |
| §4 proof-relevant transport | `EvidenceTransport.v`, `EvidenceReindexing.v`, `ProofRelevant.v`, `GrothendieckEvidence.v`, `ResourceProfile.v` |
| §§5–6 rational `W^{1,2}` reconstruction/compiler | rational Sobolev, mesh, hat/POU, synthesis, PUFEM, proof-DAG and bit-budget modules |
| §7 refinement/descent | geometry, precision schedule, H1–H7 descent, encoding regime and `Theorem74Manuscript.v` |
| §§8–9 boundaries/semantics | `ContextualChoice.v`, `FiniteMeasureBoundary.v`, `InformationBoundary.v`, `ExtensionalSheaf.v` |

The complete directory contains additional helper and migration modules. Inclusion in `Coq/V3/` does **not** imply theorem status; `_CoqProject.authoritative-v3` and the status ledger are controlling.

## Reproducing the authoritative check locally

With Rocq 9.2 available:

```sh
cd Coq
coq_makefile -f _CoqProject.authoritative-v3 -o Makefile.authoritative-v3
make -f Makefile.authoritative-v3 -j2
coqchk -R . UELAT UELAT.UELATAuthoritativeV3
```

The GitHub workflow is the reproducible pinned reference. It should be used when local package versions differ.

## What the repository does not claim

The repository does not claim that:

- every file under `Coq/V3/` is part of the current paper;
- a compiling helper module proves the corresponding manuscript theorem;
- old CI success transfers automatically to the authoritative manuscript;
- the entire paper is machine-checked merely because an aggregate builds;
- standard analytic or categorical background becomes novel by being represented in Rocq.

The purpose of the repository is narrower: to make exact theorem correspondence, dependencies, compilation state, kernel checking and remaining obligations inspectable.