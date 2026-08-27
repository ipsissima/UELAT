# Authoritative-v3 formalization map

`V3/` is intentionally flat because the Rocq logical paths were stabilized during reconstruction. It should be read by **manuscript section**, not alphabetically or chronologically.

**Important:** presence in this directory is not a verification claim. The controlling build surface is [`../_CoqProject.authoritative-v3`](../_CoqProject.authoritative-v3), and theorem status is controlled by [`../../docs/FORMALIZATION STATUS.md`](../../docs/FORMALIZATION%20STATUS.md).

## §2 — represented analytic objects and finite evidence

Core entry points include:

- `CertificateEnrichment.v`
- `RepresentedSpace.v`
- `ComputableBanach.v`
- `GenericSlackCertification.v`
- `StrictSlackSearch.v`
- `EvidenceCategory.v`
- `SlackCollapse.v`

Reusable earlier-v3 infrastructure includes `Presentation.v`, `EvidenceSyntax.v`, `Evidence.v`, `MetricReflection.v` and `EffectiveCompleteness.v`.

## §3 — universal effective linear representation

The implementation is decomposed because this is the technically sensitive part of the manuscript. Main families include:

- realized bounded functionals and approximate Hahn–Banach interfaces;
- nonzero-core search and norming-family construction;
- `LinearUniversality.v` and `NormingPolar.v`;
- coordinate dual-ball / closedness / semidecision modules;
- effective compactness and Cantor/function-space bridge modules;
- range-inverse and finite `C([0,1])` representation modules;
- manuscript-facing theorem assembly modules.

The exact remaining obligations for Lemma 3.1 and Theorem 3.2 are recorded as `PARTIAL` in the status ledger. Do not infer completion from the existence of strong-interface or assembly files.

## §4 — proof-relevant evidence transport

Main modules:

- `EvidenceTransport.v`
- `EvidenceReindexing.v`
- `ProofRelevant.v`
- `GrothendieckEvidence.v`
- `ResourceProfile.v`

Reusable infrastructure includes `RealizableMap.v`, `GenericLift.v` and `Composition.v`.

## §§5–6 — rational `W^{1,2}` reconstruction and one-cover compiler

The finite arithmetic and compiler chain is split into:

- rational Sobolev code/presentation/checker modules;
- arbitrary/common mesh refinement;
- rational interval-cover, hat and partition-of-unity construction;
- exact synthesis;
- PUFEM analytic/evidence/compiler interfaces;
- proof DAG and encoding append machinery;
- weighted synthesis, global-code and rational bit budgets.

The decomposition distinguishes exact finite-code computation from the external/standard Sobolev inequalities used by the manuscript.

## §7 — refinement, represented limits and encoding cost

Main families:

- quasi-uniform geometry and scale-sensitive PUFEM estimates;
- persistent genealogy and descent assembly;
- geometric precision schedules and epsilon selection;
- H1–H7 theorem data and descent;
- certificate-size and encoding-regime bounds;
- standard rational regime;
- `Theorem74Manuscript.v` as the manuscript-facing Theorem 7.4 wrapper.

## §§8–9 — generated semantics and boundaries

Main modules:

- `ContextualChoice.v`
- `FiniteMeasureBoundary.v`
- `InformationBoundary.v`
- `ExtensionalSheaf.v`

These modules deliberately distinguish structural/semantic placement from novelty claims in analysis or category theory.

## Names such as `Strong`, `Fixed`, numbered variants and bridges

These are implementation-level modules produced while decomposing dependencies or replacing weaker interfaces. They are **not parallel manuscript theorems**. A reviewer normally does not need to inspect them unless auditing a dependency of a status-table row.

For the shortest external audit path, start at [`../../docs/REVIEWER_GUIDE.md`](../../docs/REVIEWER_GUIDE.md).