# FORMALIZATION STATUS — authoritative arXiv v3 correspondence

This file is the authoritative correspondence table for:

> **Andreu Ballús Santacana, _Proof-Carrying Analytic Approximation: Local-to-Global Evidence Transport at Encoding Cost_, arXiv:2506.22693 v3.**

The manuscript is the controlling mathematical source. The repository state before this authoritative-paper migration is preserved at `legacy-pre-authoritative-v3-2026-08-27`.

## Status vocabulary

- **`CHECKED-EXACT`** — the named Rocq theorem has the same hypotheses and conclusion as the current manuscript result, is included in the current-paper build, `coqchk` succeeds, reachable assumptions have been audited, and `checked_at` records the exact audited commit.
- **`DEFINITION-EXACT`** — the current paper definition is faithfully represented and the defining module compiles. This is not a theorem-verification claim.
- **`SOURCE-MATCHED`** — a substantive Rocq statement/implementation matching the current manuscript exists in the migration surface, but the current canonical repository has not yet completed the pinned build + `coqchk` + assumptions audit required for `CHECKED-EXACT`.
- **`PARTIAL`** — substantive formal mathematics exists but a manuscript obligation, effective construction, or concrete analytic instantiation remains.
- **`PAPER-ONLY`** — no current-paper Rocq artifact yet.
- **`OLDER-SNAPSHOT-CHECKED`** — the artifact was checked against a previous v3 manuscript snapshot and is retained as reusable infrastructure. It is not automatically `CHECKED-EXACT` for this manuscript.
- **`LEGACY-V2`** — pre-v3 material that the authoritative manuscript no longer asserts.
- **`WITHDRAWN`** — an earlier claim explicitly withdrawn by the authoritative manuscript.

Only `CHECKED-EXACT` may be described as a machine-checked current-paper theorem.

## Current audit rule

A row can move to `CHECKED-EXACT` only when all of the following hold at one recorded commit:

1. the formal statement matches the authoritative manuscript at the same strength;
2. the pinned current-paper build succeeds;
3. `coqchk` succeeds on the public current-paper entry point;
4. `Print Assumptions` (or the corresponding dependency audit) has been captured and reviewed;
5. no older-snapshot theorem is being counted merely because its source compiles.

The migration therefore deliberately resets current-paper theorem claims until exact correspondence is revalidated.

---

## Section 2 — represented analytic objects and finite evidence

| Paper item | Current target | Status | Notes |
| --- | --- | --- | --- |
| Def. 2.1 Real computable Banach presentation | `Coq/V3/ComputableBanach.v`, `RepresentedSpace.v`; reusable `Presentation.v` | SOURCE-MATCHED | Current reconstruction contains rational core, Banach laws, norm/name interfaces. Existing `Presentation.v` was checked against an older snapshot and remains reusable. |
| Def. 2.2 Certificate enrichment | `CertificateEnrichment.v`; reusable `EvidenceSyntax.v` / `Evidence.v` | SOURCE-MATCHED | Must retain terminating checkers, dense finite codes, normalized spine signature and presentation-relative encoding. |
| Def. 2.3 Certificate / certificate system | `CertificateEnrichment.v`; reusable `Evidence.v` | SOURCE-MATCHED | Current-paper bound is rational `0 <= eps_bar < eps`. |
| Def. 2.4 Strict-slack completeness | `GenericSlackCertification.v`, `StrictSlackSearch.v` | SOURCE-MATCHED | Access-sensitive completeness, not a new representation. |
| Prop. 2.5 Canonical slack certification | `GenericSlackCertification.v`, `DyadicVanishing.v`, `StrictSlackSearch.v` | SOURCE-MATCHED | Finite-stage search from full Cauchy-name access. |
| Def. 2.6 Proof-relevant evidence category | `EvidenceCategory.v`; reusable `Evidence.v` | SOURCE-MATCHED | Identity/associativity are literal via normalized endpoint-indexed spines. |
| Def. 2.7 Evidence pseudometric | `SlackCollapse.v`; reusable `MetricReflection.v` | SOURCE-MATCHED | Infimum / greatest-lower-bound presentation. |
| Thm. 2.8 Conditional extensional collapse | `SlackCollapse.v`; reusable `MetricReflection.v` | SOURCE-MATCHED | Exact current-paper theorem still requires current-surface build/audit before `CHECKED-EXACT`. |

## Section 3 — universal effective linear representation

| Paper item | Current target | Status | Notes |
| --- | --- | --- | --- |
| Lem. 3.1 Effective approximate Hahn–Banach | `RealizedBoundedFunctional.v`, `ApproximateHahnBanachStrongInterface.v` | PARTIAL | Exact Type-2 contract is isolated; constructive/effective epsilon-extension implementation is the genuine remaining obligation. |
| Thm. 3.2 Effective linear Banach–Mazur universality | strong norming/coordinate/compactness/range-inverse modules; `Theorem32CoreAssemblyFixed.v` | PARTIAL | Norming-family and coordinate machinery are advanced; concrete effective compactness/Cantor-surjection/function-space/interval-extension chain still requires completion and audit. |
| Cor. 3.4 Universal finite linear representation | `C01FiniteRepresentation.v` | SOURCE-MATCHED | Pointwise finite rational polygonal/hat representation only; no AP/BAP claim. |

## Section 4 — proof-relevant evidence transport

| Paper item | Current target | Status | Notes |
| --- | --- | --- | --- |
| Def. 4.1 Finite-code realizable Lipschitz map | `EvidenceTransport.v`; reusable `RealizableMap.v` | SOURCE-MATCHED | Analytic Lipschitz derivation, Type-2 realizer and finite-code compiler. |
| Thm. 4.2 Qualitative local-transport saturation | `EvidenceTransport.v`; reusable `GenericLift.v` / `Composition.v` | SOURCE-MATCHED | Canonical three-way slack split and `Q_target = 0` local discipline. |
| Def. 4.4 Analytic maps with chosen lifts | `ProofRelevant.v`, `EvidenceReindexing.v` | SOURCE-MATCHED | Chosen evidence transformer is part of arrow data. |
| Def. 4.5 Evidence regularity | `EvidenceReindexing.v`; reusable `EffectiveCompleteness.v` | SOURCE-MATCHED | Exact self-certification + approximation-to-distance promotion. |
| Prop. 4.6 Non-faithfulness | `EvidenceReindexing.v`, `ProofRelevant.v` | SOURCE-MATCHED | Reindexing monoid `R_k` over analytic identity. |
| Prop. 4.7 Grothendieck organization | `GrothendieckEvidence.v` | SOURCE-MATCHED | Standard split opfibration; no novelty claim. |
| Def. 4.8 Evidence-local transformer | `EvidenceTransport.v`, `ResourceProfile.v` | SOURCE-MATCHED | Explicit access restriction. |
| Def. 4.9 Resource profile `(G,V,T,S,Q;L)` | `ResourceProfile.v` | SOURCE-MATCHED | Encoding/machine-relative bookkeeping only. |

## Section 5 — certified local-to-global reconstruction in `W^{1,2}(0,1)`

| Paper item | Current target | Status | Notes |
| --- | --- | --- | --- |
| Def. 5.1 Rational `W^{1,2}` presentation | `RationalSobolev*.v` | SOURCE-MATCHED | Rational continuous PWP codes, exact finite-stage squared norms, Cauchy names/checkers. |
| Lem. 5.2 Exact finite-code arithmetic | `RationalSobolev.v`, mesh/common-mesh/finite-operation modules | SOURCE-MATCHED | Exact rational operations; arbitrary rational common refinements. |
| Prop. 5.3 Concrete soundness and strict-slack completeness | `RationalSobolevCheckers.v`, `RationalSobolevCompleteness.v`, `RationalSobolevBooleanCheckers.v` | SOURCE-MATCHED | Must compile on canonical surface before exact-check label. |
| Lem. 5.4 Certified rational partitions of unity | rational interval/hat/POU construction modules | SOURCE-MATCHED | Includes rational slope bounds and multiplier interface. |
| Prop. 5.5 Exact finite synthesis | `RationalSynthesis.v` | SOURCE-MATCHED | Code synthesis and evidence composition. |
| Thm. 5.6 Certified localized PUFEM defect | `LocalizedPUFEMEvidence.v`, `LocalizedPUFEMCompiler.v`, `SobolevPUFEMAnalyticInterface.v` | PARTIAL | Finite compiler and corrected `R_j` algebra exist; concrete external/function-space instantiation of standard product-rule/bounded-overlap inequalities remains. |

## Section 6 — quantitative proof transport under one-cover gluing

| Paper item | Current target | Status | Notes |
| --- | --- | --- | --- |
| Def. 6.1 Incremental transport resources | `ProofDAG.v`, `ProofDAGEncodingAppend.v`, `ResourceProfile.v` | SOURCE-MATCHED | Shared self-contained DAG with binary references. |
| Thm. 6.2 Single-cover provenance compiler | `PUFEMCompiler.v`, `LocalizedPUFEMCompiler.v` | SOURCE-MATCHED | `Delta S`, verification bound, structural node count and literal `Q_target=0`. |
| Prop. 6.3 Weighted global approximation budget | `WeightedSynthesisBudget.v`, `PUFEMCompiler.v` | SOURCE-MATCHED | **Authoritative weight is `max(C_inf^2 + 2 L_i^2, 2 C_inf^2)`. Older `3 C_inf^2 + 2 L_i^2` implementation is superseded.** |
| Prop. 6.4 Global rational-code size | `GlobalCodeSize.v`, `RationalBitBudget.v` | SOURCE-MATCHED | Fixed raw binary-rational encoding; no representation-invariance claim. |

## Section 7 — proof-carrying refinement and represented-limit transport

| Paper item | Current target | Status | Notes |
| --- | --- | --- | --- |
| Def. 7.1 Provenance-complete certificate | `ProofDAG.v`, `FiniteCodeDescent.v` | SOURCE-MATCHED | Rooted shared DAG, accepted reachable nodes, sink identifies constructed code. |
| Thm. 7.2 Classical scale-sensitive PUFEM estimate | `ScaleSensitivePUFEMAnalytic.v`, `Refinement.v` | PARTIAL | Current algebra derives `C_* = kappa((1+C_chi)C0+C1)` from standard aggregate inequalities; concrete Sobolev-library instantiation remains. |
| Prop. 7.3 Concrete compiler bound for standard local encodings | `H6EncodingRegime.v`, `StandardRationalH1H7.v`, compiler/resource modules | SOURCE-MATCHED | Must be exposed under the exact new proposition number. |
| Thm. 7.4 Encoding-cost evidence transport under Sobolev refinement | `H1H7Descent.v`, `OrderNeutralEpsilonDescent.v`, `ManuscriptH1H7.v`, new `Theorem74Manuscript.v` | SOURCE-MATCHED | Main H1--H7 theorem: represented limit, `m(eps)`, complete genealogy `O(B_m)`, standard-regime asymptotic, `Q_target=0`, conditional `Q_source`, verification bound. |
| Cor. 7.5 Same-order transport in the standard rational regime | `StandardRationalRegime.v`, `StandardRationalH1H7.v` | SOURCE-MATCHED | No two-sided certificate lower bound. |
| Ex. 7.6 / Ex. 7.7 failure modes | `DescentFailureModes.v` | SOURCE-MATCHED | Geometric-history and payload-comparability failures kept separate. |

## Section 8 — Contextual Choice

| Paper item | Current target | Status | Notes |
| --- | --- | --- | --- |
| Def. 8.1 CCP-admissible constructor | `ContextualChoice.v` | SOURCE-MATCHED | Finite access plus explicit modulus/interface requirement. |
| Prop. 8.2 Closure under admissible constructors | `ContextualChoice.v`, `CCPCompilerInstances.v`, `CCPSynthesisInstance.v` | SOURCE-MATCHED | Identity/product/composition plus cited concrete constructors. |
| Def. 8.3 Contextual Choice Principle | `ContextualChoice.v` | SOURCE-MATCHED | Internal certified-development discipline only. |
| Def. 8.4 CCP-generated universe | `ContextualChoice.v` | SOURCE-MATCHED | Least typed closure, not a Grothendieck universe. |
| Thm. 8.5 Invariant preservation | `ContextualChoice.v` | SOURCE-MATCHED | Structural induction over generated closure. |
| Cor. 8.6 Internal Banach–Tarski boundary | `FiniteMeasureBoundary.v` | SOURCE-MATCHED | Internal finite-measure generated-class statement; ambient classical theorem untouched. |

## Section 9 — information boundaries and exact extensional gluing

| Paper item | Current target | Status | Notes |
| --- | --- | --- | --- |
| Prop. 9.1 Fibre indistinguishability | `InformationBoundary.v` | SOURCE-MATCHED | Model-relative finite-information obstruction. |
| Prop. 9.2 Extensional sheaf placement | `ExtensionalSheaf.v` | SOURCE-MATCHED | Ordinary sheaf after zero-distance quotient; no enriched sheaf or stack claim. |

## Explicitly withdrawn / legacy claims

| Earlier claim | Current status |
| --- | --- |
| Probes–models adjunction as stated in earlier versions | WITHDRAWN |
| Universal finite-rank projection / approximation-property formulation of UELAT | WITHDRAWN |
| Incorrect Chebyshev/B-spline worked calculations identified in revision | WITHDRAWN |
| Priority claim for generic certificate stability | WITHDRAWN; effective completion/strict-slack certification is background |

## Migration / verification state

The large current-paper reconstruction originated in `andreu-toposcircuitry/UELAT` and is being consolidated into this canonical repository. Existing `ipsissima/UELAT` Rocq-checked modules are preserved and reused where they are stronger. During migration, `SOURCE-MATCHED` means source-level current-paper correspondence, **not** kernel verification in this repository.

No blanket machine-checked claim is made. The public manuscript itself says the same.
