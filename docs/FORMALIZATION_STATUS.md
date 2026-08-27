# FORMALIZATION_STATUS.md — authoritative v3 correspondence

This file is the **authoritative correspondence table** required by Section 12 of:

> Andreu Ballús Santacana, *Proof-Carrying Analytic Approximation: Local-to-Global Evidence Transport at Encoding Cost*, arXiv:2506.22693 v3.

The 35-page manuscript supplied for the 2026-08-27 repository migration is the controlling source for title, numbering, hypotheses, conclusions, and limitations. Earlier v3 draft titles and numbering are superseded.

## Status vocabulary

| label | meaning |
| --- | --- |
| `CHECKED-EXACT` | Rocq theorem has the same statement and strength as the current manuscript result, is on the declared current build surface, has passed `coqchk`, and has an audited assumption snapshot at the recorded commit. |
| `DEFINITION-EXACT` | Current manuscript definition is faithfully represented by a compiled Rocq definition/record. This is not a machine-checked theorem claim. |
| `CHECKED-RESTRICTED` | Correct checked theorem, but with a documented delta from the manuscript statement. |
| `CHECKED-ANALYTIC-CORE` | A classical analytic lemma used by the paper is checked, but the full manuscript evidence/resource statement is not. |
| `IN-PROGRESS` | A substantive current-manuscript formalization path exists, but exact-current correspondence, build, `coqchk`, or assumption audit is not yet complete. |
| `PAPER-ONLY` | No substantive Rocq artifact for the current result. |
| `LEGACY-V2` | Historical v1/v2 material not asserted by the current paper. |
| `SUPERSEDED-V3` | Formalization targeted an earlier v3 manuscript snapshot and is not evidence for the current numbered result without a new correspondence audit. |
| `FAILED-AUDIT` | A previous formal claim failed statement/proof audit. |

**Only `CHECKED-EXACT` rows may be described as machine-checked current-paper results.** During this migration no row is promoted merely because a related older module compiled.

## Current migration rule

The branch `authoritative-v3-final` imports the reconstructed proof-carrying/Sobolev and effective-universality development into this public repository while retaining the existing Rocq-9 audit infrastructure. Until the new authoritative build surface has run successfully, imported rows remain `IN-PROGRESS` even when the underlying source branch contains a completed proof script.

The pre-migration public `main` is preserved at `legacy-pre-authoritative-v3-2026-08-27`.

## Section 2 — represented analytic objects and finite evidence

| current paper item | target | status | current delta / audit note |
| --- | --- | --- | --- |
| Definition 2.1 — real computable Banach presentation | `Coq/V3/ComputableBanach.v`, `RepresentedSpace.v` | IN-PROGRESS | Current reconstruction supplies metric/Banach structure, rational core, norm procedure and fast names; exact-current build audit pending. |
| Definition 2.2 — certificate enrichment + normalized endpoint-indexed proof spine | `Coq/V3/CertificateEnrichment.v` plus existing `EvidenceSyntax.v` normalization layer | IN-PROGRESS | Must integrate the imported enrichment interface with the already-audited strict spine implementation before `DEFINITION-EXACT`. |
| Definition 2.3 — certificate and certificate system | `CertificateEnrichment.v` / existing `Evidence.v` | IN-PROGRESS | Current manuscript uses rational tolerances and fixed binary length accounting; exact type reconciliation pending. |
| Definition 2.4 — strict-slack completeness | `StrictSlackSearch.v`, `GenericSlackCertification.v` | IN-PROGRESS | Effective finite-stage search path exists; current build audit pending. |
| Proposition 2.5 — canonical slack certification | `StrictSlackSearch.v`, `DyadicVanishing.v`, `GenericSlackCertification.v` | IN-PROGRESS | Substantive constructive search is present; promote only after exact statement/build/assumptions audit. |
| Definition 2.6 — proof-relevant evidence category | `EvidenceCategory.v` + `EvidenceSyntax.v` | IN-PROGRESS | Current paper requires literal strict identity/associativity from normalized spines; integration pending. |
| Definition 2.7 — evidence pseudometric | `SlackCollapse.v` and existing `MetricReflection.v` | IN-PROGRESS | Need one current canonical implementation of the infimum/greatest-lower-bound semantics. |
| Theorem 2.8 — conditional extensional collapse | `SlackCollapse.v` / `MetricReflection.v` | IN-PROGRESS | Older restricted result exists; imported current route must be reconciled and freshly audited. |

## Section 3 — universal effective linear representation

| current paper item | target | status | current delta / audit note |
| --- | --- | --- | --- |
| Lemma 3.1 — effective approximate Hahn–Banach | `RealizedBoundedFunctional.v`, `ApproximateHahnBanachStrongInterface.v`, `NormalizedApproxHBStrong.v` | IN-PROGRESS | Strong Type-2 contract is explicit. The constructive/effective epsilon-extension implementation remains the principal mathematical obligation. |
| Theorem 3.2 — effective linear Banach–Mazur universality | strong norming/coordinate/compactness/range-inverse modules; manuscript wrapper to be `Theorem32...` | IN-PROGRESS | Norming, coordinate ball, semidecidable complement and inverse-search machinery exist. Effective compactness/Cantor/function-space/interval-extension chain still requires exact end-to-end closure and fresh kernel audit. |
| Corollary 3.4 — universal finite linear representation | `C01FiniteRepresentation.v` | IN-PROGRESS | Standard computable `C([0,1])` rational polygonal-core path exists; exact dependency on a checked Theorem 3.2 remains. |

No current result asserts AP/BAP or universal finite-rank approximation of the identity.

## Section 4 — proof-relevant evidence transport

| current paper item | target | status | current delta / audit note |
| --- | --- | --- | --- |
| Definition 4.1 — finite-code realizable Lipschitz map | `EvidenceTransport.v` / existing `RealizableMap.v` | IN-PROGRESS | Reconcile the two interfaces around the current three-clause finite-code compiler definition. |
| Theorem 4.2 — qualitative local-transport saturation | `EvidenceTransport.v`, existing `GenericLift.v` | IN-PROGRESS | Canonical alpha/epsilon-third transport path exists; exact-current spine integration/build pending. |
| Definition 4.4 — analytic maps with chosen lifts | `ProofRelevant.v`, `GrothendieckEvidence.v` | IN-PROGRESS | Current arrow identity must retain selected evidence functor. |
| Definition 4.5 — evidence regularity | `EvidenceReindexing.v` and existing `EffectiveCompleteness.v` | IN-PROGRESS | Exact self-certificate and approximation-to-distance promotion path exists. |
| Proposition 4.6 — non-faithfulness | `EvidenceReindexing.v`, `ProofRelevant.v` | IN-PROGRESS | Precision reindexing monoid path exists; current exact category integration pending. |
| Proposition 4.7 — Grothendieck organization | `GrothendieckEvidence.v` | IN-PROGRESS | Standard strict Cat-valued construction path exists. |
| Definition 4.8 — evidence locality | `EvidenceTransport.v` | IN-PROGRESS | Access discipline represented operationally; current wording audit pending. |
| Definition 4.9 — resource profile `(G,V,T,S,Q;L)` | `ResourceProfile.v` | IN-PROGRESS | Current bookkeeping interface exists. |

## Section 5 — certified local-to-global reconstruction in W^{1,2}(0,1)

| current paper item | target | status | current delta / audit note |
| --- | --- | --- | --- |
| Definition 5.1 — rational W1,2 presentation | rational Sobolev presentation/checker modules | IN-PROGRESS | Exact rational piecewise-polynomial arithmetic and finite-stage checker path exists; import/build pending. |
| Lemma 5.2 — exact finite-code arithmetic | `RationalSobolev.v`, mesh/refinement/finite-operation modules | IN-PROGRESS | Exact Q arithmetic path exists; fresh build audit pending. |
| Proposition 5.3 — concrete soundness and strict-slack completeness | Sobolev checker/completeness modules | IN-PROGRESS | Terminating rational boolean checker route exists. |
| Lemma 5.4 — certified rational partitions of unity | rational hat/interval/assignment/construction modules | IN-PROGRESS | Finite rational star assignment and grouped nodal-hat construction exist. Multiplier/zero-extension analytic bridge remains part of the end-to-end Sobolev audit. |
| Proposition 5.5 — exact finite synthesis | `RationalSynthesis.v` | IN-PROGRESS | Exact code synthesis/evidence compiler path exists. |
| Theorem 5.6 — certified localized PUFEM defect | `RationalPUFEM.v`, `LocalizedPUFEMCompiler.v`, `LocalizedPUFEMEvidence.v`, `SobolevPUFEMAnalyticInterface.v` | IN-PROGRESS | Correct manuscript A_j^2/B_j^2/R_j algebra and compiler exist at a standard analytic interface; concrete W1,2 product-rule/bounded-overlap instantiation remains. |

## Section 6 — quantitative one-cover proof transport

| current paper item | target | status | current delta / audit note |
| --- | --- | --- | --- |
| Definition 6.1 — incremental resources/shared DAG | proof-DAG/resource modules | IN-PROGRESS | Shared backward-reference encoding path exists. |
| Theorem 6.2 — single-cover provenance compiler | `PUFEMCompiler.v`, `LocalizedPUFEMCompiler.v` | IN-PROGRESS | Delta-S, verification and `Q_target=0` path exists. Must be rebuilt after authoritative weight update. |
| Proposition 6.3 — weighted global approximation budget | **authoritative replacement of `WeightedSynthesisBudget.v`/`PUFEMCompiler.v`** | IN-PROGRESS | **Current manuscript weight is `w_i^2 = max(C_inf^2 + 2 L_i^2, 2 C_inf^2)`. The older reconstructed `3 C_inf^2 + 2 L_i^2` weight is superseded and must not be cited as exact.** |
| Proposition 6.4 — global rational-code size | `RationalBitBudget.v`, `GlobalCodeSize.v` | IN-PROGRESS | Mesh/degree/bit-growth path exists; current build audit pending. |

## Section 7 — proof-carrying refinement and represented-limit transport

| current paper item | target | status | current delta / audit note |
| --- | --- | --- | --- |
| Definition 7.1 — provenance-complete certificate | `ProofDAG.v`, `FiniteCodeDescent.v` | IN-PROGRESS | Rooted shared genealogy representation exists. |
| Theorem 7.2 — classical scale-sensitive PUFEM estimate | `ScaleSensitivePUFEMAnalytic.v` | IN-PROGRESS | Manuscript constant `C_* = kappa((1+C_chi)C0+C1)` is derived at an aggregate standard-analytic interface; concrete W1,2 instantiation remains. |
| Proposition 7.3 — concrete compiler bound for standard local encodings | encoding/bit-budget/descent modules | IN-PROGRESS | Must have a dedicated current-numbered wrapper; previously conflated with the old “Theorem 7.3” wrapper. |
| **Theorem 7.4 — encoding-cost evidence transport under Sobolev refinement** | `H1H7Descent.v`, `DescentCertificateSize.v`, `FiniteCodeDescent.v`, `EpsilonPrecision.v`, `OrderNeutralEpsilonDescent.v`, `ManuscriptH1H7.v`, new `Theorem74Manuscript.v` | IN-PROGRESS | Core rational-epsilon theorem already carries represented limit, size, verification, source-lookahead and `Q_target=0`. The authoritative wrapper must expose the current H1–H7 statement and numbering and be freshly audited. |
| Corollary 7.5 — standard rational regime | `StandardRationalRegime.v`, `StandardRationalH1H7.v`, `H6EncodingRegime.v` | IN-PROGRESS | Standard `O(epsilon^{-1/(r-1)}(1+log(1/epsilon)))` route exists; current-numbered wrapper/audit pending. |
| Example 7.6 — failure without summable refinement history | `DescentFailureModes.v` | IN-PROGRESS | Structural counterexample path exists. |
| Example 7.7 — failure without proof-payload comparability | `DescentFailureModes.v` | IN-PROGRESS | Structural counterexample path exists. |

## Section 8 — Contextual Choice

| current paper item | target | status | current delta / audit note |
| --- | --- | --- | --- |
| Definition 8.1 — CCP-admissible constructor | `ContextualChoice.v` | IN-PROGRESS | Finite-access/modulus constructor interface exists. |
| Proposition 8.2 — closure under admissible constructors | `ContextualChoice.v`, compiler-instance modules | IN-PROGRESS | Id/product/composition and concrete compiler instances exist at declared interfaces. |
| Definition 8.3 — Contextual Choice Principle | `ContextualChoice.v` | IN-PROGRESS | Generated/admissible promotion discipline exists. |
| Definition 8.4 — CCP-generated universe | `ContextualChoice.v` | IN-PROGRESS | Least typed closure exists. |
| Theorem 8.5 — invariant preservation | `ContextualChoice.v` | IN-PROGRESS | Structural-induction proof path exists. |
| Corollary 8.6 — internal finite-measure boundary | `FiniteMeasureBoundary.v` | IN-PROGRESS | Internal finite-additivity contradiction path exists; ambient Banach–Tarski is untouched. |

## Section 9 — information boundaries and exact extensional gluing

| current paper item | target | status | current delta / audit note |
| --- | --- | --- | --- |
| Proposition 9.1 — fibre indistinguishability | `InformationBoundary.v` | IN-PROGRESS | Noninjective finite-information fibre obstruction path exists. |
| Proposition 9.2 — extensional sheaf placement | `ExtensionalSheaf.v` | IN-PROGRESS | Exact represented gluing after zero-distance quotient is modelled; no enriched-sheaf/stack claim. |

## Explicitly withdrawn/superseded material

- `Coq/Adjunction/` probes–models adjunction: **LEGACY-V2 / withdrawn at the former level of generality**.
- Old universal finite-rank UELAT wrapper: **LEGACY-V2**.
- Incorrect Chebyshev/B-spline numerical worked material: **not current**.
- Generic certificate-stability priority claim: **not current**; effective completion/strict slack are background.
- Earlier v3 theorem numbering and titles, including the manuscript-facing name `Theorem73Manuscript`: **SUPERSEDED-V3** once the authoritative `Theorem74Manuscript` wrapper is installed.

## Promotion checklist

A row moves to `CHECKED-EXACT` only after all of the following at one recorded commit:

1. exact comparison with the 35-page authoritative manuscript;
2. pinned/current Rocq build succeeds for the declared authoritative surface;
3. `coqchk` succeeds;
4. `Print Assumptions` output is captured and reviewed;
5. no undeclared `Admitted`, `admit`, or project-level `Axiom` is reachable;
6. the row records the audited commit SHA.

Until then, this table deliberately understates rather than overstates machine verification.
