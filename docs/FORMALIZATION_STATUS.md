# FORMALIZATION_STATUS.md — v3 theorem correspondence

This document is the authoritative record of correspondence between
theorems in

> Ballús Santacana, *Universal Gluing and Contextual Choice:
> Certificate-Carrying Approximation, Functorial Evidence, and
> Effective Descent*, arXiv:2506.22693 v3

and Rocq artifacts in this repository. It replaces every earlier
document that claimed "all main theorems are proven" or "scientifically
complete". The only theorems in the v3 paper that may be described as
machine-checked are the ones with status `CHECKED-EXACT` below, at the
commit hash CI stamped on that row's `checked_at` column.

## Status vocabulary

| label | meaning |
| --- | --- |
| `CHECKED-EXACT` | The named Rocq **theorem** has the same statement, at the same strength (same hypotheses, same conclusion), as the paper theorem, and lives on a `coqchk`-clean dependency path in the CI-built module set. Applies to theorems / propositions / lemmas — assertions with mathematical content. |
| `DEFINITION-EXACT` | The named Rocq **definition** (record, inductive, or `Definition`) has been checked to correspond exactly to a paper definition. This is NOT itself a machine-checked theorem — it means the object is faithfully modelled. The Print Assumptions audit does not apply. |
| `CHECKED-RESTRICTED` | The named Rocq theorem is valid, but its statement adds hypotheses / narrows a quantifier / restricts to a domain that the paper theorem does not. The delta is stated. |
| `CHECKED-ANALYTIC-CORE` | A classical analytic lemma the paper uses is checked, but not the evidence-level v3 statement built around it. |
| `LEGACY-V2` | Formalizes a v1/v2 statement that v3 no longer asserts (withdrawn or restated). Kept for historical reasons. Not a v3 theorem. |
| `PAPER-ONLY` | Proved in the paper, no Rocq artifact exists. |
| `IN-PROGRESS` | Rocq module exists in `Coq/V3/` (or a designated scratch location) with a placeholder or partial proof — must not be advertised as checked. |
| `FAILED-AUDIT` | An earlier repository incarnation claimed this as checked, but an audit found the statement false as written, vacuous, or proved from inconsistent local assumptions. Details in `docs/LEGACY_AUDIT.md`. |

**The advertised machine-checked v3 theorem list is `CHECKED-EXACT` only.** `DEFINITION-EXACT` rows say "we modelled the paper's object faithfully" — not "we proved a theorem". `CHECKED-RESTRICTED` rows say "we proved a weaker or otherwise deltaed statement". Neither counts as machine-checked v3 in the sense of paper §18.

An entry may only advance to `CHECKED-EXACT` when all of:

1. The current CI is green on the relevant module.
2. `coqchk` reports the module clean in the CI enumeration.
3. `Print Assumptions <theorem>` has been captured and reviewed.
4. A comment in the .v file records the paper theorem, the Rocq
   theorem, and the correspondence class, as required by section 11
   of the project brief.

## v3 correspondence table

Rows are ordered by paper appearance. `module` is repo-relative;
`Rocq theorem` is the exact `Theorem`/`Corollary`/`Proposition`/`Lemma`
name. `—` means no artifact exists. The `assumptions` column lists
non-obvious dependencies beyond the paper's declared mathematical
hypotheses; a Rocq artifact should never depend on axioms not either
inherent in Stdlib+MathComp (functional extensionality, classical
choice as separately noted, etc.) or explicit hypotheses of the paper
theorem.

| v3 paper result | section | Rocq theorem | module | status | assumptions | notes |
| --- | --- | --- | --- | --- | --- | --- |
| Def 2.1 Approximation presentation | §2 | `V3_Presentation.Presentation` record | `Coq/V3/Presentation.v` | IN-PROGRESS | — | Semantic checker core of Def 2.1: abstract `CodeF`, `NameF`, `F` carriers; analytic `distF` with metric axioms; decoders `rhoF`, `deltaF`, `iotaF`; `AppCheck` / `DistCheck` soundness in the `distF` shape. Def 2.1 additionally requires an effectively enumerable `CodeF` with dense decoding range in the completion, and a represented subdomain `D_F ⊆ F` with `deltaF` surjective onto it — neither is encoded yet. Future refinement will add `EnumerableCode`, a represented-domain predicate/subtype, and a density property. |
| Prop 2.4 Norm-enclosure ⇒ certificate system | §2 | — | — | PAPER-ONLY | — | To be `Coq/V3/Presentation.v :: certificate_system_from_enclosure`. |
| Prop 2.5 Hilbert presentation | §2 | — | — | PAPER-ONLY | — | Parseval-based construction; requires a Hilbert-space interface. |
| Prop 2.7 Finite product presentations | §2 | — | — | PAPER-ONLY | — | Tuple/max-norm; naturally follows the record definition. |
| Def 2.3 Certificate system | §2 | `V3_Evidence.CertSystem` | `Coq/V3/Evidence.v` | IN-PROGRESS | closure record `EvidenceClosure` for the presentation | Rocq record matches Def 2.3 (procedure returning `(p, ε̄, V)` with `ε̄ < ε` and `AppCheck` accept). |
| Def 3.1 Proof-relevant evidence category | §3 | `V3_Evidence.EvidenceObject`, `V3_Evidence.EvidenceMorphism`, `V3_Evidence.id_evidence`, `V3_Evidence.comp_evidence` | `Coq/V3/Evidence.v` | IN-PROGRESS | `EvidenceClosure P` (reflexivity/weakening/symmetry/triangle witnesses) | Objects/morphisms/identity/composition constructors match Def 3.1. On-the-nose category laws pending proof-tree normalization; arithmetic content of the bounds is proved (`id_evidence_bound`, `comp_evidence_*_bound`). |
| Def 3.2 Lawvere metric `d_Cert` | §3 | `V3_MetricReflection.is_lawvere_dist` (predicate) | `Coq/V3/MetricReflection.v` | IN-PROGRESS | — | Prop-level specification: `r` is the Lawvere distance iff it is a lower bound of accepted rational bounds and a greatest lower bound. Uniqueness proved (`is_lawvere_dist_unique`). No infimum-as-term construction — deliberately avoided. |
| Prop 3.3 Soundness of evidence metric (lower-bound half) | §3 | `V3_MetricReflection.prop_3_3_lower_bound` (+ corollary `lawvere_bounds_analytic`) | `Coq/V3/MetricReflection.v` | CHECKED-RESTRICTED | — | The lower-bound direction: every accepted rational bound dominates `distF`. Full Prop 3.3 also includes surjectivity of the certifiable-subset image, deferred to a downstream module that will invoke Prop 2.4. |
| Def 4.1 Distance adequacy | §4 | `V3_MetricReflection.distance_adequate` | `Coq/V3/MetricReflection.v` | DEFINITION-EXACT | — | Exact restatement of the paper definition. Not itself a theorem. |
| Thm 4.4 Extensional collapse (first equation) | §4 | `V3_MetricReflection.extensional_collapse` | `Coq/V3/MetricReflection.v` | CHECKED-RESTRICTED | rational density hypothesis `Q_dense_R` | Proves `is_lawvere_dist c d (distF …)` under distance adequacy AND a `Q dense in R` hypothesis passed as a Section variable. The hypothesis is a true fact of ℝ; a follow-up commit will discharge it inline. Quotient-object statement (isometry to certifiable subset, separated reflection universal property) not yet formalized. |
| Def 5.1 Certifiably realizable Lipschitz map | §5 | `V3_RealizableMap.RealizableMap` | `Coq/V3/RealizableMap.v` | IN-PROGRESS | — | The Rocq record does NOT match v3 Def 5.1 as stated. v3 Def 5.1 has four clauses — analytic Lipschitz map with a **stored finite derivation** in the evidence language, name transformer with naturality, finite-code realizer with defect witness, distance-evidence transformer Θ_T that **preserves identity and concatenation on the nose**. The current Rocq record has five components (adds a separate `rm_app_promote` transformer that Def 5.1 does not have), does not represent the stored derivation as evidence, and does not encode the strict identity/composition laws for Θ_T. Follow-up commit will restructure the record to the paper's four clauses and add the strict-coherence obligations. |
| Thm 5.2 Generic lifting — achievable-bound Lipschitz | §5 | `V3_RealizableMap.lift_dist_accepted`, `V3_RealizableMap.analytic_lipschitz` | `Coq/V3/RealizableMap.v` | IN-PROGRESS | inherits the Def 5.1 mismatch | Depends on `RealizableMap`; downgraded to `IN-PROGRESS` in tandem with the Def 5.1 row. The `lift_dist_accepted` and `analytic_lipschitz` lemmas are individually correct against the current record but do not express the full Thm 5.2 content and cannot be claimed as an EXACT correspondence with the paper until the Def 5.1 record itself matches. |
| Prop 5.3 Identity + composition of lifts | §5 | — | — | PAPER-ONLY | — | Deferred pending Q-arithmetic bookkeeping (aligning 1*r with r etc.). |
| Thm 5.6 Grothendieck construction / split opfibration | §5 | — | — | PAPER-ONLY | — | Standard categorical argument once Def 5.4 is stated. |
| Thm 5.8 Presentation invariance | §5 | — | — | PAPER-ONLY | — | Requires Def 5.7 effective equivalence + distance adequacy + Thm 4.4. |
| Def 4.3 Evidence-regular presentation | §4 | `V3_EffectiveCompleteness.EvidenceRegular` | `Coq/V3/EffectiveCompleteness.v` | DEFINITION-EXACT | — | Two-constructor record (exact witness for canonical name; approximation-to-distance promotion). Reverse-bound remark proved as the lemma `er_promote_reverse_ok` (which is itself the theorem-side of this definition — see the Def 4.3 remark). Not itself a theorem. |
| Def 6.4 Principal evidence | §6 | `V3_EffectiveCompleteness.principal_cert_system`, `V3_EffectiveCompleteness.principal_evidence` | `Coq/V3/EffectiveCompleteness.v` | DEFINITION-EXACT | evidence-regular presentation | Certificate system returns `(p, 0, er_exact_witness p)` at every positive tolerance. Not itself a theorem. |
| Thm 6.2 Effective limits lift to evidence | §6 | — | — | PAPER-ONLY | — | Uses effective completeness (Def 6.1). Def 6.1 as a Rocq record not yet added. |
| Thm 6.5 (1) Density of principal evidence | §6 | `V3_EffectiveCompleteness.principal_evidence_dense` (+ analytic corollary `principal_evidence_dense_analytic`) | `Coq/V3/EffectiveCompleteness.v` | CHECKED-RESTRICTED | evidence-regular presentation, evidence-closure record | For every ε>0 there is a code p and bound q with `0 ≤ q < ε` and DistCheck between the name of c and iota_F(p) at bound q. The Lawvere-distance form `d_Cert(c, hat_p) < ε` follows once `MetricReflection.v` provides d_Cert as a term. The certified-Cauchy-modulus part of Thm 6.5 needs Thm 6.2. |
| Thm 6.5 (2) Cauchy limits of principal evidence | §6 | — | — | PAPER-ONLY | — | Requires Thm 6.2. |
| Thm 7.2 Certified synthesis and reconstruction | §7 | — | — | PAPER-ONLY | — | The v3 substantive local-to-global result; carries the reconstruction datum of Def 7.1 including proof-transport interfaces `Γ_Σ`, `Γ_R`. Distinct from the v2 syntactic `GlueCert` in `Coq/Approx/EffectiveDescent.v`. |
| Cor 8.2 Certified partition-of-unity synthesis | §8 | — | — | PAPER-ONLY | — | W^{1,2} instance of Thm 7.2 plus multiplier estimate (Lem 8.1). |
| Thm 9.2 Quantitative certified gluing | §9 | — | — | PAPER-ONLY | — | Local defects `Δ_j = Σ_i (1+L_i) ε_ij`. |
| Cor 9.3 Exact certified gluing | §9 | — | — | PAPER-ONLY | — | Zero-defect corollary of Thm 9.2. |
| Thm 10.2 Refinement comparison | §10 | — | — | PAPER-ONLY | — | Uses Lem 8.1. |
| Thm 10.3 Scale-sensitive partition-of-unity estimate | §10 | — | — | PAPER-ONLY | — | Babuška–Melenk classical majorant; analytic core, requires `W^{r,2}` interface. |
| Thm 10.5 Effective certified descent | §10 | — | — | PAPER-ONLY | — | Uses Thm 6.2. |
| Cor 10.6 Sobolev-order descent criterion | §10 | — | — | PAPER-ONLY | — | Requires Thm 10.3. |
| Thm 11.2 Closure calculus for CCP-admissible operations | §11 | — | — | PAPER-ONLY | — | Identities, composition, products, plus the six item-by-item citations (Def 5.1 / Thm 6.2 / Thm 7.2 / Thm 10.5). |
| Def 11.5 CCP-generated universe `CU_Σ(P)` | §11 | — | — | PAPER-ONLY | — | Formalize as an inductive typed closure family (equivalent to the intersection). |
| Thm 11.6 CCP preservation and exclusion | §11 | — | — | PAPER-ONLY | — | The generative exclusion mechanism; distinct from Thm 12.1. |
| Cor 11.8 Preservation ⇒ CCP-ban | §11 | — | — | PAPER-ONLY | — | Rephrasing of Thm 11.6 with Def 11.7. |
| Prop 11.9 Rational-step L¹ evidence presentation | §11.2 | — | `Coq/V3/Models/L1StepPresentation.v` (planned) | IN-PROGRESS | — | The concrete measure-algebra universe. |
| Lem 11.10 Indicator objects closed under L¹ limits | §11.2 | — | — | PAPER-ONLY | — | Uses fast-Cauchy subsequence trick. |
| Prop 11.11 Certified set constructors preserve measurability | §11.2 | — | — | PAPER-ONLY | — | Union / intersection / difference / rational translation are certifiably realizable 1-Lipschitz. |
| Thm 11.13 Measurability of generated set universe | §11.2 | — | — | PAPER-ONLY | — | Application of Thm 11.6 with `R_s` = indicator-valued finite-measure L¹ elements. |
| Prop 11.14 Non-primitive generated measurable set | §11.2 | — | — | PAPER-ONLY | — | Rational balls belong to `MCU_3` but are not primitive box unions. |
| Thm 11.15 Finitely additive invariant obstruction | §11.2 | — | — | PAPER-ONLY | — | `m(X) = m(Y)` under generated equidecomposition. |
| **Cor 11.16 Internal Banach–Tarski exclusion** | §11.2 | — | — | PAPER-ONLY | — | Short measure-additivity contradiction; MUST be advertised only as internal exclusion inside `MCU_3` — not as denial of the classical theorem. |
| Thm 12.1 Non-certifiability from non-injective linear information | §12 | — | `Coq/V3/NonCertifiability.v` (planned) | IN-PROGRESS | — | Distinct from the v2 metric-entropy incompressibility theorem — do not conflate the two. |
| Cor 12.2 Sampling-only obstruction | §12 | — | — | PAPER-ONLY | — | Corollary of Thm 12.1 with sampling map. |
| Thm 14.2 Extensional certified evidence is a sheaf | §14 | — | — | PAPER-ONLY | — | On a certified analytic site; requires the exact hypotheses of Def 14.1 (chosen restriction lifts, certified gluing procedure). |
| Cor 14.3 Certified Sobolev gluing gives a sheaf | §14 | — | — | PAPER-ONLY | — | Corollary of Thm 14.2 for the W^{1,2} site. |
| Cor 14.4 Extensional evidence in sheaf topos | §14 | — | — | PAPER-ONLY | — | Standard topos-theory step from Thm 14.2. |
| Prop 15.3 W^{1,2} presentation soundness / adequacy / regularity | §15 | — | `Coq/V3/Models/W12Presentation.v` (planned) | IN-PROGRESS | — | Concrete rational piecewise-polynomial 𝔓_I. |
| Prop 15.4 Effective completeness of 𝔓_I | §15 | — | — | PAPER-ONLY | — | Diagonal construction. |
| Prop 15.9 Nontrivial effective equivalence 𝔓_I ≅ 𝔏_I | §15 | — | — | PAPER-ONLY | — | Different finite languages, same extensional semantics. |
| Thm 15.10 Concrete simultaneous realization | §15 | — | — | PAPER-ONLY | — | The concrete instance activating extensional-collapse, generic-lifting, opfibration, finite-core-completion, presentation-invariance, reconstruction, quantitative-gluing, effective-descent and extensional-sheaf simultaneously. |
| Prop 16.1 Nonzero approximate-gluing computation | §16 | — | `Coq/V3/Examples/PositiveDefectGluing.v` (planned) | IN-PROGRESS | — | Explicit rational computation `‖G−x_j‖^2 = 100256/50625`, etc. Excellent formalization target. |
| Prop 16.2 Non-singleton proof-relevant fibre | §16 | — | — | PAPER-ONLY | — | Two distinct certificate systems over the same name, both with Lawvere distance 0. |
| Prop 16.3 Exact dyadic refinement for x² | §16 | — | — | PAPER-ONLY | — | `‖f−u_h‖² = h⁴/30 + h²/3`. |
| Prop 16.4 Non-finite evidence-level limit for e^x | §16 | — | — | PAPER-ONLY | — | Rational Taylor codes converge to a non-finite point. |
| Thm 16.5 Operational nontriviality | §16 | — | — | PAPER-ONLY | — | Conjunction of Prop 16.1–16.4. |

## Layer-C legacy entries (informational — NOT v3 theorems)

For completeness the following legacy v2 items are also tracked here so
that a reader who follows a citation from an old paper version can find
the current status. **None of these count toward the v3 checked list**.

| v2 identifier | module | v2 status | v3 status | notes |
| --- | --- | --- | --- | --- |
| Probes–models adjunction (v2 Thm 3.3) | `Coq/Adjunction/Adjunction.v` (excluded from CI) | asserted core-proven | **LEGACY-V2, WITHDRAWN** | v3 explicitly withdraws the probes–models adjunction as a paper theorem (Remark 5.5). |
| Internal UELAT (v2 Thm 5.1) | `Coq/Approx/UELAT_Internal.v` (excluded from CI) | asserted core-proven | **LEGACY-V2** | The analytic Bernstein content is a candidate for `CHECKED-ANALYTIC-CORE` once ported to mathcomp-analysis 1.16; the wrapper theorem name has no v3 counterpart. |
| Certificate incompressibility (v2 Thm 8.2) | `Coq/Approx/Incompressibility.v` (excluded from CI) | asserted "Fully proven" | `certificate_size_lower_bound` is `CHECKED-RESTRICTED`; wrapping file `LEGACY-V2` and excluded | The pigeonhole proof was fixed in Round 21 (`docs/BUILD_NOTES.md`), but v3's non-certifiability theorem (Thm 12.1) is a **different** theorem — do not conflate. Two sibling lemmas in the same file (`lipschitz_lower_bound`, `explicit_lower_bound`) `FAILED-AUDIT` — false statements old Coq's `lra` silently accepted. |
| Effective descent (v2 Thm 9.3) | `Coq/Approx/EffectiveDescent.v` (excluded from CI) | asserted core-proven | **LEGACY-V2** | v3 Thm 7.2 (Certified reconstruction) and Thm 10.5 (Effective certified descent) supersede this. |
| Uniform stability (v2 Thm 7.1) | `Coq/Stability/UniformStability.v` (excluded from CI) | asserted core-proven | **LEGACY-V2, IN-AUDIT** | Awaits `Print Assumptions` inspection (see `docs/LEGACY_AUDIT.md`). |
| CCP (v2 §4) | `Coq/Foundations/CCP.v` | asserted core-proven | `CHECKED-ANALYTIC-CORE` for its bounded-search / dependent-choice content; **not** a formalization of the v3 CCP-generated universe (Def 11.5 / Thm 11.6). |
| Certificate.v grammar | `Coq/Foundations/Certificate.v` | asserted core-proven | `CHECKED-ANALYTIC-CORE` for its structural `cert_wf` invariants; **not** the v3 semantic evidence interface (Def 2.1 / Def 3.1). |

## Machine-readable audit

`Print Assumptions` output for every advertised v3-checked theorem
should be committed under `docs/assumptions/<theorem>.txt` and
regenerated by CI. Nothing under that path yet, because nothing has
reached `CHECKED-EXACT`.

## Update discipline

Any commit that changes a row's status must:

1. update this file in the same commit;
2. state the new status in the commit message;
3. cite the CI run URL that supports the change.

A commit that adds a new `CHECKED-EXACT` row without a passing CI job
in the same PR is a bug.
