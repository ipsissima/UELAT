# LEGACY_AUDIT.md — audit of pre-v3 modules

This document records what happens to each pre-v3 module under the v3
correspondence audit. It is **not** a promise that these modules will
be deleted; it is a promise that this repository will not misrepresent
them.

Every conclusion here is intended to feed one row of
`docs/FORMALIZATION_STATUS.md`. When an audit conclusion changes, both
files must be updated in the same commit.

## Method

For each legacy module the audit asks the questions from section 9 of
the project brief:

1. What is the exact Rocq type of the advertised main theorem?
2. What are its `Print Assumptions`?
3. What mathematical statement does that type actually make?
4. Does it correspond to a v3 theorem, and at what strength?
5. Is the proof non-vacuous — does its `Proof` actually establish the
   `Type`?
6. Are any hypotheses inconsistent or strong enough to trivialize the
   conclusion?
7. Does a "certificate" object carry semantic content or only
   structural well-formedness?
8. Is a claimed analytic bound actually encoded in the checker /
   evidence relation, or only announced in a nearby comment?

`Print Assumptions` capture is deferred until a module is included in
the CI build (many currently are not). Where a live `Print
Assumptions` reading is not yet available, the "assumptions" column
records the static evidence: `From … Require Import` lines, in-file
`Axiom`/`Parameter`/`Hypothesis` declarations, and any `Admitted`
whose lemma is on a dependency path.

Statuses use the labels defined in `docs/FORMALIZATION_STATUS.md`.

## Module-by-module

### `Coq/Adjunction/Adjunction.v` (excluded from CI)

- Claim in v1–v2: probes–models fibred adjunction `F ⊣ G`.
- v3 status: **withdrawn as a paper theorem** — v3 Remark 5.5 says
  "no probes–models adjunction is asserted here; the categorical
  statement is the one supported by the declared evidence interfaces
  (Def 5.4, Thm 5.6 opfibration)".
- Audit conclusion: **LEGACY-V2, WITHDRAWN**. Do not advertise as a
  v3 theorem. May remain in the tree as legacy formal work; the file
  header should carry an explicit legacy notice.
- Follow-up: add module-level warning; do not port to `Coq/V3/`.

### `Coq/Adjunction/Probe.v`, `Coq/Adjunction/Model.v` (in CI)

- Currently included in the build. Contain a categorical infrastructure
  (Probe / Model records, morphisms, identity, composition) plus
  supporting universal-property lemmas.
- `probe_coprod_univ` is `Admitted` (see `docs/AXIOMS_AND_ADMISSIONS.md`).
- Audit conclusion: **LEGACY-V2** structural infrastructure that
  contains no v3 theorem. Retain, but v3's categorical vehicle is
  `CAn↑` / evidence functors (Def 5.4, Thm 5.6), not these categories.

### `Coq/Adjunction/Functors.v`, `Adjunction/Reflection.v` (excluded)

- Depend on `find_index` axioms and on several `nth 0` sites that need
  per-line fixes for Rocq 9 (see `docs/BUILD_NOTES.md`).
- Audit conclusion: **LEGACY-V2**. Reserving effort for `Coq/V3/`
  ahead of any Rocq-9 restoration.

### `Coq/Approx/UELAT_Internal.v`, `UELAT_External.v` (excluded)

- v2 "main UELAT theorem" and external variant.
- Audit conclusion pending: the wrapper theorem name has no v3
  counterpart. The Bernstein-Lipschitz analytic estimate that these
  files depend on is a genuine analytic core suitable for
  `CHECKED-ANALYTIC-CORE`, once ported past the mathcomp-analysis
  1.16 reshuffle. Wrapper: **LEGACY-V2**. Analytic core:
  **IN-PROGRESS**.

### `Coq/Approx/Bernstein.v` (in CI), `Coq/Approx/Bernstein_Lipschitz.v` (excluded)

- Standard Bernstein-polynomial approximation of continuous functions.
- Audit conclusion: **CHECKED-ANALYTIC-CORE candidate**. `Bernstein.v`
  is currently in the green build; `Bernstein_Lipschitz.v` needs the
  mathcomp-analysis 1.16 port (`reals` split into
  `rocq-mathcomp-reals`, `binom` lemma renames). These are ingredients
  of v3 Thm 10.3 (Babuška–Melenk style scale-sensitive estimate) only
  in the sense that "an r-th order local approximation estimate is
  needed"; the exact partition-of-unity majorant of Thm 10.3 is not
  in these files.

### `Coq/Approx/Incompressibility.v` (excluded)

- v2 Thm 8.2 (metric-entropy certificate lower bound).
- Round-21 audit (see `docs/BUILD_NOTES.md`) rewrote the pigeonhole
  proof of `certificate_size_lower_bound` with a real argument;
  the theorem is now genuinely proved.
- **But**: the same file contains `lipschitz_lower_bound` and
  `explicit_lower_bound` whose statements are **false as written**
  (small L / large ε makes the hypothesis vacuous while forcing the
  conclusion's constant to be non-positive). Old Coq's `lra`
  accepted these silently because the file was never built.
- Audit conclusion: `certificate_size_lower_bound` is
  **CHECKED-RESTRICTED** as a metric-entropy statement — it is not a
  formalization of v3 Thm 12.1 (non-certifiability from non-injective
  linear information). Two sibling lemmas: **FAILED-AUDIT**. Whole
  file: **LEGACY-V2**, remains excluded until restatement. Do not
  cite v2 Thm 8.2 in support of v3 Thm 12.1.

### `Coq/Approx/EffectiveDescent.v` (excluded)

- v2 Thm 9.3 (syntactic `GlueCert` composition with size and error
  arithmetic).
- v3 replaces this with two logically distinct theorems: Thm 7.2
  (certified reconstruction, with proof-transport interfaces `Γ_Σ`,
  `Γ_R`), and Thm 10.5 (effective certified descent). Neither is
  the v2 syntactic gluing statement.
- Audit conclusion: **LEGACY-V2**. The certificate grammar and
  size/error arithmetic remain as infrastructure (`CHECKED-ANALYTIC-CORE`
  candidate) once dust settles.

### `Coq/Foundations/Certificate.v` (in CI)

- Structural inductive grammar with a `cert_wf` predicate that checks
  well-formedness (arities, list-length compatibility of `GlueCert`
  arguments, etc.).
- Audit conclusion: **CHECKED-ANALYTIC-CORE candidate** — for its
  structural claims. **NOT a formalization of the v3 semantic
  certificate interface** (Def 2.1 / Def 3.1). `cert_wf` checks
  syntactic well-formedness; it does not check `AppCheck` /
  `DistCheck` soundness against a decoded analytic point. Rename
  candidate: `Coq/LegacyV2/CertificateGrammar.v` when v3 modules
  land, to prevent name collision with a future
  `Coq/V3/Certificate.v`.

### `Coq/Foundations/CCP.v` (in CI)

- Contains dependent-witness existence, bounded search, modulus-based
  choice, effective existence, countable/dependent choice.
- Audit conclusion: **CHECKED-ANALYTIC-CORE candidate** for its
  bounded-search / dependent-choice content. **NOT the v3 CCP
  generated-universe (Def 11.5) or preservation theorem (Thm 11.6).**
  v3 CCP is a typed inductive closure family under a declared
  signature of admissible constructors; the current file's exports
  are choice-like tools, not that closure family.

### `Coq/Foundations/ProbeTheory.v` (in CI)

- Probe categorical / combinatorial helpers.
- Audit conclusion: **LEGACY-V2** infrastructure.

### `Coq/Stability/UniformStability.v` (excluded)

- v2 Thm 7.1.
- Pre-existing suspicion (v3 brief section 1, item I): the proof may
  use a Cauchy modulus at ε/4 after choosing an index based only on
  ε/2 without an explicit monotonicity/majorization property, in
  which case `lia` cannot in fact discharge the arithmetic step.
- Audit conclusion: **IN-AUDIT** — needs an explicit
  `Print Assumptions` and hand check. Currently excluded from CI on
  the `Qreals.Q2R` Rocq-9 path issue, which happens to keep the audit
  pending as well.

### `Coq/Stability/Modulus.v` (in CI)

- Modulus-of-continuity records and helpers.
- Audit conclusion: **CHECKED-ANALYTIC-CORE**. Genuine reusable
  infrastructure for any v3 module that talks about moduli of
  continuity. No v3 wrapper theorem lives here.

### `Coq/Stability/CertificateComposition.v` (excluded)

- `cert_parallel_error` states an unconditional equality
  `cert_error (cert_parallel C1 C2) = Rmax (cert_error C1) (cert_error C2)`
  that is false without a `cert_wf`/positivity hypothesis on `C2`
  (`Rmax (cert_error C2) 0 = cert_error C2` requires `cert_error C2 ≥ 0`).
- Audit conclusion: **FAILED-AUDIT** on `cert_parallel_error` as
  currently stated; file stays excluded until restated with the
  needed hypothesis. Other lemmas in the file are unaudited.

### `Coq/Util/Reals_ext.v`, `Coq/Util/Summation.v`, `Coq/Util/Modulus.v` (in CI)

- Small analytic-infrastructure files.
- Audit conclusion: **CHECKED-ANALYTIC-CORE**. Retain as-is; these
  will very likely feed the concrete `Coq/V3/Models/W12Presentation.v`.

### `Coq/Util/Entropy.v` (excluded)

- Contains `entropy_to_discrete_pigeonhole` and `packing_le_covering`
  as `Admitted` lemmas (per `docs/AXIOMS_AND_ADMISSIONS.md`), used
  only for the (v2) incompressibility exposition.
- Audit conclusion: **LEGACY-V2**. Nothing here is a v3 theorem, and
  its main dependency (Incompressibility) is itself legacy.

### `Coq/PartitionOfUnity.v` (in CI as of Round 22)

- Analytic partition-of-unity infrastructure with a normalization
  lemma `partition_sums_to_one`.
- Audit conclusion: **CHECKED-ANALYTIC-CORE**. Small, self-contained;
  can feed `Coq/V3/Reconstruction.v` and W^{1,2} model modules.

### `Coq/Examples/*` (all excluded)

- `ChebyshevProof.v`, `ChebyshevCert.v`, `FourierCert.v`, `SobolevCert.v`,
  `ExpCert.v`. v3 explicitly withdraws the erroneous numerical
  material from the former Chebyshev and B-spline examples
  (Revision notice, item (i)).
- Audit conclusion: **LEGACY-V2** wholesale; individual lemmas
  reachable for reuse but the "example proves the paper claim"
  framing does not carry over. v3's concrete instances live in
  §15–§16 and belong under `Coq/V3/Models/` and `Coq/V3/Examples/`.

### `Coq/Reconstruct.v`, `Coq/SobolevApprox.v`, `Coq/ErrorBound.v`, `Coq/Example.v`, `Coq/Certificate.v` (root — all excluded)

- Legacy top-level modules with various Rocq-9 breakages.
- Audit conclusion: **LEGACY-V2**. To be relocated under
  `Coq/LegacyV2/` in a later chore commit; kept in place for now to
  avoid disturbing the include list.

## What this audit does NOT say

- It does not say any of these modules are wrong (except where
  `FAILED-AUDIT` is explicit).
- It does not say they will be deleted.
- It does not say the analytic content is worthless — much of it will
  be reused as `CHECKED-ANALYTIC-CORE`.

It says: **do not read the presence of these files as evidence that
v3 is machine-checked.**
