[![CI](https://github.com/ipsissima/UELAT/actions/workflows/ci.yml/badge.svg)](https://github.com/ipsissima/UELAT/actions/workflows/ci.yml)

# Proof-Carrying Analytic Approximation

Formal artifacts accompanying the authoritative version 3 manuscript:

> **Andreu Ballús Santacana, _Proof-Carrying Analytic Approximation: Local-to-Global Evidence Transport at Encoding Cost_.**  
> arXiv:2506.22693, version 3.

The manuscript is the controlling mathematical source. The pre-migration repository state is preserved at `legacy-pre-authoritative-v3-2026-08-27`.

## Current architecture

The repository now distinguishes three layers.

1. **Authoritative-v3 formalization.** Current-paper theorem statements and manuscript-facing wrappers. The target theorem graph follows Sections 2–9 of the authoritative paper: represented Banach presentations and strict-slack evidence, UELAT as effective linear Banach–Mazur universality, chosen proof-relevant evidence transport, exact rational `W^{1,2}` reconstruction, one-cover provenance compilation, proof-carrying refinement at encoding cost, Contextual Choice, and the information/sheaf boundary results.
2. **Previously checked v3 core.** The existing modules in `Coq/V3/` such as `Presentation.v`, `EvidenceSyntax.v`, `Evidence.v`, `MetricReflection.v`, `RealizableMap.v`, `GenericLift.v`, `Composition.v`, and `EffectiveCompleteness.v` were checked against an earlier v3 manuscript snapshot. They are retained as reusable checked infrastructure, but do **not** automatically count as `CHECKED-EXACT` for the authoritative manuscript.
3. **Legacy v1–v2 material.** Historical modules elsewhere under `Coq/` remain for auditability and lemma reuse. The old probes–models adjunction, finite-rank universal-approximation formulation, and superseded numerical material are not part of the current theorem surface.

## The current paper's four mathematical layers

The authoritative manuscript separates four claims:

- **Effective linear universality.** Every real computable Banach presentation admits a uniformly computable linear isometric embedding into standard computable `C([0,1])`, with computable inverse on the represented range; finite rational polygonal/hat codes then give a common pointwise finite representation language.
- **Evidence boundary.** Complete strict-slack metric evidence collapses extensionally once full effective names are available, while selected evidence transformers, construction history, proof size, verification work, and source use remain proof-relevant.
- **Quantitative `W^{1,2}` compiler.** Supplied local approximation and overlap witnesses are transported through exact rational partition-of-unity synthesis and geometric refinement to a represented limit with `Q_target = 0` and retained genealogy of the same asymptotic bit order as the finest declared conventional encoding.
- **Contextual Choice.** Certified constructions form the least generated genealogical closure under declared admissible constructors; invariant preservation gives internal exclusion results, while exact extensional gluing remains ordinary sheaf semantics.

## Authoritative theorem numbering

The repository follows the manuscript numbering exactly. In particular:

- Proposition 6.3 uses
  `w_i^2 = max(C_inf^2 + 2 L_i^2, 2 C_inf^2)`.
- Proposition 7.3 is the concrete compiler bound for standard local encodings.
- Theorem 7.4 is the main encoding-cost evidence-transport theorem under H1--H7.
- Corollary 7.5 is the standard-rational same-order regime.

The former manuscript-facing `Theorem73Manuscript` name is therefore historical and is being replaced by an exact `Theorem74Manuscript` surface.

## Formalization status rule

The paper's Section 12 is controlling. The authoritative correspondence table is:

`docs/FORMALIZATION STATUS.md`

A paper result may be described as **machine-checked** only when that table marks the exact current-paper result `CHECKED-EXACT` at a recorded audited commit and all of the following hold:

1. a reproducible pinned Rocq/Coq toolchain builds the declared current-paper surface;
2. the formal statement has the same hypotheses and conclusion as the manuscript result;
3. `coqchk` succeeds on the public entry point; and
4. reachable assumptions are audited at that same commit.

A green repository-wide build, a legacy module, or an artifact targeting an older manuscript snapshot is not by itself evidence that a current theorem is machine-checked.

## Current migration status

The larger reconstruction developed in `andreu-toposcircuitry/UELAT` is being consolidated here because this is the canonical public repository cited by the manuscript. The migration preserves the earlier checked core and imports the newer manuscript machinery rather than replacing one with the other.

Substantive remaining mathematics is concentrated in:

- a concrete constructive/effective implementation of Lemma 3.1 (approximate Hahn–Banach);
- the full effective compactum/Cantor/function-space realization required for Theorem 3.2;
- concrete `W^{1,2}` library instantiations of the standard analytic inequalities behind Theorem 5.6 and Theorem 7.2.

The conditional H1--H7 descent/resource theorem is a separate formal target and should not be conflated with those analytic instantiations.

## Building and verification

The existing Rocq-9 build infrastructure remains in place during migration. The canonical current-paper build surface will be narrowed to the authoritative entry point and audited before any new `CHECKED-EXACT` labels are assigned.

Do not infer current-paper verification status from old CI badges alone; consult `docs/FORMALIZATION STATUS.md`.

## License

MIT. See `LICENSE`.

## Citation

```bibtex
@misc{ballus2026proofcarrying,
  title         = {Proof-Carrying Analytic Approximation: Local-to-Global Evidence Transport at Encoding Cost},
  author        = {Ballús Santacana, Andreu},
  year          = {2026},
  eprint        = {2506.22693},
  archivePrefix = {arXiv},
  note          = {Version 3}
}
```
