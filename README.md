[![CI](https://github.com/ipsissima/UELAT/actions/workflows/ci.yml/badge.svg)](https://github.com/ipsissima/UELAT/actions/workflows/ci.yml)

# Proof-Carrying Analytic Approximation

Formal artifacts accompanying the authoritative version 3 of:

> **Proof-Carrying Analytic Approximation: Local-to-Global Evidence Transport at Encoding Cost**  
> Andreu Ballús Santacana. arXiv:2506.22693, version 3.

This title, theorem numbering, hypotheses, caveats, and Section 12 formalization policy are the controlling manuscript contract for this repository. Earlier v3 draft titles and theorem numbers are historical snapshots only.

## Current repository policy

The public repository named by the paper is **`ipsissima/UELAT`**. The pre-migration state of `main` is preserved on `legacy-pre-authoritative-v3-2026-08-27`. The active reconstruction is staged on `authoritative-v3-final` until the current-manuscript build and assumption audit pass.

The repository contains three kinds of material:

1. **Current-manuscript formalization.** Files explicitly listed in `docs/FORMALIZATION_STATUS.md` against the present 35-page manuscript.
2. **Reusable analytic/formal infrastructure.** Correct lemmas and definitions that may support the current formalization without themselves constituting a current paper theorem.
3. **Legacy v1/v2 and superseded-v3 artifacts.** Retained for auditability but not evidence for current claims.

The old probes–models adjunction, old universal finite-rank approximation formulation, incorrect Chebyshev/B-spline calculations, and generic certificate-stability priority claims are not current v3 theorems.

## What the authoritative v3 proves

The paper separates four layers.

- **Universal effective linear representation.** Every real computable Banach presentation admits a uniformly computable linear isometric embedding into standard computable `C([0,1])`, with computable inverse on its represented range. Corollary 3.4 gives finite rational polygonal/hat representation of individual embedded points. This is not an approximation-property or finite-rank-identity theorem.
- **Finite evidence and proof relevance.** Strict-slack complete metric evidence collapses extensionally under full name access, while selected evidence transformers, derivations, proof size, source use, and transport resources remain intensional. The finite-code Lipschitz grammar has canonical evidence-local transport.
- **Quantitative rational `W^{1,2}(0,1)` transport.** Supplied local approximation and overlap evidence is compiled through exact rational partition-of-unity synthesis and geometric refinement into a represented limit with a shared proof DAG. Under the paper's H1–H7 hypotheses, complete genealogy through the precision-relevant level has size `O(B_{m(epsilon)})` and `Q_target = 0`.
- **Contextual Choice.** CCP is an operational generated-closure discipline for declared certified primitives and constructors. Its exclusion results are internal to that generated universe; no ambient classical non-existence claim follows.

## Current exact-numbering targets

The manuscript-facing headline targets are:

- Proposition 2.5 — canonical slack certification;
- Theorem 2.8 — conditional extensional collapse;
- Lemma 3.1 — effective approximate Hahn–Banach;
- Theorem 3.2 — effective linear Banach–Mazur universality;
- Theorem 4.2 — qualitative local-transport saturation;
- Proposition 4.6 — non-faithfulness;
- Proposition 4.7 — Grothendieck organization;
- Theorem 5.6 — certified localized PUFEM defect;
- Theorem 6.2 — single-cover provenance compiler;
- Proposition 6.3 — weighted global approximation budget, with
  `w_i^2 = max(C_inf^2 + 2 L_i^2, 2 C_inf^2)`;
- Proposition 6.4 — global rational-code size;
- Theorem 7.2 — classical scale-sensitive PUFEM estimate;
- Proposition 7.3 — concrete compiler bound for standard local encodings;
- **Theorem 7.4 — encoding-cost evidence transport under Sobolev refinement**;
- Corollary 7.5 — same-order transport in the standard rational regime;
- Theorem 8.5 — invariant preservation;
- Corollary 8.6 — internal finite-measure boundary;
- Proposition 9.1 — fibre indistinguishability;
- Proposition 9.2 — extensional sheaf placement.

Earlier repository names such as `Theorem73Manuscript` are superseded by the authoritative numbering and must not be cited as current correspondence without an explicit mapping.

## Formalization-status rule

`docs/FORMALIZATION_STATUS.md` is authoritative, exactly as stated in manuscript Section 12. A current paper result may be called **machine-checked** only if that table marks it `CHECKED-EXACT` for this manuscript title and theorem number at a recorded commit, and all of the following hold:

1. the Rocq statement has the same strength as the manuscript statement;
2. the pinned current build succeeds;
3. `coqchk` succeeds on the declared current entry point; and
4. reachable assumptions have been audited at that exact commit.

Repository-wide CI, legacy modules, or correspondence to an earlier manuscript snapshot do not establish a current theorem. During the authoritative migration, rows are deliberately conservative and may be downgraded until a fresh current-manuscript audit has run.

## Build surfaces

The existing Rocq-9 migration/audit infrastructure is retained. The authoritative branch adds a current-manuscript build surface rather than treating legacy modules as dependencies of v3 claims. See:

- `docs/FORMALIZATION_STATUS.md` — theorem-by-theorem correspondence;
- `docs/AXIOMS_AND_ADMISSIONS.md` — assumption/admission audit;
- `docs/LEGACY_AUDIT.md` — historical artifacts;
- `docs/BUILD_NOTES.md` — toolchain/build history.

## Citation

```bibtex
@misc{ballus2026proofcarrying,
  title        = {Proof-Carrying Analytic Approximation: Local-to-Global Evidence Transport at Encoding Cost},
  author       = {Ballús Santacana, Andreu},
  year         = {2026},
  eprint       = {2506.22693},
  archivePrefix= {arXiv},
  note         = {Version 3}
}
```

## Links

- [Paper (arXiv)](https://arxiv.org/abs/2506.22693)
- [Issues](https://github.com/ipsissima/UELAT/issues)
