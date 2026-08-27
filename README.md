# Proof-Carrying Analytic Approximation

[![Authoritative v3](https://github.com/ipsissima/UELAT/actions/workflows/authoritative-v3.yml/badge.svg?branch=main)](https://github.com/ipsissima/UELAT/actions/workflows/authoritative-v3.yml)
[![V3 diagnostic build](https://github.com/ipsissima/UELAT/actions/workflows/v3-fast.yml/badge.svg?branch=main)](https://github.com/ipsissima/UELAT/actions/workflows/v3-fast.yml)

Formal companion to:

> **Andreu Ballús Santacana, _Proof-Carrying Analytic Approximation: Local-to-Global Evidence Transport at Encoding Cost_.**  
> arXiv:2506.22693, version 3.

The manuscript is the controlling mathematical source. This repository makes theorem correspondence, build inclusion, kernel checking, assumptions and remaining obligations inspectable rather than inferring them from filenames or historical CI.

## Start here

| Purpose | Authoritative location |
| --- | --- |
| Reviewer audit path | [`docs/REVIEWER_GUIDE.md`](docs/REVIEWER_GUIDE.md) |
| Theorem-by-theorem status | [`docs/FORMALIZATION STATUS.md`](docs/FORMALIZATION%20STATUS.md) |
| Current-paper Rocq project | [`Coq/_CoqProject.authoritative-v3`](Coq/_CoqProject.authoritative-v3) |
| Public current-paper aggregate | [`Coq/UELATAuthoritativeV3.v`](Coq/UELATAuthoritativeV3.v) |
| Rocq tree orientation | [`Coq/README.md`](Coq/README.md) |
| Pinned verification workflow | [`.github/workflows/authoritative-v3.yml`](.github/workflows/authoritative-v3.yml) |

## Verification contract

A current-paper result is described as **machine-checked** only when its row in `docs/FORMALIZATION STATUS.md` is marked `CHECKED-EXACT` at a recorded audited commit and all of the following hold:

1. the Rocq statement matches the manuscript at the same strength;
2. the pinned authoritative project builds;
3. `coqchk` succeeds on `UELAT.UELATAuthoritativeV3`;
4. reachable assumptions have been audited at that same commit; and
5. the result is actually included in the authoritative project surface.

A green broad build, a legacy module, or a theorem checked against an older manuscript snapshot does **not** by itself satisfy this contract.

## Current-paper mathematical layers

The formalization follows the four layers of the v3 manuscript.

- **Effective linear universality.** Real computable Banach presentations, approximate norming functionals, coordinate dual-ball machinery, effective compactness interfaces and finite representation in standard `C([0,1])`.
- **Evidence boundary and chosen transport.** Strict-slack extensional collapse, finite-code realizable Lipschitz transport, chosen lifts, proof relevance and resource profiles.
- **Quantitative rational `W^{1,2}` compiler.** Exact rational meshes, partition-of-unity synthesis, local PUFEM defect transport, shared proof DAGs and encoding-cost accounting.
- **Refinement and generated semantics.** H1–H7 descent to a represented limit with `Q_target = 0`, standard-rational asymptotics, Contextual Choice, finite-measure and information/sheaf boundaries.

The repository follows the authoritative manuscript numbering. In particular:

- Proposition 6.3 uses `w_i^2 = max(C_inf^2 + 2 L_i^2, 2 C_inf^2)`;
- Proposition 7.3 is the concrete standard-local-encoding compiler bound;
- Theorem 7.4 is the main encoding-cost evidence-transport theorem under H1–H7;
- Corollary 7.5 is the standard-rational same-order regime.

## What is complete and what is not

The repository deliberately separates formal source coverage from full kernel-audited theorem completion.

The strongest remaining mathematical formalization obligations are currently concentrated in:

- the executable constructive/effective realization of Lemma 3.1 (approximate Hahn–Banach);
- completion and audit of the effective compactum → Cantor-surjection → function-space → interval-extension chain for Theorem 3.2;
- concrete `W^{1,2}` library instantiations of the standard analytic inequalities behind Theorem 5.6 and Theorem 7.2.

Other current-paper items already have substantive manuscript-matched formal sources but remain below `CHECKED-EXACT` until the authoritative build, `coqchk` and assumptions-audit contract is discharged. The exact state is maintained only in the status ledger.

## Reproduce the authoritative build

With Rocq 9.2 installed:

```sh
cd Coq
coq_makefile -f _CoqProject.authoritative-v3 -o Makefile.authoritative-v3
make -f Makefile.authoritative-v3 -j2
coqchk -R . UELAT UELAT.UELATAuthoritativeV3
```

The GitHub Actions workflow is the pinned reference environment when local package versions differ.

## Repository layers

The codebase contains three deliberately distinct strata:

1. **Authoritative v3 surface** — files included by `_CoqProject.authoritative-v3` and exposed through `UELATAuthoritativeV3.v`.
2. **Reusable v3 infrastructure** — checked or useful modules that may support the current paper but do not automatically inherit current-paper theorem status.
3. **Historical v1–v2 material** — preserved for auditability and lemma reuse; superseded claims are not part of the v3 theorem surface.

The pre-authoritative repository state is preserved at `legacy-pre-authoritative-v3-2026-08-27`.

## Historical corrections

Version 3 explicitly withdraws or supersedes the earlier probes–models adjunction, the universal finite-rank approximation-property formulation, identified incorrect Chebyshev/B-spline calculations, and broad priority claims for generic certificate stability. The repository preserves those distinctions rather than silently reusing old artifacts as current evidence.

## License

MIT. See [`LICENSE`](LICENSE).

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
