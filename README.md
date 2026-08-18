[![CI](https://github.com/ipsissima/UELAT/actions/workflows/ci.yml/badge.svg)](https://github.com/ipsissima/UELAT/actions/workflows/ci.yml)

# Universal Gluing and Contextual Choice

Formal artifacts accompanying:

> **Certificate-Carrying Approximation: Functorial Evidence,
> Quantitative Descent, and Generated Universes.**
> Andreu Ballús Santacana. arXiv:2506.22693, version 3.

Prior arXiv versions of this preprint were titled *Universal Embedding and
Linear Approximation Theorem*; version 3 supersedes them under the current
title. This repository is being restructured to correspond to version 3.

## Status of this repository — read before citing

This repository contains, in one tree, three logically distinct layers:

1. **Layer A — `Coq/V3/`** (new, in progress). The
   theorem-corresponding formalization of version 3 of the manuscript.
   Only the entries listed as `CHECKED-EXACT` in `FORMALIZATION_STATUS.md`
   should be treated as machine-checked v3 theorems, and each of those
   entries also cites the exact Rocq identifier.

2. **Layer B — reusable analytic cores.** Lemmas and small
   developments (Bernstein estimates, finite summation, modulus
   machinery, rational partition-of-unity data) that survive as
   infrastructure for Layer A even when the enclosing v2 wrapper
   theorem does not.

3. **Layer C — legacy v1–v2 modules** in place elsewhere under `Coq/`.
   These formalize claims from the v1–v2 programme. Version 3
   **explicitly withdraws** several of those claims — most notably the
   probes–models adjunction as stated, and the numerical material in the
   former Chebyshev / B-spline examples. Legacy modules are retained
   because portions of their proofs remain useful, but they are
   **not** to be read as formalizations of v3 theorems. See
   `docs/LEGACY_AUDIT.md`.

**A green CI build is necessary but not sufficient** for calling a
paper theorem machine-checked. Section 18 of v3 states three
requirements — clean toolchain build, correspondence to a theorem of
the same strength in the repository, and either formalization or
explicit paper-only labelling for the v3 theorem inventory. This
repository does not yet satisfy those requirements across the full v3
inventory. Do not describe the paper as machine-checked on the basis
of a green build alone.

## Authoritative correspondence table

| document | purpose |
| --- | --- |
| `docs/FORMALIZATION_STATUS.md` | v3 theorem inventory, Rocq identifier when one exists, exact status label (`CHECKED-EXACT`, `CHECKED-RESTRICTED`, `CHECKED-ANALYTIC-CORE`, `LEGACY-V2`, `PAPER-ONLY`, `IN-PROGRESS`, `FAILED-AUDIT`), and known assumption footprint. |
| `docs/LEGACY_AUDIT.md` | audit of pre-v3 modules — what survives as analytic infrastructure, what is legacy, what failed a correspondence check. |
| `docs/AXIOMS_AND_ADMISSIONS.md` | dependency/status report for every `Admitted`, `Axiom`, `Parameter`, and `Hypothesis` in the tree. Assumption text is descriptive; the file makes no scientific-completeness claim. |
| `docs/BUILD_NOTES.md` | round-by-round record of the Rocq 9 migration and every discovery that changed the status of a legacy theorem. |

## Building

The current CI environment is:

- OCaml 4.14.2
- rocq-prover ≥ 9.0.0 (installed via opam)
- mathcomp / mathcomp-analysis as pulled by the pinned `uelat.opam` deps
- dune (bundled with the ocaml/setup-ocaml action)

`.github/workflows/ci.yml` provisions the environment from a fresh
runner. To reproduce locally with opam ≥ 2.5:

```bash
opam repo add coq-released https://coq.inria.fr/opam/released
opam switch create uelat ocaml-base-compiler.4.14.2
eval "$(opam env)"
opam pin add uelat.dev . --no-action --yes
opam install . --deps-only --yes
cd Coq && coq_makefile -f _CoqProject $(grep -E '^[^#[:space:]].*\.v$' _CoqProject) -o Makefile && make -j
```

`Coq/_CoqProject` is the authoritative list of modules included in the
build. Files marked `# EXCLUDED:` are not built by CI and each carries
an inline comment stating **why** — most commonly: awaiting the mathcomp
1.16+ package reshuffle, awaiting a paper-side restatement, or awaiting
integration into the v3 skeleton.

## Verification

`coqchk` is run in CI over the included module set. See the
`coqchk (included modules)` step of `.github/workflows/ci.yml` for the
exact enumeration. Do not read a `coqchk` pass as endorsement of any
theorem beyond that enumerated set.

## License

License metadata in `uelat.opam` and this README have not yet been
reconciled with the top-level `LICENSE`. Any use of the code should
consult the file present in the repository root; the eventual reconciled
choice will be recorded in the git history under a `chore: license` commit.

## Citation

Cite the paper, not the repository. Cite the repository only for
formal artifacts that `FORMALIZATION_STATUS.md` marks as `CHECKED-EXACT`
against the current commit:

```bibtex
@misc{uelat-v3,
  title  = {Certificate-Carrying Approximation: Functorial Evidence, Quantitative Descent, and Generated Universes},
  author = {Ballús Santacana, Andreu},
  year   = {2026},
  eprint = {2506.22693},
  archivePrefix = {arXiv},
  primaryClass  = {math.FA},
  note   = {Version 3}
}
```

## Links

- [Paper (arXiv)](https://arxiv.org/abs/2506.22693)
- [Issues](https://github.com/ipsissima/UELAT/issues)
