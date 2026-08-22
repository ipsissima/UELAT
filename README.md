[![CI](https://github.com/ipsissima/UELAT/actions/workflows/ci.yml/badge.svg)](https://github.com/ipsissima/UELAT/actions/workflows/ci.yml)

# Universal Gluing and Contextual Choice

Formal artifacts accompanying:

> **Universal Gluing and Contextual Choice: Certificate-Carrying
> Approximation, Functorial Evidence, and Effective Descent.**
> Andreu Ballús Santacana. arXiv:2506.22693, version 3.

Prior arXiv versions of this preprint used two different titles:

- **v1** — *Universal Embedding and Linear Approximation Theorem*.
- **v2** — *Universal Gluing and Contextual Choice: Categorical Logic and the
  Foundations of Analytic Approximation*.

v3 supersedes both under the title above. This repository is being
restructured to correspond to v3.

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
| `docs/FORMALIZATION_STATUS.md` | v3 theorem inventory, Rocq identifier when one exists, exact status label (see vocabulary below), and known assumption footprint. |
| `docs/LEGACY_AUDIT.md` | audit of pre-v3 modules — what survives as analytic infrastructure, what is legacy, what failed a correspondence check. |
| `docs/AXIOMS_AND_ADMISSIONS.md` | dependency/status report for every `Admitted`, `Axiom`, `Parameter`, and `Hypothesis` in the tree. Assumption text is descriptive; the file makes no scientific-completeness claim. |
| `docs/BUILD_NOTES.md` | round-by-round record of the Rocq 9 migration and every discovery that changed the status of a legacy theorem. |

The status vocabulary used consistently across this repository:

- **`CHECKED-EXACT`** — Rocq **theorem** with the same statement, at
  the same strength, as the paper theorem, on a `coqchk`-clean
  dependency path in the CI-built module set, with a captured
  `Print Assumptions` audit under `docs/assumptions/`.
- **`DEFINITION-EXACT`** — Rocq **definition / record** faithfully
  modelling a paper definition. Does NOT itself count as a
  machine-checked theorem.
- **`CHECKED-RESTRICTED`** — Rocq theorem valid but with a documented
  delta from the paper theorem (extra hypothesis, narrower
  quantifier, etc.).
- **`CHECKED-ANALYTIC-CORE`** — classical analytic lemma the paper
  uses, checked in isolation from the v3 evidence-level statement.
- **`LEGACY-V2`** — v1/v2 statement no longer asserted in v3. Not a
  v3 theorem.
- **`PAPER-ONLY`** — proved in the paper, no Rocq artifact.
- **`IN-PROGRESS`** — Rocq module exists with partial correspondence;
  must NOT be advertised as checked.
- **`FAILED-AUDIT`** — earlier repository incarnation claimed this as
  checked; audit found the statement false or vacuous.

**The advertised machine-checked v3 theorem list is `CHECKED-EXACT`
only.** `DEFINITION-EXACT` says "we modelled the object faithfully";
`CHECKED-RESTRICTED` says "we proved a deltaed statement"; neither
counts as machine-checked v3 in the sense of paper §18.

## Building

The CI environment is currently specified by lower-bound constraints
in `uelat.opam`:

- OCaml ≥ 4.14.2
- rocq-prover ≥ 9.0.0 (installed via opam)
- mathcomp / mathcomp-algebra / mathcomp-analysis (unversioned;
  whatever the opam solver picks at CI time under the rocq-prover ≥
  9.0.0 constraint)
- dune ≥ 3.10.0

**These are constraints, not exact pins.** A fresh build in the future
can resolve to newer versions inside those ranges, and `opam update`
runs during CI. For paper-grade reproducibility we need an opam
lockfile (or an exact-version dependency block, or a pinned
opam-repository revision) so that this repository can truthfully
report the versions the paper was checked against, rather than
"whatever currently satisfies these constraints". Adding a lockfile is
tracked as a follow-up.

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

MIT. See the root `LICENSE` file. `uelat.opam` declares `license: "MIT"`
consistently.

## Citation

Cite the paper, not the repository. Cite the repository only for
formal artifacts that `FORMALIZATION_STATUS.md` marks as `CHECKED-EXACT`
against the current commit:

```bibtex
@misc{uelat-v3,
  title  = {Universal Gluing and Contextual Choice: Certificate-Carrying Approximation, Functorial Evidence, and Effective Descent},
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
