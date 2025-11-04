[![CI](https://github.com/ipsissima/UELAT/actions/workflows/ci.yml/badge.svg)](https://github.com/ipsissima/UELAT/actions/workflows/ci.yml)
# Certificate-Based Approximation in Sobolev Spaces

![CI](https://github.com/ipsissima/UELAT/actions/workflows/ci.yml/badge.svg)

This repository hosts the formal Coq development for certificate-driven approximation of functions in Sobolev spaces, as described in the appendices of our manuscript and in our patent-pending system. It implements fully constructive, machine-checkable algorithms for universal embedding and approximation, using local certificates, compatibility checks, and partition-of-unity gluing.

> 💡 **Goal:** Given a computable function `f` in a Sobolev space and accuracy `ε`, construct a finite certificate and a reproducible global approximant `f_ε`, with formal correctness guarantees.

---

## 🚧 Project Status

- **Initial release:** Contains all core Coq files underpinning our appendices and main results, including type definitions, certificate construction, partition-of-unity, error bounds, and explicit examples.
- **Ongoing development:** Modularization, addition of `Utils/` and `Examples/`, integration of numerical scripts and proof documents, and further expansion per our roadmap (see below).
- **Patent pending:** Key algorithmic and architectural methods in this repository are covered by U.S. Provisional Patent Application No. 63/827,358, filed June 20, 2025. See the LICENSE and “Intellectual Property” section for important details on usage.

---

## 📂 Files and Structure

**Current files:**
- `Coq/Certificate.v` – Certificate types and main definitions
- `Coq/SobolevApprox.v` – Certificate construction, partitioning, and error routines
- `Coq/PartitionOfUnity.v` – Partition-of-unity implementation and properties
- `Coq/Reconstruct.v` – Gluing certificates into global approximants
- `Coq/ErrorBound.v` – Formalization of error bounds
- `Coq/Example.v` – Explicit example: approximation of `sin(πx)` with B-splines
- `Coq/_CoqProject` – Canonical list of Coq sources used by CI and local builds
- `tests/` – Python unit tests executed by CI via `pytest`
- `Project.toml`, `src/`, `test/` – Julia project used by CI (`Pkg.test()`)

**To be added:**
Modular subfolders (`Utils/`, `Examples/`), data files, scripts for numerical extraction, formal proof PDFs, and more.

---

## 📦 Prerequisites

- Coq ≥ 8.18 recommended
- (Optional) MathComp, Coquelicot for advanced analysis
- Python 3.9+ with `pytest` for the sanity test suite under `tests/`
- Julia 1.9 or 1.10 for the lightweight project under `Project.toml`
- See each `.v` file for dependencies

---

## 🚀 Getting Started

1. Clone the repo and enter the directory:
    ```sh
    git clone https://github.com/ipsissima/UELAT.git
    cd UELAT
    ```
2. Build the Coq development (uses `Coq/_CoqProject`):
    ```sh
    bash .github/scripts/build_coq.sh
    ```
    Alternatively, `make coq` delegates to `coq_makefile` when `_CoqProject` is present.
3. Run the Python sanity tests:
    ```sh
    python -m pip install pytest
    pytest
    ```
4. Run the Julia tests (instantiates the project defined in `Project.toml`):
    ```sh
    julia --project=. -e 'using Pkg; Pkg.instantiate(); Pkg.test()'
    ```

---

## 🔁 Reproducible build

Use a local opam switch pinned to the versions enforced in CI:

```sh
opam switch create . ocaml-variants.4.14.2+options
opam install . --deps-only -y
make -C Coq -j$(nproc)
```

Continuous integration also runs these builds inside docker-coq images for Coq 8.18 and 8.19 to ensure reproducibility.

---

## 🧑‍🔬 Next Steps and Roadmap

- Modularize code (move utility functions to `Coq/Utils/`, examples to `Coq/Examples/`)
- Add formal proofs in `proofs/`
- Integrate Python scripts for certificate extraction and validation
- Add data files for quadrature and basis construction
- Document API and provide interactive demos

---

## 🛡️ Intellectual Property & License

- **Copyright © Andreu Ballús Santacana, 2025.**
- **Patent pending:**
  Some or all of the algorithms and certificate-based approximation procedures in this repository are protected under U.S. Provisional Patent Application No. 63/827,358, filed June 20, 2025 (“Universal Symbolic Approximation of Functions via Logic Fragment Assembly and Categorical Embedding”).
- **Academic and non-commercial use** is permitted under the MIT license.
- **Commercial use:** For any commercial application, integration, or licensing inquiry, contact andreuballus@gmail.com.
- See `LICENSE` for details.

---

## 📚 References

* A. Cohen, *Numerical Analysis of Wavelet Methods*, Elsevier, 2003.
* R. DeVore and G. Lorentz, *Constructive Approximation*, Springer, 1993.

---

## 🔗 Links

- [Formal appendices and manuscript](https://...)
- [Contact / Issues](mailto:andreuballus@gmail.com)
