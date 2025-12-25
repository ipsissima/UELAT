# License & Patent Notice

This repository is dual-licensed:

1.  **Open Source:** Available under the **GNU Affero General Public License v3 (AGPLv3)** for academic and open-source projects.
2.  **Commercial:** For proprietary use, closed-source integration, or to use the algorithms without AGPL restrictions, you must purchase a **Commercial License**.

> *Note: The algorithms, methods, and certificate procedures in this repository are protected by U.S. Patent App. No. 63/827,358. This software is strictly for open-source use unless a commercial license is obtained.*

**Contact:** andreuballus@gmail.com

---

[![CI](https://github.com/ipsissima/UELAT/actions/workflows/ci.yml/badge.svg)](https://github.com/ipsissima/UELAT/actions/workflows/ci.yml)

# Universal Embedding and Linear Approximation Theorem (UELAT)

This repository contains the formal Coq development for the Universal Embedding and Linear Approximation Theorem (UELAT), as described in our accompanying paper.

**Paper:** [Universal Gluing and Contextual Choice: Categorical Logic and the Foundations of Analytic Approximation (arXiv:2506.22693)](https://arxiv.org/abs/2506.22693)

---

## Main Contributions

The UELAT formalization establishes five key results:

### 1. UELAT (Sections 5-6)
Internal and external formulations of universal approximation with first-class certificates. For any continuous function f and precision ε > 0, we constructively produce a finite certificate C witnessing ‖f - g_C‖ < ε.

### 2. Probes-Models Adjunction (Section 3, Theorem 3.3)
A fibered adjunction F ⊣ G between the category of finite probe theories and the category of locally finite-dimensional analytic models. This provides categorical foundations for certificate-based approximation.

### 3. Contextual Choice Principle (Section 4)
A foundational stance on witness-bearing existence, providing constructive choice for contextual predicates without requiring the full Axiom of Choice.

### 4. Certificate Incompressibility (Section 8, Theorem 8.2)
Information-theoretic lower bounds on certificate size: Ω(ε^{-d/s}) for approximating W^{s,p}([0,1]^d) functions to precision ε. This shows our certificates are essentially optimal.

### 5. Effective Descent (Section 9, Theorem 9.3)
Certificate composition under sheaf-theoretic gluing with explicit size bounds. Local certificates can be combined into global certificates with controlled overhead.

---

## Repository Structure

```
UELAT/
├── Coq/                           # Coq formalization
│   ├── UELAT.v                    # Main entry point
│   ├── _CoqProject                # Build configuration
│   │
│   ├── Foundations/               # Core definitions
│   │   ├── Certificate.v          # Certificate type grammar (Appendix A)
│   │   ├── ProbeTheory.v          # Probe category (Section 3.2)
│   │   └── CCP.v                  # Contextual Choice Principle (Section 4)
│   │
│   ├── Adjunction/                # Probes-Models adjunction
│   │   ├── Probe.v                # Category Probe
│   │   ├── Model.v                # Category Model
│   │   ├── Functors.v             # F and G functors
│   │   ├── Adjunction.v           # Main theorem (Theorem 3.3)
│   │   └── Reflection.v           # Reflection principle (Theorem 3.7)
│   │
│   ├── Approx/                    # Approximation theory
│   │   ├── Bernstein.v            # Bernstein polynomials
│   │   ├── Bernstein_Lipschitz.v  # Main Lipschitz bound (fully proven)
│   │   ├── UELAT_Internal.v       # Internal UELAT (Theorem 5.1)
│   │   ├── UELAT_External.v       # External version (Section 6)
│   │   ├── Incompressibility.v    # Lower bounds (Theorem 8.2)
│   │   └── EffectiveDescent.v     # Descent theorem (Theorem 9.3)
│   │
│   ├── Stability/                 # Stability theory
│   │   ├── Modulus.v              # Modulus of continuity
│   │   ├── UniformStability.v     # Theorem 7.1
│   │   └── CertificateComposition.v
│   │
│   ├── Examples/                  # Concrete examples
│   │   ├── ExpCert.v              # exp(x) certificate
│   │   ├── FourierCert.v          # Fourier series (Appendix C)
│   │   ├── ChebyshevCert.v        # Chebyshev polynomials (Verified & Optimized)
│   │   └── SobolevCert.v          # Sobolev space examples
│   │
│   └── Util/                      # Utility lemmas
│       ├── Reals_ext.v            # Real number extensions
│       ├── Summation.v            # Finite summation
│       └── Entropy.v              # Metric entropy
│
├── .github/workflows/ci.yml       # CI configuration
├── LICENSE                        # AGPLv3 License
└── README.md                      # This file
```

---

## Building

### Prerequisites

- **Coq** >= 8.18 (tested with 8.18, 8.19)
- **MathComp** (ssreflect, algebra, analysis)
- **Coquelicot** for real analysis

### Using opam (recommended)

```bash
# Create local switch
opam switch create . ocaml-base-compiler.4.14.2
opam install . --deps-only -y

# Build
make -C Coq -j$(nproc)
```

### Using the build script

```bash
bash .github/scripts/build_coq.sh
```

## Verification

Check the compiled development:

```bash
coqchk -R Coq UELAT UELAT
```

---

## Key Theorems

| Theorem | Module | Status |
|---------|--------|--------|
| Bernstein Lipschitz bound | `Approx/Bernstein_Lipschitz.v` | Fully proven |
| Chebyshev Certification | `Examples/ChebyshevCert.v` | Fully proven |
| Internal UELAT (5.1) | `Approx/UELAT_Internal.v` | Core proven |
| Probes-Models Adjunction (3.3) | `Adjunction/Adjunction.v` | Core proven |
| Certificate Stability (7.1) | `Stability/UniformStability.v` | Core proven |
| Incompressibility (8.2) | `Approx/Incompressibility.v` | Fully proven |
| Effective Descent (9.3) | `Approx/EffectiveDescent.v` | Core proven |

---

## Development Notes

### Constructive Island

The directories `Coq/Util/`, `Coq/Approx/`, and `Examples/ChebyshevCert.v` form a constructive island with no `Admitted` or unjustified `Axiom` declarations. This is enforced by CI.

### Proof Status

- Files in `Foundations/`, `Adjunction/`, `Approx/`, and `Stability/` contain the main development
- The Chebyshev approximation layer and Information Theoretic lower bounds are now fully verified
- Some advanced pedagogical examples in `Examples/` (e.g., Sobolev) may still use `Admitted` as placeholders

### Style

- Uses MathComp/ssreflect tactics where available
- Module system for namespace isolation
- Comments reference paper section numbers

---

## Citation

If you use this formalization, please cite:

```bibtex
@misc{uelat2025,
  title={Universal Gluing and Contextual Choice: Categorical Logic and the Foundations of Analytic Approximation},
  author={Ballus Santacana, Andreu},
  year={2025},
  eprint={2506.22693},
  archivePrefix={arXiv},
  primaryClass={math.FA}
}
```

---

## Legal

### Copyright

Copyright (c) Andreu Ballus Santacana, 2025.

### Patent Notice

Some or all of the algorithms and certificate-based approximation procedures in this repository are protected under U.S. Provisional Patent Application No. 63/827,358, filed June 20, 2025:

**"Universal Symbolic Approximation of Functions via Logic Fragment Assembly and Categorical Embedding"**

### License

- **Open Source:** This project is licensed under the GNU Affero General Public License v3 (AGPLv3).
- **Commercial Use:** Commercial use, integration, or modification without the open-source requirements of AGPLv3 requires a separate commercial license.

For licensing inquiries, contact: andreuballus@gmail.com

See `LICENSE` for full details.

---

## References

1. A. Cohen, *Numerical Analysis of Wavelet Methods*, Elsevier, 2003.
2. R. DeVore and G. Lorentz, *Constructive Approximation*, Springer, 1993.

---

## Links

- [Paper (arXiv)](https://arxiv.org/abs/2506.22693)
- [Issues](https://github.com/ipsissima/UELAT/issues)
- [Contact](mailto:andreuballus@gmail.com)
