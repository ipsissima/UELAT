# Theorems 5.6 and 7.2 — formalization boundary (working branch)

Governing manuscript: arXiv:2506.22693 v3, **Proof-Carrying Analytic Approximation**.

This note describes a **candidate, unverified** formal development on the PR #42 branch. It **does not** promote either manuscript theorem to `CHECKED-EXACT`. Authoritative status remains **PARTIAL**.

## Constructed candidates

- `PUFEMPointwiseCore.v`: finite Cauchy–Schwarz, square-multiplier and product-term bounds, active support rather than an incorrectly capped full neighbour list, and finite positive quadrature.
- `PUFEMIntegralBridge.v`: local-to-global energy inequality using an explicit positive linear integral; a discrete weighted-sample instance is built with no assumed integral laws.
- `PUFEMScaleBridge.v`: square-error global scale estimate derived from the previous result and **stated** local rate bounds. It proves the abstract one-order loss and a norm consequence under an explicit constant.
- `PUFEMLimitBridge.v`: epsilon proof that finite quadrature inequalities pass to real-number limits whenever both sides converge.
- `RationalPolynomialSemantic.v`: pointwise semantics of the *actual* rational polynomial addition/multiplication compiler, coefficient Leibniz identity, and additivity/homogeneity of its exact polynomial antiderivative evaluator.
- `RationalHatProductSemantic.v`: exact affine rational hat polynomial realizations and their code-level Leibniz/product identities on a rational cell.
- `RationalRealPolynomialSemantics.v`: the concrete Horner interpretation in real-valued polynomials, its compatibility with rational evaluation, and multiplicativity of interpreted rational codes.
- `ConcretePolynomialSobolev.v`: a candidate proof that the real function denoted by each rational polynomial is differentiable with derivative computed by `qpoly_deriv`; constructs an **actual** Stdlib `RiemannInt` for its squared value-and-derivative energy and shows nonnegativity.
- `ConcretePolynomialFTC.v`: constructs a concrete Stdlib `C1_fun` from each polynomial code and invokes the verified fundamental theorem of calculus to integrate the encoded real derivative on arbitrary ordered real intervals.
- `ConcretePiecewiseSobolev.v`: constructs actual Riemann energy on every **positive rational cell** and its finite sum for every `RationalPiecewiseCode`; proves seam endpoint/value matching over real numbers from the existing `Qeq` certificates.
- `ConcreteRiemannPUFEM56.v`: derives the local-to-global bound using Stdlib's actual monotonicity of real Riemann integrals, conditional on integrability of the piecewise composite integrands and certified active overlap; unlike earlier generic `PositiveLinearIntegral`, this is **a real continuous-integral statement**.
- `ConcretePolynomialWeakTest.v`: candidate proof of exact real Riemann integration-by-parts and the polynomial-test weak-derivative identity, via the C1 product and library FTC.
- `ConcretePiecewiseWeakTest.v`: sums actual cell Riemann integrals and cancels interior boundary terms using the rational seam certificates; proves a weak-derivative identity for rational polynomial test functions zero at the domain endpoints. **This is not yet a distributional weak derivative theorem for all test functions.**
- `tests/test_piecewise_weak_derivative_exact.py`: 1,600 deterministic, exact-Fraction polynomial-chain regression examples for integration by parts and boundary cancellation (not a proof).

Every result above requires successful compilation with Rocq 9.2, `coqchk`, and a theorem-specific assumptions audit at one immutable SHA. See `.github/workflows/pufem-pointwise.yml`.

## Exact remaining obligations: continuous 5.6

1. Identify the rational piecewise-polynomial and hat-code syntax with **actual functions** in (W^{1,2}(0,1)), not merely an abstract metric presentation.
2. Prove the *weak derivative* product rule for the actual functions (piecewise polynomial instances suffice initially), and that gluing preserves the relevant function-space membership.
3. Construct an actual continuous positive integral with finite-sum linearity and monotonicity; identify the integrated component terms with Sobolev squared norms.
4. Establish that positive quadratures of the appropriate concrete integrands converge to those same integrals, or use a separately verified continuous integral instance.
5. Check the manuscript's exact coefficients and `R_j` decomposition against the actual finite-code compiler and checker acceptance.
6. Integrate the final concrete theorem into `UELATAuthoritativeV3.v` *after* successfully auditing the complete build.

## Exact remaining obligations: continuous 7.2

1. Instantiate the local approximation estimates for the actual (W^{1,2}) rational-code approximants; they are currently **hypotheses** in the scale bridge.
2. Derive the partition multiplier bound (|chi_i'|_infty le C_chi h^{-1}) from the certified rational hat code and prove the pointwise support overlap count.
3. Identify squared scales `h_r`, `h_alpha`, `h_inv` with powers of a positive mesh size (h); transport the squared rate to the genuine norm (h^{r-1}) and the manuscript constant regime.
4. Check any required **effective** certificate synthesis and resource clauses independently; the pointwise/limit bridge says nothing about verification complexity.

## CI limitations and claim policy

- The legacy/general v3 pipeline currently has unrelated failing modules; the isolated PUFEM gate is designed to show **which** candidate file first fails.
- No `Admitted` or `Axiom` is intentionally introduced in these thirteen new Rocq files. This is a source-level claim pending build and kernel verification.
- Finite numerical smoke tests are useful to detect coefficient mistakes but do not prove theorem correctness.
- `Print Assumptions` reporting **Closed under the global context** does **not** discharge hypotheses explicitly quantified in a theorem. Exact theorem-type comparison against the manuscript is always required.

## Current exact boundary / dependency graph (nonpromotable pending kernel)

```text
RationalSobolev.v (finite rational syntax)
   +-- RationalPolynomialSemantic.v (Qeq algebra and exact Q integrals)
   |      +-- RationalHatProductSemantic.v
   +-- RationalRealPolynomialSemantics.v (real-valued Horner semantics)
PUFEMPointwiseCore.v (finite CS, derivative/multiplier square bounds)
   +-- PUFEMIntegralBridge.v (positive integral + finite concrete instance)
   |      +-- PUFEMScaleBridge.v (7.2, conditional on local rate data)
   +-- PUFEMLimitBridge.v (epsilon passage to a continuous limit)
```

Crucial missing arrows: the rational hat code to an actual Sobolev
weak-derivative carrier; the continuous integral realization and
norm-identity; genuine approximation-rate hypotheses for the local
rational approximants; effective certificate/checker linkage; and
successful Rocq 9.2 compilation, `coqchk`, and assumption reporting.

CI status must be read from the **latest SHA on PR #42**, not old
unrelated green jobs. `CHECKED-EXACT` is forbidden until every relevant
theorem, including the real analytic instantiation, passes that
complete audit.

## Continuous-domain progress, precise proof boundary (10 October 2026)

The new real-analysis modules now contain **candidate** definitions and
theorems for the *polynomial subspace* of `W^{1,2}(0,1)`: real-valued Horner
functions, derivatives, continuous Riemann energies on genuine rational
intervals, finite piece-chain energies, and boundary cancellation in the
weak test pairing.

Those are mathematically more concrete than the original analytic
interfaces. The following statements are **not yet established in Rocq**:

1. **Full weak derivative:** the polynomial-test integration-by-parts
   identity must be extended from rational polynomials vanishing at
   endpoints to all smooth compactly supported real tests. Density
   and/or distributional integration-by-parts on piecewise `C1`
   carriers requires its own checked lemma.
2. **Exact metric identification:** show that the real Riemann cell
   energies are precisely the `Q2R` images of the rational polynomial
   integration operations in `RationalSobolev.v`. This uses the
   antiderivative and fundamental theorem but is not yet proved.
3. **Unit interval coverage:** a `RationalPiecewiseCode` currently
   contains a nonempty continuous chain of positive cells but does not
   itself certify that its first left endpoint is exactly 0 and its
   last right endpoint is exactly 1. Add an explicit unit-domain
   certificate and verify coverage before calling this the whole
   `W^{1,2}(0,1)` coding language.
4. **Density/completion:** prove that the concrete finite-code
   carrier is dense in the represented full Sobolev space and that its
   exact coded distances agree with the desired metric presentation.
5. **5.6 compiler correspondence:** show actual rational PUFEM/hat
   synthesis and checked acceptance induce the pointwise incidence
   data and the integrated budget exactly as stated in the manuscript.
6. **7.2 local estimates:** prove the (h^r)/(h^{r-1}) local rates for
   the actual approximants and the certified inverse-width multiplier
   estimates, rather than assuming them in `PUFEMScaleBridge.v`.
7. **Kernel status:** the CI pipeline must compile the exact PR #42
   SHA with Rocq 9.2, run `coqchk`, inspect theorem *types* and
   `Print Assumptions`. No new theorem is promoted to `CHECKED-EXACT`
   before these checks succeed.

The continuous integral here is Stdlib's **Riemann integral**, which is
appropriate for the represented piecewise-polynomial code functions.
The equivalence to Lebesgue/Sobolev integration and the weak derivative
of the *glued* function must still be justified formally.

All of the above progress is candidate source code until machine
validation. The existing manuscript status of 5.6 and 7.2 remains
`PARTIAL`.
