# Theorems 5.6 and 7.2 — formalization boundary (working branch)

Governing manuscript: arXiv:2506.22693 v3, **Proof-Carrying Analytic Approximation**.

This note describes a **candidate, unverified** formal development on the PR #42 branch. It **does not** promote either manuscript theorem to `CHECKED-EXACT`. Authoritative status remains **PARTIAL**.

## Constructed candidates

- `PUFEMPointwiseCore.v`: finite Cauchy–Schwarz, square-multiplier and product-term bounds, active support rather than an incorrectly capped full neighbour list, and finite positive quadrature.
- `PUFEMIntegralBridge.v`: local-to-global energy inequality using an explicit positive linear integral; a discrete weighted-sample instance is built with no assumed integral laws.
- `PUFEMScaleBridge.v`: square-error global scale estimate derived from the previous result and **stated** local rate bounds. It proves the abstract one-order loss and a norm consequence under an explicit constant.
- `PUFEMLimitBridge.v`: epsilon proof that finite quadrature inequalities pass to real-number limits whenever both sides converge.

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
- No `Admitted` or `Axiom` is intentionally introduced in these four new files. This is a source-level claim pending build and kernel verification.
- Finite numerical smoke tests are useful to detect coefficient mistakes but do not prove theorem correctness.
- `Print Assumptions` reporting **Closed under the global context** does **not** discharge hypotheses explicitly quantified in a theorem. Exact theorem-type comparison against the manuscript is always required.
