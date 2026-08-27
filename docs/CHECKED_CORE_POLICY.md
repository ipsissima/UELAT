# Current-paper checked-core policy

The authoritative manuscript is:

**Andreu Ballús Santacana, _Proof-Carrying Analytic Approximation: Local-to-Global Evidence Transport at Encoding Cost_, arXiv:2506.22693 v3.**

The repository deliberately distinguishes two formalization surfaces.

## 1. Checked-core candidate

Entry point:

```text
Coq/UELATCheckedCoreV3.v
```

Project:

```text
Coq/_CoqProject.checked-core-v3
```

Workflow:

```text
.github/workflows/checked-core-v3.yml
```

This surface contains current-paper statements that can be kernel-validated independently of the four intentional analytic/computable-analysis research boundaries. In particular, conditional theorems are allowed to quantify over exactly the hypotheses that the manuscript itself states; they are not required to construct those hypotheses unless the manuscript theorem claims to construct them.

A green build is still **not by itself** permission to say that every exported result is `CHECKED-EXACT`. The exact formal statement must be compared against the manuscript row and reachable assumptions must be audited at the passing commit.

## 2. Research / completion surface

Entry point:

```text
Coq/UELATAuthoritativeV3.v
```

This additionally contains the strong Type-2 Section 3 construction track and explicit analytic interfaces used to close remaining boundaries. These files are research formalization, not blanket machine-checked claims.

## Intentional partial boundaries

The following remain outside the checked-core claim until their concrete implementations are complete and separately audited:

1. **Lemma 3.1** — uniform constructive/effective epsilon-Hahn–Banach existence producing the strong Type-2 realized functional contract.
2. **Theorem 3.2** — fully concrete effective compact dual-ball presentation, effective Cantor surjection, represented function-space realization, affine extension to `[0,1]`, and inverse-on-range assembly.
3. **Theorem 5.6** — instantiation of the standard multiplier/product-rule/bounded-overlap Sobolev primitives in a concrete formal `W^{1,2}` function-space library.
4. **Theorem 7.2** — instantiation of the scale-sensitive `W^{1,2}` PUFEM inequalities in that same analytic library.

## Why Theorem 7.4 may nevertheless be checked conditionally

The authoritative Theorem 7.4 is explicitly conditional on H1–H7. Its H3 assumes supplied accepted local approximation evidence, and H4 assumes/records the exact synthesis and scale estimate derived from the preceding analytic layer. The formal theorem is therefore statement-exact when it proves the represented limit, persistent genealogy, same-order encoding bound, verification bound and `Q_target = 0` **from those stated hypotheses**.

The optional clauses remain separate:

- `LinearBitRegime` represents the additional `beta_n = O(n+1)` assumption used for the explicit standard-rational certificate-size asymptotic;
- `SourceLookaheadRegime` represents the still stronger local-certificate-generation lookahead assumption used for the conditional `Q_source(epsilon)=O(log(1/epsilon))` conclusion.

Neither is silently inserted into H1–H7.

## Formalization-status authority

The only authoritative theorem-by-theorem status table is:

[`docs/FORMALIZATION STATUS.md`](./FORMALIZATION%20STATUS.md).

Only a row explicitly marked `CHECKED-EXACT`, at a recorded audited commit, may be described as machine-checked for the current manuscript.
