# Current manuscript contract

This repository is governed by exactly one manuscript snapshot:

> **Andreu Ballús Santacana, _Proof-Carrying Analytic Approximation: Local-to-Global Evidence Transport at Encoding Cost_, arXiv:2506.22693 v3.**

Repository code, documentation, theorem names, and formalization claims must be interpreted against that manuscript. Older v3 snapshots and v1–v2 files are not allowed to override this contract.

## Current numbered result graph

### Section 2
- Definition 2.1 — real computable Banach presentation
- Definition 2.2 — certificate enrichment
- Definition 2.3 — certificate and certificate system
- Definition 2.4 — strict-slack completeness
- Proposition 2.5 — canonical slack certification
- Definition 2.6 — proof-relevant evidence category
- Definition 2.7 — evidence pseudometric
- Theorem 2.8 — conditional extensional collapse

### Section 3
- Lemma 3.1 — effective approximate Hahn–Banach
- Theorem 3.2 — effective linear Banach–Mazur universality
- Corollary 3.4 — universal finite linear representation

UELAT in the current paper means **Universal Embedding and Linear Approximation**. It is pointwise finite linear representation after a computable linear isometric embedding into standard computable `C([0,1])`; it is **not** a universal finite-rank approximation-property statement.

### Section 4
- Definition 4.1 — finite-code realizable Lipschitz map
- Theorem 4.2 — qualitative local-transport saturation
- Definition 4.4 — analytic maps with chosen lifts
- Definition 4.5 — evidence regularity
- Proposition 4.6 — non-faithfulness of analytic forgetting
- Proposition 4.7 — Grothendieck organization
- Definition 4.8 — evidence-local transformer
- Definition 4.9 — resource profile `(G,V,T,S,Q;L)`

### Section 5
- Definition 5.1 — rational `W^{1,2}` presentation
- Lemma 5.2 — exact finite-code arithmetic
- Proposition 5.3 — concrete soundness and strict-slack completeness
- Lemma 5.4 — certified rational partitions of unity
- Proposition 5.5 — exact finite synthesis
- Theorem 5.6 — certified localized PUFEM defect

### Section 6
- Definition 6.1 — incremental transport resources
- Theorem 6.2 — single-cover provenance compiler
- Proposition 6.3 — weighted global approximation budget
- Proposition 6.4 — global rational-code size

The authoritative Proposition 6.3 weight is

```text
w_i^2 = max(C_inf^2 + 2 L_i^2, 2 C_inf^2).
```

The older safe but looser coefficient `3 C_inf^2 + 2 L_i^2` is not the current statement.

### Section 7
- Definition 7.1 — provenance-complete certificate
- Theorem 7.2 — classical scale-sensitive PUFEM estimate
- **Proposition 7.3 — concrete compiler bound for standard local encodings**
- **Theorem 7.4 — encoding-cost evidence transport under Sobolev refinement**
- **Corollary 7.5 — same-order transport in the standard rational regime**
- Examples 7.6–7.7 — failure modes

Theorem 7.4 has three logical layers:

1. **H1–H7 core:** represented limit, same-order complete genealogy, verification bound, and `Q_target = 0`.
2. **Additional linear-bit regime** `beta_n = O(n+1)`: explicit `O(epsilon^{-1/(r-1)}(1+log(1/epsilon)))` certificate-size form.
3. **Additional source-generation regime** plus the linear-bit regime: `Q_source(epsilon)=O(log(1/epsilon))`.

The linear-bit and source-generation assumptions are not part of H1–H7 itself.

### Section 8
- Definition 8.1 — CCP-admissible constructor
- Proposition 8.2 — closure under admissible constructors
- Definition 8.3 — Contextual Choice Principle
- Definition 8.4 — CCP-generated universe
- Theorem 8.5 — invariant preservation
- Corollary 8.6 — internal Banach–Tarski boundary

### Section 9
- Proposition 9.1 — fibre indistinguishability
- Proposition 9.2 — extensional sheaf placement

## Withdrawn / non-current claims

The following do **not** belong to the authoritative theorem graph:

- the old probes–models adjunction as a theorem at the stated generality;
- universal finite-rank approximation of the identity;
- the old Chebyshev/B-spline numerical calculations removed in v3;
- generic certificate stability as a priority claim;
- ambient classical nonexistence claims derived from CCP;
- enriched-sheaf or stack claims not explicitly proved.

Legacy files may remain for auditability but must stay outside the authoritative export/build surface.

## Formalization claim policy

The manuscript itself fixes the rule. The authoritative correspondence table is

[`docs/FORMALIZATION STATUS.md`](./FORMALIZATION%20STATUS.md).

A current-paper result may be called **machine-checked** only when the table marks it `CHECKED-EXACT` at a recorded commit and all of the following hold:

1. the formal statement has the same strength and hypotheses as this manuscript;
2. the pinned current-paper project builds;
3. `coqchk` succeeds on the declared current-paper entry point;
4. reachable assumptions are audited at that exact commit.

Repository-wide CI or compilation of an older-snapshot file is not enough.

## Intentional current hard boundaries

Until discharged and audited, the following remain genuinely partial rather than documentation tasks:

1. **Lemma 3.1:** actual uniform constructive/effective epsilon-Hahn–Banach realizer, not merely its strong Type-2 contract.
2. **Theorem 3.2:** fully concrete effective compact dual-ball / Cantor-surjection / represented function-space / affine-extension / inverse-on-range instantiation.
3. **Theorem 5.6:** concrete instantiation of the standard multiplier/product-rule/bounded-overlap Sobolev primitives in a formal function-space library.
4. **Theorem 7.2:** concrete instantiation of the standard scale-sensitive `W^{1,2}` inequalities in the same analytic library.

The finite compiler and resource layers downstream of those analytic boundaries may be statement-exact even while these four boundaries remain partial.
