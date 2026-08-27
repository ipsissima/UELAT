# Authoritative v3 manuscript contract

The governing manuscript for this repository is:

**Andreu Ballús Santacana, _Proof-Carrying Analytic Approximation: Local-to-Global Evidence Transport at Encoding Cost_, version 3 of arXiv:2506.22693.**

The manuscript theorem numbering and statements are controlling. In particular:

- Proposition 6.3 uses the weight `w_i^2 = max(C_inf^2 + 2 L_i^2, 2 C_inf^2)`.
- Proposition 7.3 is the concrete compiler bound for standard local encodings.
- Theorem 7.4 is the main encoding-cost evidence-transport theorem under H1--H7.
- Corollary 7.5 is the same-order statement in the standard rational regime.
- The old probes--models adjunction is withdrawn from the current theorem surface.

A result may be described as machine-checked only when the repository correspondence ledger marks the exact current-paper statement `CHECKED-EXACT` at a recorded audited commit, with a successful pinned build, `coqchk`, and assumptions audit.

The pre-migration `main` is preserved at `legacy-pre-authoritative-v3-2026-08-27`.
