# docs/assumptions/

This directory holds generated `Print Assumptions` snapshots for the v3 theorem surface explicitly audited by `.github/scripts/print_assumptions.sh`.

At minimum, every theorem advertised in `docs/FORMALIZATION_STATUS.md` as `CHECKED-RESTRICTED`, `CHECKED-ANALYTIC-CORE`, or `CHECKED-EXACT` must be present in the generator's `AUDIT_LIST`. Frontier theorems may also be audited before their status is promoted. A report here is therefore evidence about dependency footprint; by itself it does **not** promote a paper theorem to `CHECKED-EXACT`.

Files here are **generator output** produced by `.github/scripts/print_assumptions.sh`. Do NOT edit them by hand. CI runs the generator and diffs the freshly generated output against what is committed; any mismatch fails the build. This makes assumption-footprint drift mechanical and reviewable.

## Current contents

There are **18 theorem reports**. The snapshots in this revision are regenerated from the `V3 Fast` artifact for branch commit `80fa29f0518c923b061702c44c3b9105504cc01e` under the pinned Rocq 9.2 toolchain. On that run the V3 modules compiled and `coqchk` passed; the assumptions step failed only because these committed snapshots still used the older pretty-printed form of the same stdlib assumptions.

Nothing in this directory changes the correspondence classification in `FORMALIZATION_STATUS.md`. In particular, a theorem becomes `CHECKED-EXACT` only after the status document's full five-part discipline has been satisfied on the exact audited commit.

`DEFINITION-EXACT` rows get no theorem report merely for being definitions: a definition has no `Print Assumptions` verdict in the relevant sense.

## What the reports say

All 18 current verdicts have the same non-legacy assumption footprint:

```
Axioms:
ClassicalDedekindReals.sig_forall_dec
FunctionalExtensionality.functional_extensionality_dep
```

Under Rocq 9.2, `sig_forall_dec` is printed as the decidable-search principle

```
forall P : nat -> Prop,
  (forall n : nat, {P n} + {~ P n}) ->
  {n : nat | ~ P n} + {forall n : nat, P n}
```

rather than the older pretty-printed type retained in the previous snapshots. The dependency is still Rocq stdlib's classical-real infrastructure, not a new UELAT axiom.

`FunctionalExtensionality.functional_extensionality_dep` is likewise a stdlib dependency. No legacy UELAT axiom appears — nothing from `Adjunction/Functors.v` (`find_index_*`), `Examples/ChebyshevProof.v` (`rolle`, `chebyshev_nodal_identity_axiom`), `ErrorBound.v` (`parseval_identity_integration`), or `Example.v` (`error_bound_example`).

The footprint is uniform even for proofs that do not themselves invoke classical reasoning because `V3_Presentation.Presentation` contains `distF : F -> F -> R` and metric laws in `R`; theorem statements quantifying over a presentation therefore mention Rocq's classical real construction. Removing these two stdlib dependencies would require an explicit constructive-reals redesign and is not part of the present v3 formalization target.
