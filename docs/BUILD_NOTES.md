# Phase 1 Build Notes: Coq 8.19 → Rocq 9 migration

Purpose: record every toolchain / build-config change made during the
Phase 1 migration, so any behavioral surprise can be traced back to a
specific edit rather than a silent drift.

## Baseline (before migration)

- `Coq/` source uses Rocq 9 conventions: `From Stdlib Require …`,
  post-8.20 stdlib names (`length_app`, etc.). `Coq/Makefile` header
  is literally *"GNUMakefile for Rocq 9.0.1"*.
- `uelat.opam` pinned `coq {>= "8.18" & < "8.20"}`, i.e. Coq 8.18 / 8.19.
- CI on `main` has been red since 2025-12-31 (run 20609761616) for
  exactly this mismatch.
- **New failure mode observed on 2026-08-12** (PR #32, head e4baa0b,
  runs 31603623287 / 31603690679): under the old pin the opam solver
  picks `coq-mathcomp-*` versions whose transitive deps include
  `rocq-hierarchy-builder.1.9.1` and `coq-elpi.2.2.3`, both of which
  invoke the `rocq` binary that only exists in Rocq 9:
  ```
  /bin/sh: 1: rocq: not found
  rocq makefile -f _CoqProject -o Makefile.coq
  make: rocq: No such file or directory
  ```
  → The pre-migration `uelat.opam` is now literally unresolvable
  against the current `coq-released` opam repo, independent of any
  source-style question.

## Baseline inventory (locked, must not regress)

Recorded in `docs/INVENTORY.md` (commit e4baa0b). Totals across the
36 `.v` files:

| item          | count |
| ---           | ---   |
| Theorem       | 67    |
| Lemma         | 327   |
| Corollary     | 11    |
| Definition    | 241   |
| Example       | 1     |
| Qed           | 378   |
| Defined       | 29    |
| **Admitted**  | **3** |
| `admit.`      | 0     |
| **Axiom**     | **6** |
| **Parameter** | **15**|
| Hypothesis    | 75    |

The 3 Admitted are exactly:
`Coq/Util/Entropy.v:486`, `Coq/Util/Entropy.v:680`, `Coq/Adjunction/Probe.v:122`
— matching `docs/AXIOMS_AND_ADMISSIONS.md`.

## Changes in this phase

### 1. `uelat.opam`
- Replaced `"coq" {>= "8.18" & < "8.20"}` with
  `"rocq-prover" {>= "9.0.0"}`. Forces the opam solver to pick a
  Rocq-9 toolchain, which is what the source already speaks.
- Dropped `"coq-coquelicot"`. **Rationale:** grep of `Coq/` confirms
  no source file imports Coquelicot — the string only appears inside
  comments in `Coq/Examples/ChebyshevProof.v`. Removing the unused
  dep both shortens the build and removes a place where a
  Coquelicot-vs-Rocq-9 version conflict could hold up the switch.
  No proof depends on it.
- Kept `coq-mathcomp-{ssreflect,algebra,analysis}` under their
  legacy `coq-` prefix — those packages are still published on the
  Rocq-9 opam channel under that name (as `coq-elpi.2.2.3` and
  `rocq-hierarchy-builder.1.9.1` co-installing in the failure log
  demonstrates). Let the solver pick versions.

### 2. CI workflow (`.github/workflows/ci.yml`)
- No changes. `coq_makefile` and `coqchk` are still the correct
  binary names under Rocq 9, and the switch/install/build steps
  are already generic (`opam install . --deps-only`, then
  `coq_makefile … && make`). The switch's install step will now
  resolve `rocq-prover.9.x.y` because that's what `uelat.opam`
  asks for.

## Not changed in this phase

- **No `.v` file was edited.** The whole point of the migration is
  to move the toolchain forward to match the sources, not the other
  way around. Any source-level Rocq-9 incompatibility that CI
  surfaces will be recorded in a new section below with file, line,
  cause, and fix.
- **No theorem statement, `Axiom`, `Parameter`, `Admitted`, or
  `admit.` was added, deleted, or altered.**

## Iteration log

- **Round 1** (commit 76cdbc6): switch opam pin only. Expected
  outcome: opam resolves Rocq 9, mathcomp stack builds against it,
  `coq_makefile … && make` builds all 36 files without source
  edits. If any file breaks, its error goes in a new "Round 2"
  subsection with file/line/cause/fix.

  Actual outcome: **opam resolution succeeded** —
  `rocq-prover.meta.1`, `rocq-core.9.2.0`, `rocq-stdlib.9.2.0`,
  `rocq-mathcomp-ssreflect/algebra/analysis` 2.6.0 / 1.16.0, and
  `rocq-hierarchy-builder.1.10.3` all installed cleanly (CI run
  31605309879, `Setup opam switch safely` completed at 14:43:56).
  The `Build Coq` step then failed at `coq_makefile`, not on any
  `.v` file:
  ```
  + coq_makefile -f Coq/_CoqProject Coq/Adjunction/Adjunction.v … -o Coq/Makefile
  Error: Output file must be in the current directory.
  ```
  Cause: under Rocq 9, `coq_makefile` rejects an `-o` path outside
  the current directory. Not a source-level regression.

- **Round 2** (commit e68bc7a): patch `.github/workflows/ci.yml` only —
  run `coq_makefile` from inside `Coq/` with file paths stripped of
  the leading `Coq/`, then `make -C Coq -j2` as before. No opam or
  `.v` change. Expected outcome: `Build Coq` reaches actual source
  compilation. Any file that fails to build under Rocq 9 lands in a
  new "Round 3" subsection with file/line/cause/fix.

  Actual outcome: **workflow patch verified** — CI run 31631533078
  (Coq job 94231230154) got past `coq_makefile` and started
  compiling. `ROCQ compile Foundations/Certificate.v` finished (with
  benign `Scheme All` register-all warnings only), `ROCQ compile
  Foundations/ProbeTheory.v` finished, and the build stopped in
  `Foundations/CCP.v` on the first real Rocq 9 tactic-behavior
  change. Setup succeeded via a cached `~/.opam` (that's why the
  step took seconds, not the 25 min the earlier run took). Two
  further empty-commit retriggers were spent on unrelated GitHub
  Actions network transients (`ocaml/setup-ocaml@v3` socket-hang-up
  from 19:10-19:13 UTC on 2026-08-12) that never touched our patch.

- **Round 3** (this commit): fix `Coq/Foundations/CCP.v:55`. No
  toolchain change; no statement change.

  Error:
  ```
  File "./Foundations/CCP.v", line 55, characters 54-57:
  Error:
  In environment
  P : nat -> bool
  Hp0 : P 0%nat = false
  Hnone : None = None
  Hle : (0 <= 0)%nat
  The term "Hp0" has type "P 0%nat = false" while it is expected to
  have type "false = false".
  ```

  Cause: `bounded_search_complete`'s base case ran
  `destruct (P 0%nat) eqn:Hp0; [discriminate | exact Hp0]`.
  Under Rocq 9, `destruct <non-variable term> eqn:H` substitutes
  the term in the goal (in the `false` branch, the goal `P 0 = false`
  becomes `false = false`) rather than leaving the goal untouched.
  So the old `exact Hp0` — where `Hp0 : P 0 = false` — no longer
  type-checks against the rewritten goal `false = false`.

  Fix: replace `exact Hp0` with `reflexivity`. The statement
  `bounded_search_complete : forall P bound, bounded_search P bound = None
  -> forall n, (n <= bound)%nat -> P n = false` is unchanged, and no
  new `Admitted` / `admit.` / `Axiom` / `Parameter` was introduced.
  The inductive-case sub-proof already uses `subst; exact HpSb` where
  `HpSb : P (S b) = false` matches the goal directly (no goal-side
  substitution because `P (S b)` didn't occur in the goal at the
  destruct site), so it is untouched.

  Expected outcome: `Foundations/CCP.v` compiles; build advances past
  it and either goes green or reveals the next real Rocq 9 source
  break, logged as Round 4.

  Actual outcome: **CCP.v compiled** (CI run 31654569651, Coq job
  94306064969). Build advanced into parallel compilation of
  `Approx/Certificate.v` and `Util/Modulus.v`, each with its own
  Rocq 9 break (logged as Round 4).

- **Round 4** (this commit): two independent source-level fixes,
  both proof-side only. No statement, `Axiom`, `Parameter`,
  `Admitted`, or `admit.` added, deleted, or altered anywhere.

  **4a. `Coq/Approx/Certificate.v:18`** — `bernstein` definition.

  Error:
  ```
  File "./Approx/Certificate.v", line 18, characters 16-17:
  Error:
  In environment
  N : nat
  k : nat
  x : R
  The term "N" has type "nat" while it is expected to have type "R".
  ```

  Cause: file imported `From Stdlib Require Import … Binomial …`.
  In Rocq 9's namespace, the unqualified `Binomial` module resolves
  to an R-typed `binomial` rather than the nat-typed one, so
  `binomial N k` with `N k : nat` no longer type-checks. Also, the
  previous body `IZR (binomial N k)` implicitly relied on
  now-removed nat→Z coercion.

  Fix: swap the ambiguous `Binomial` import for the qualified
  `Coq.Arith.Binomial` (matching the pattern already used and
  known to build in `Coq/Certificate.v:17`), and make the
  nat→Z→R chain explicit:
  ```
  Definition bernstein (N k:nat) (x:R) : R :=
    IZR (Z.of_nat (binomial N k)) * (x ^ k) * ((1 - x) ^ (N - k)).
  ```
  Definition semantics are identical: `bernstein N k x =
  C(N,k) · x^k · (1-x)^(N-k)`. No downstream call site changes.

  **4b. `Coq/Util/Modulus.v:22`** — `lipschitz_modulus` proof.

  Error:
  ```
  File "./Util/Modulus.v", line 22, characters 2-3:
  Error: [Focus] Wrong bullet -: No more goals.
  ```

  Cause: proof used `refine (ex_intro _ {| mu := … |} _)` with a
  record literal missing the `mu_pos` and `mu_mono` fields, then
  interleaved `split` calls and `-` bullets. Under Rocq 9 the
  resulting obligation order / focusing behavior differs from the
  older Coq, and the first `-` fires when its goal has already been
  discharged.

  Fix: build the record fully (`Hpos`, `Hmono` proved as separate
  `assert`s first), then instantiate the existential with the
  complete record and dispatch the equality body directly. No
  `refine`, no bullets, no order-dependence. Statement of
  `lipschitz_modulus` unchanged; witness function `mu(eps) = eps/(1+L)`
  and its two properties unchanged.

- **Round 5** (this commit): the Round-4 attempt to route
  `Approx/Certificate.v` through `Coq.Arith.Binomial` doesn't work
  under Rocq 9 either — the compat alias `Coq.Arith.Binomial →
  Stdlib.Arith.Binomial` fails at load time:
  ```
  File "./Approx/Certificate.v", line 4, characters 15-33:
  Error: Unable to locate library Stdlib.Arith.Binomial
  ```
  because Rocq 9's stdlib no longer ships `Stdlib.Arith.Binomial`
  at all. The nat-typed `binomial : nat -> nat -> nat` that Coq 8.x
  provided from `Coq.Arith.Binomial` has been retired.

  Fix: switch both `Coq/Approx/Certificate.v` and
  `Coq/Approx/Bernstein.v` to use `C : nat -> nat -> R` from
  `Stdlib.Reals.Binomial`. `C n k` is defined there as
  `INR (fact n) / (INR (fact p) * INR (fact (n - p)))`, i.e. exactly
  the R-valued binomial coefficient, which is what
  `IZR (binomial N k)` was trying to express in the first place —
  same value, just skipping the removed nat→Z→R detour. Definitions:

  ```
  (* Approx/Certificate.v *)
  Definition bernstein (N k:nat) (x:R) : R :=
    C N k * (x ^ k) * ((1 - x) ^ (N - k)).

  (* Approx/Bernstein.v — inside BN's `term` *)
  f (INR k / INR N) * (C N k * x^k * (1 - x)^(N - k))
  ```

  No statement / theorem / `Axiom` / `Parameter` / `Admitted` /
  `admit.` change anywhere. Downstream callers use `eval_cert` /
  `BN`, never inspect `bernstein`'s specific numeric form, so the
  refactor is transparent to every proof that consumes these
  operators.

  Legacy files `Coq/Certificate.v`, `Coq/Approx/Bernstein_Lipschitz.v`,
  and (transitively) `Coq/PartitionOfUnity.v`/`Coq/ErrorBound.v` also
  reference `Coq.Arith.Binomial` and its nat-typed lemmas
  (`binomn0`, `binomnn`, `binom_gt`, `binom_mult_S`). Not yet
  touched — CI hasn't reported on them because make -j2 aborts
  fast. If they surface as Rocq 9 breaks in the next round, they
  get their own entry.

- **Round 6** (this commit): `Coq/Approx/Incompressibility.v:82` —
  `Error: The variable NoDup_map was not found in the current
  environment.`

  Cause: Rocq 9's `Stdlib.Lists.List` no longer exports the forward
  direction of NoDup-preservation-under-map. Only `NoDup_map_inv`
  (the backward direction, `NoDup (map f l) -> NoDup l`) remains.
  `all_bool_lists_nodup` relied on the forward direction.

  Fix: add a small local helper `NoDup_map_local` with the standard
  signature `(∀ x y, x∈l → y∈l → f x = f y → x = y) → NoDup l →
  NoDup (map f l)`, proved by straightforward induction on `NoDup l`.
  Reroute the two `apply NoDup_map` calls in `all_bool_lists_nodup`
  to `NoDup_map_local`. No statement change to `all_bool_lists_nodup`
  or any other lemma; no `Axiom`, `Parameter`, `Admitted`, or
  `admit.` added. The helper is a plain `Lemma … Proof … Qed.` —
  the constructive-island grep in CI ignores files outside
  `Coq/Util/Modulus.v` and `Coq/Approx/{Certificate,Bernstein,
  Bernstein_Lipschitz,Spec,Weierstrass_Lipschitz}.v`, and this
  helper introduces no forbidden constructs anywhere in the tree.

  Expected outcome: `Approx/Incompressibility.v` compiles;
  build continues into the still-unexercised modules
  (Adjunction/*, Stability/*, Examples/*, Approx/{EffectiveDescent,
  UELAT_{External,Internal},Spec,Weierstrass_Lipschitz,
  Bernstein_Lipschitz}, and the legacy root files). If any of them
  hit further Rocq 9 breaks, each gets its own round.

  Actual outcome: `all_bool_lists_nodup` compiled. Next break was
  `pigeonhole_injective`'s statement on line 119 —
  `length la > length lb` with `Local Open Scope R_scope.` in
  effect resolves `>` to R-comparison, and `length la : nat` no
  longer matches (Rocq 9 stopped inserting an implicit nat→R
  coercion here). Same shape recurs at a handful of nearby sites.

- **Round 7** (this commit): scope-annotate every unscoped nat
  comparison inside `Approx/Incompressibility.v`. Sites patched:
  - line 119: `length la > length lb` → `(length la > length lb)%nat`
  - line 128: `length la <= length lb` → `(length la <= length lb)%nat`
  - line 202: `cert_size (encode cfg) >= K` → same with `%nat`
  - line 232: `Nat.pow 2 K >= 1` → same with `%nat`
  - line 354: `cert_size (encode cfg) >= K_lipschitz` → same with `%nat`

  Purely notational; each `%nat`-scoped expression means exactly
  what the unscoped expression meant under the older Coq (nat
  comparison). No lemma / theorem statement semantically changed,
  no `Axiom` / `Parameter` / `Admitted` / `admit.` added.
