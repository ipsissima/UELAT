# Effective section 3 and categorical 4.4: proof audit

Governing manuscript: Proof-Carrying Analytic Approximation v3, arXiv:2506.22693.
Branch: formal-effective-31-and-category44-20261010, draft PR #43.
This is a working proof boundary, not CHECKED-EXACT status.

## 3.1: actual algorithmic sublemma now authored

The input is a CoreNamedPoint: a semantic vector plus its fast core Cauchy
name and the certified tail estimate. At stage n, the executable function
named_norm_approx computes a rational a_n with

    |Q2R(a_n) - norm(v)| <= 2 * dyadic(n).

The boolean test 2*qdyadic(n) < a_n uses only rational arithmetic. For a
nonzero named vector it eventually accepts: choose n with
4*dyadic(n)<norm(v). The first_true_index combinator extracts a successful
stage. Then a_n-2*qdyadic(n) is a strictly positive *rational* lower bound
on norm(v). See Coq/V3/NamedNonzeroWitness.v (candidate; kernel pending).

This eliminates any need to *supply* an additional positive norm lower bound.
It DOES NOT construct an approximately norm-preserving linear functional.
The central mathematical formalization still must realize Bishop's
epsilon-Hahn--Banach extension as a uniform Type-2 program from the
one-dimensional named subspace. The pre-existing record
EffectiveApproxHahnBanachStrong only assumes this extension as a field.

## 3.1: exact source line, inverse, and error control

OneDimensionalHBSeed.v now provides a concrete scalar-span starting
functional f0(a*v)=a*norm(v), with exact norm one, saturation at v,
and injectivity of a -> a*v.

The **computable scalar inverse** has two complementary routes:

- An explicit norm-only identity, valid for y=a*v:

      a = (norm(y+v)^2 - norm(y-v)^2)/(4*norm(v)^2).

  The positive rational norm lower bound produced by the previous
  sublemma allows effective reciprocal computation. Addition and norm
  approximation are computable in the Banach presentation. No
  functional of the full space is presupposed.

- A quantitative inverse modulus on the embedded line:

      distance(a*v,b*v) = |a-b|*norm(v).

  For any rational 0<ell<=norm(v), if
  distance(a*v,b*v)<ell*eps, then |a-b|<eps.

  Thus strict-distance semidecision searches over rational a have
  explicit scalar error certificates on the promised line.

These are mathematically constructive primitives for the initial
functional, not yet a fully implemented Type-2 coefficient realizer on
arbitrary incoming line names. The epsilon-Hahn--Banach extension
remains a separate and substantially harder obligation.

## 3.2: concrete route to compact finite nets

The key issue is computing the weak-star dual unit ball *as a compactum*
rather than writing a generic record that presupposes it.

1. Complete 3.1 and derive a uniformly computable one-norming family.
2. Prove the rational absolutely convex hull of that family's signed
   functionals is weak-star dense in the full dual unit ball by the bipolar
   argument. A norming family alone need not be dense in the full ball.
3. Express the dual ball as a co-c.e.-closed coordinate subset K of the
   computably compact Hilbert cube H (negative information).
4. At accuracy delta, enumerate finite lists D_m from the positive dense
   sequence, and dovetail finite stages of the complement of K with a
   semidecision of whether

      H is covered by (H minus K) union
      the open delta-balls centered at the points of D_m.

   Compactness plus dense positive points guarantees some finite list
   passes. Effective ambient compactness enables a terminating fair search,
   giving actual computable finite nets.
5. Construct the effective Cantor surjection, coordinate evaluation,
   computable linear norm-one interpolation from the Cantor subset
   to the unit interval, and the inverse only on the represented range.

The existing Coq/V3/EffectiveClosedCompactness.v contains abstract
closed-cover semidecision infrastructure. It has not yet been instantiated
with concrete positive dense dual-ball points and actual finite-net codes.
Theorem 3.2 must remain linear and isometric, not merely metric-isometric.

## 4.4: exact closure statement and limitation

The candidate Coq/V3/Category44FiniteCompilerClosure.v actually defines
identity and composition of finite-code Lipschitz realizers and name
realizers, proves Lipschitz constant multiplication, and establishes the
strict intermediate tolerance split:

  eta_T = eps/[3(1+Lambda_S)],  eta_S = eps/3;
  Lambda_S*eta_T + eta_S < eps.

Analytic arrows are identified extensionally by their underlying maps,
while chosen lift functors remain data of lifted arrows.

Crucial remaining obligation: its present precision is an R-valued input.
The manuscript requires an *effective rational* precision interface and
checker-accepted typed evidence. Before claiming Definition 4.4 fully
formalized, implement its rational compiler and the reflexive, Lipschitz,
and triangle evidence constructors. The stronger Definition 4.5
evidence-regularity hypothesis is NOT necessary for ordinary category
closure.

## Checking and claim policy

- The focused GitHub Actions workflow builds only the trusted dependencies
  needed by 3.1/4.4 and invokes Rocq 9.2, coqchk and Print Assumptions.
- Existence of source files or rational regression tests is never equivalent
  to successful kernel verification.
- Do not promote Lemma 3.1 or Theorem 3.2 merely because a preprocessing
  algorithm or conditional assembly record typechecks.
- Keep PR #43 in draft and leave the manuscript status ledger unchanged
  until every exact theorem-level obligation passes.

References:
- V. Brattka (2005), On the Borel Complexity of Hahn-Banach Extensions,
  Electronic Notes in Theoretical Computer Science 120, 3-16.
  https://doi.org/10.1016/j.entcs.2004.07.011
- V. Brattka and C. Sorg (2026),
  Computability of the Hahn-Banach Theorem Revisited,
  https://arxiv.org/abs/2603.16802
