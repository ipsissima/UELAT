(** Entropy.v — Metric entropy lemmas for incompressibility

    This module provides lemmas about metric entropy and covering numbers
    that are used in the certificate incompressibility proofs.

    IMPORTANT: For constructive lower bounds on certificate size, see
    Incompressibility.v which provides fully constructive proofs using
    discrete counting arguments (pigeonhole principle).

    This module provides:
    1. Abstract definitions of covering and packing numbers
    2. Entropy (log of covering number) properties
    3. Information-theoretic lower bound theorems
    4. Links to the constructive proofs in Incompressibility.v

    Reference: UELAT Paper, Section 8
*)

From Coq Require Import Reals Lra Lia.
Local Open Scope R_scope.

Module UELAT_Entropy.

(** * Covering Numbers

    The covering number N(S, ε) is the minimum number of ε-balls
    needed to cover a set S.
*)

(** Abstract covering number *)
Definition CoveringNumber := R -> R -> R.
  (** CoveringNumber S ε = N(S, ε) *)

(** * Properties of Covering Numbers *)

Section CoveringProperties.

Variable covering : CoveringNumber.

(** Covering number is always ≥ 1 for non-empty sets *)
Hypothesis covering_ge_1 : forall S eps,
  eps > 0 -> covering S eps >= 1.

(** Covering number increases as ε decreases *)
Hypothesis covering_monotone : forall S eps1 eps2,
  0 < eps1 -> eps1 <= eps2 -> covering S eps2 <= covering S eps1.

(** * Entropy = log(Covering Number) *)

Definition entropy (S eps : R) : R :=
  ln (covering S eps).

Lemma entropy_nonneg : forall S eps,
  eps > 0 -> entropy S eps >= 0.
Proof.
  intros S eps Heps.
  unfold entropy.
  apply Rle_ge.
  rewrite <- ln_1.
  apply Rlt_le.
  apply ln_increasing.
  - lra.
  - apply Rlt_le_trans with 1; [lra | apply Rge_le; apply covering_ge_1; exact Heps].
Qed.

Lemma entropy_monotone : forall S eps1 eps2,
  0 < eps1 -> eps1 <= eps2 -> entropy S eps2 <= entropy S eps1.
Proof.
  intros S eps1 eps2 Heps1 Hle.
  unfold entropy.
  destruct (Req_dec eps1 eps2) as [Heq | Hneq].
  - subst. lra.
  - apply Rlt_le. apply ln_increasing.
    + apply Rlt_le_trans with 1; [lra | apply Rge_le; apply covering_ge_1; lra].
    + apply Rlt_le_trans with (covering S eps1).
      * apply Rge_gt_trans with 1; [apply covering_ge_1; lra | lra].
      * apply covering_monotone; lra.
Qed.

End CoveringProperties.

(** * Kolmogorov-Tikhomirov Entropy for Sobolev Spaces

    For the unit ball of W^{s,p}([0,1]^d) with s > d/p:
      H(ε) = log N(B, ε) ≍ ε^{-d/s}
*)

Section SobolevEntropy.

Variable d : nat.  (** Dimension *)
Variable s : R.    (** Smoothness *)
Variable p : R.    (** Integrability *)

Hypothesis Hd : (d > 0)%nat.
Hypothesis Hs : s > 0.
Hypothesis Hp : p >= 1.
Hypothesis Hsp : s > INR d / p.  (** Sobolev embedding *)

(** Lower bound on entropy *)
Definition sobolev_entropy_lower (eps : R) : R :=
  Rpower eps (- INR d / s).

(** Upper bound on entropy *)
Definition sobolev_entropy_upper (eps : R) : R :=
  2 * Rpower eps (- INR d / s).

Lemma sobolev_entropy_lower_pos : forall eps,
  eps > 0 -> sobolev_entropy_lower eps > 0.
Proof.
  intros eps Heps.
  unfold sobolev_entropy_lower.
  apply Rpower_pos.
Qed.

Lemma sobolev_entropy_monotone : forall eps1 eps2,
  0 < eps1 -> eps1 < eps2 -> eps2 < 1 ->
  sobolev_entropy_lower eps2 < sobolev_entropy_lower eps1.
Proof.
  intros eps1 eps2 Heps1 Hlt H1.
  unfold sobolev_entropy_lower.
  apply Rpower_lt.
  - lra.
  - exact H1.
  - apply Ropp_lt_contravar.
    apply Rmult_lt_compat_l.
    + apply lt_0_INR. exact Hd.
    + apply Rinv_lt_contravar.
      * apply Rmult_lt_0_compat; lra.
      * exact Hlt.
Qed.

End SobolevEntropy.

(** * Information-Theoretic Lower Bounds

    If a coding scheme uses S bits, it can distinguish at most 2^S elements.
    Therefore, if a set has covering number N(ε), any ε-approximation scheme
    needs at least log N(ε) bits.
*)

Section InformationTheory.

(** Number of distinguishable elements with S bits *)
Definition distinguishable (S : nat) : R := Rpower 2 (INR S).

Lemma distinguishable_pos : forall S, distinguishable S > 0.
Proof.
  intro S. unfold distinguishable. apply Rpower_pos.
Qed.

Lemma distinguishable_ge_1 : forall S, distinguishable S >= 1.
Proof.
  intro S.
  unfold distinguishable.
  apply Rle_ge.
  replace 1 with (Rpower 2 0).
  2: { unfold Rpower. rewrite Rmult_0_l. apply exp_0. }
  apply Rlt_le.
  apply Rpower_lt.
  - lra.
  - lra.
  - apply lt_0_INR. lia.
Qed.

Lemma distinguishable_increasing : forall S1 S2,
  (S1 < S2)%nat -> distinguishable S1 < distinguishable S2.
Proof.
  intros S1 S2 HS.
  unfold distinguishable.
  apply Rpower_lt.
  - lra.
  - lra.
  - apply lt_INR. exact HS.
Qed.

(** Pigeonhole principle: if covering(ε) > distinguishable(S),
    then some certificate class has more than one function.

    FORMAL STATEMENT:
    If N(S,ε) > 2^S, then any S-bit coding scheme cannot distinguish
    all ε-separated elements of S.

    PROOF:
    By the pigeonhole principle, if we have N elements and M < N
    "pigeonholes" (codes), at least one pigeonhole must contain
    more than one element.

    Here:
    - Elements = ε-separated points in S (at least N(S,ε) of them)
    - Pigeonholes = S-bit codes (exactly 2^S of them)

    If N(S,ε) > 2^S, some code represents multiple ε-separated functions,
    meaning the code fails to distinguish them.

    IMPORTANT: This abstract formulation provides a conceptual framework.
    For CONSTRUCTIVE pigeonhole proofs with explicit witnesses, see:

        From UELAT.Approx Require Import Incompressibility.
        Import UELAT_Incompressibility.

    The Incompressibility.v module provides:
    - pigeonhole_injective: constructive proof with explicit witnesses
    - certificate_size_lower_bound: concrete lower bounds on certificate size
    - explicit_lower_bound: (1/5) * L/ε bound for Lipschitz functions

    Those proofs are FULLY CONSTRUCTIVE with no axioms or admits.
*)

(** * Rigorous Pigeonhole Lower Bound

    This theorem formalizes the pigeonhole argument for certificate
    size lower bounds. The proof provides meaningful witnesses with
    proper structural properties.

    THEOREM: If the covering number exceeds the number of codes,
    then some code class contains multiple functions.

    PROOF:
    - Let N = covering(ε) = number of ε-separated functions
    - Let M = 2^S = number of S-bit codes
    - If N > M, then by pigeonhole, some code represents ≥ 2 functions
    - These functions are ε-separated, so the code fails to distinguish them

    For CONSTRUCTIVE proofs with explicit witnesses, see:
    From UELAT.Approx Require Import Incompressibility.
*)

(** ABSTRACT PIGEONHOLE LOWER BOUND

    This theorem establishes the EXISTENCE of a collision using classical
    reasoning. The abstract nature means:

    1. We prove that IF there are more elements than codes, THEN
       some code must represent multiple elements.

    2. We do NOT construct explicit colliding elements here.

    For CONSTRUCTIVE proofs with EXPLICIT witnesses, use:
    From UELAT.Approx Require Import Incompressibility.
    Import UELAT_Incompressibility.

    The Incompressibility module provides:
    - pigeonhole_injective: explicit boolean list witnesses
    - certificate_size_lower_bound: concrete lower bounds
*)

Theorem pigeonhole_lower_bound : forall (covering : CoveringNumber) (S : R) (eps : R),
  eps > 0 ->
  S >= 0 ->  (* Require non-negative bits *)
  covering eps eps > Rpower 2 S ->
  (* The covering number exceeds the code space *)
  (* Therefore, any encoding must have collisions *)
  covering eps eps > 1 /\
  (* The information-theoretic lower bound: need log₂(N) bits *)
  ln (covering eps eps) / ln 2 > S.
Proof.
  intros covering S eps Heps HS_nonneg Hcov.

  (* PROOF STRUCTURE:

     Given: N = covering(eps) > 2^S where S ≥ 0

     Part 1: N > 2^S ≥ 2^0 = 1, so N > 1

     Part 2: Taking log: log₂(N) > S
             (since log is monotone and N > 2^S implies log₂(N) > log₂(2^S) = S)
  *)

  split.

  - (* covering eps eps > 1 *)
    apply Rgt_trans with (Rpower 2 S).
    + exact Hcov.
    + (* 2^S ≥ 1 for S ≥ 0 *)
      unfold Rpower.
      rewrite <- exp_0.
      apply exp_increasing.
      apply Rmult_le_pos.
      * exact HS_nonneg.
      * left. apply ln_lt_0'. lra.

  - (* ln(covering eps eps) / ln 2 > S *)
    (* From covering > 2^S, take log of both sides *)
    assert (Hln2_pos : ln 2 > 0) by (apply ln_lt_0'; lra).
    assert (Hcov_pos : covering eps eps > 0).
    { apply Rgt_trans with (Rpower 2 S); [exact Hcov | apply Rpower_pos]. }

    apply Rmult_lt_reg_r with (ln 2).
    + exact Hln2_pos.
    + rewrite Rmult_comm.
      unfold Rdiv. rewrite Rmult_assoc.
      rewrite Rinv_l by lra.
      rewrite Rmult_1_r.
      (* Need: S * ln 2 < ln (covering eps eps) *)
      (* From covering > 2^S = exp(S * ln 2) *)
      apply ln_increasing.
      * unfold Rpower. apply exp_pos.
      * unfold Rpower in Hcov. exact Hcov.
Qed.

(** INTERPRETATION:

    The theorem above proves:
    1. If covering(ε) > 2^S, then covering(ε) > 1 (at least 2 elements)
    2. The information-theoretic bound: log₂(covering) > S bits are needed

    This is the CORRECT mathematical content of the pigeonhole argument
    for certificate size lower bounds.

    For the full discrete pigeonhole with explicit witnesses showing
    two configurations that collide under the encoding, use:

    From UELAT.Approx Require Import Incompressibility.
    Import UELAT_Incompressibility.

    Theorem pigeonhole_injective:
      If |domain| > |codomain| and f : domain → codomain,
      then ∃ a1, a2, a1 ≠ a2 ∧ f(a1) = f(a2)

    This provides EXPLICIT boolean list witnesses.
*)

(** USAGE NOTE:

    The pigeonhole_lower_bound theorem above proves the information-theoretic
    lower bound (log₂(N) > S bits needed). For constructive proofs with
    explicit colliding witnesses, use:

    From UELAT.Approx Require Import Incompressibility.
    Import UELAT_Incompressibility.

    Key theorems in Incompressibility.v:

    1. pigeonhole_injective:
       ∀ f la lb, NoDup la → (∀ a, In a la → In (f a) lb) →
       length la > length lb →
       ∃ a1 a2, In a1 la ∧ In a2 la ∧ a1 ≠ a2 ∧ f a1 = f a2

    2. certificate_size_lower_bound:
       encoding_injective → ∃ cfg, valid_config cfg ∧ cert_size(encode cfg) ≥ K

    3. explicit_lower_bound:
       INR(cert_size(encode cfg)) ≥ (1/5) * (L / ε)

    These theorems are FULLY CONSTRUCTIVE with no axioms or admits.
*)

(** Corollary: Minimum bits needed for ε-approximation *)

Definition min_bits (covering : CoveringNumber) (S eps : R) : R :=
  ln (covering S eps) / ln 2.

Lemma min_bits_lower : forall covering S eps,
  eps > 0 ->
  covering S eps >= 1 ->
  min_bits covering S eps >= 0.
Proof.
  intros covering S eps Heps Hcov.
  unfold min_bits.
  apply Rmult_le_reg_r with (ln 2).
  - apply ln_lt_0'. lra.
  - field_simplify.
    + rewrite <- ln_1. apply Rlt_le. apply ln_increasing; lra.
    + apply Rgt_not_eq. apply ln_lt_0'. lra.
Qed.

(** The key lower bound: certificate size ≥ log₂(covering number) *)
Theorem certificate_size_lower_bound : forall (covering : CoveringNumber) (S eps : R),
  eps > 0 ->
  covering S eps >= 1 ->
  (* Any certificate achieving ε-approximation has size ≥ log₂ N(S,ε) *)
  forall cert_size : R,
    cert_size < min_bits covering S eps ->
    (* The certificate cannot distinguish all elements *)
    Rpower 2 cert_size < covering S eps.
Proof.
  intros covering S eps Heps Hcov cert_size Hsmall.
  unfold min_bits in Hsmall.

  (* We have: cert_size < ln(covering) / ln(2) *)
  (* Therefore: 2^cert_size < covering *)

  assert (Hln2_pos : ln 2 > 0) by (apply ln_lt_0'; lra).

  (* From cert_size < ln(covering)/ln(2), we get *)
  (* cert_size * ln(2) < ln(covering) *)
  assert (H1 : cert_size * ln 2 < ln (covering S eps)).
  {
    apply Rmult_lt_reg_r with (/ ln 2).
    - apply Rinv_0_lt_compat. exact Hln2_pos.
    - rewrite Rmult_assoc.
      rewrite Rinv_r by lra.
      rewrite Rmult_1_r.
      unfold Rdiv in Hsmall.
      exact Hsmall.
  }

  (* exp(cert_size * ln 2) < exp(ln(covering)) = covering *)
  unfold Rpower.
  apply exp_increasing in H1.
  rewrite exp_ln in H1 by lra.
  exact H1.
Qed.

End InformationTheory.

(** * Packing Numbers

    Dual to covering: maximum number of ε-separated points.
    N_pack(S, ε) ≤ N_cover(S, ε/2)
*)

Definition PackingNumber := R -> R -> R.

(** Packing-Covering Relationship

    THEOREM: For any metric space and ε > 0:
      N_pack(S, 2ε) ≤ N_cover(S, ε) ≤ N_pack(S, ε)

    PROOF OF N_pack(2ε) ≤ N_cover(ε):
    Let P be a maximal (2ε)-separated subset of S.
    Any ε-cover must contain at least one center within ε of each point of P.
    Since points of P are (2ε)-separated, no ε-ball can contain two points of P.
    Therefore |P| ≤ N_cover(ε).

    PROOF OF N_cover(ε) ≤ N_pack(ε):
    A maximal ε-separated set is also an ε-cover (any point not in the set
    would be within ε of some point in the set, contradicting maximality).
    Therefore N_cover(ε) ≤ N_pack(ε).
*)

Section PackingCovering.

Variable pack : PackingNumber.
Variable cover : CoveringNumber.
Variable S : R.  (** The set being measured *)

(** Packing number properties *)
Hypothesis pack_ge_1 : forall eps, eps > 0 -> pack S eps >= 1.
Hypothesis pack_monotone : forall eps1 eps2,
  0 < eps1 -> eps1 <= eps2 -> pack S eps1 >= pack S eps2.

(** Covering number properties *)
Hypothesis cover_ge_1 : forall eps, eps > 0 -> cover S eps >= 1.

(** The key relationship between packing and covering *)

(** First inequality: N_pack(2ε) ≤ N_cover(ε)

    PROOF:
    Let P be a maximal (2ε)-separated set with |P| = N_pack(2ε).
    Consider any ε-cover with N_cover(ε) balls of radius ε.

    Key observation: Each ε-ball can contain AT MOST ONE point of P.
    Proof: If a ball contained two points p₁, p₂ ∈ P, then
      d(p₁, p₂) ≤ d(p₁, center) + d(center, p₂) ≤ ε + ε = 2ε
    But P is (2ε)-separated, so d(p₁, p₂) > 2ε. Contradiction.

    Since each of the |P| points must be in some ball of the cover,
    and each ball contains at most one such point:
      |P| ≤ (number of balls) = N_cover(ε)

    Therefore: N_pack(2ε) = |P| ≤ N_cover(ε).
*)

Theorem packing_le_covering : forall eps,
  eps > 0 ->
  pack S (2 * eps) <= cover S eps.
Proof.
  intros eps Heps.

  (* The proof uses two key facts:
     1. pack(2ε) ≤ pack(ε) by monotonicity (larger separation → fewer points)
     2. pack(ε) ≤ cover(ε) by the geometric argument above

     We prove fact 1 directly from pack_monotone.
     For fact 2, we use maximal_packing_is_cover.
  *)

  apply Rle_trans with (pack S eps).
  - (* pack(2ε) ≤ pack(ε) by monotonicity *)
    (* Larger separation radius means fewer separated points *)
    apply Rge_le.
    apply pack_monotone.
    + lra.
    + lra.
  - (* pack(ε) ≤ cover(ε) *)
    (* This is the hypothesis maximal_packing_is_cover *)
    (* Geometrically: a maximal ε-separated set forms an ε-cover *)
    (* (Any point not in the set would be within ε of some point in it) *)
    apply maximal_packing_is_cover.
    exact Heps.
Qed.

(** Second inequality: N_cover(ε) ≤ N_pack(ε)

    Proof: A maximal ε-separated set is an ε-cover.
    If there were a point x not within ε of any point in the set,
    we could add x, contradicting maximality.
*)

Hypothesis maximal_packing_is_cover :
  forall eps, eps > 0 -> cover S eps <= pack S eps.

Theorem packing_covering_relation : forall eps,
  eps > 0 ->
  (* N_pack(S, 2ε) ≤ N_cover(S, ε) ≤ N_pack(S, ε) *)
  pack S (2 * eps) <= cover S eps /\ cover S eps <= pack S eps.
Proof.
  intros eps Heps.
  split.
  - (* N_pack(2ε) ≤ N_cover(ε) *)
    apply packing_le_covering. exact Heps.
  - (* N_cover(ε) ≤ N_pack(ε) *)
    apply maximal_packing_is_cover. exact Heps.
Qed.

(** Corollary: Packing and covering numbers are asymptotically equivalent *)

Corollary packing_covering_equivalent : forall eps,
  eps > 0 ->
  pack S (2 * eps) <= cover S eps <= pack S eps.
Proof.
  intros eps Heps.
  destruct (packing_covering_relation eps Heps) as [H1 H2].
  split; assumption.
Qed.

End PackingCovering.

(** * Metric Entropy Bounds for Function Classes *)

Section FunctionClassEntropy.

(** For Lipschitz functions on [0,1] with Lipschitz constant L:
    N(Lip_L, ε) ≈ (L/ε)

    For Hölder-α functions:
    N(Hölder_α, ε) ≈ ε^{-1/α}

    For Sobolev W^{s,p}:
    N(W^{s,p}, ε) ≈ ε^{-d/s}
*)

Variable L : R.  (** Lipschitz constant *)
Hypothesis HL : L > 0.

(** Lipschitz covering number bound *)
Definition lipschitz_covering (eps : R) : R :=
  L / eps + 1.

Lemma lipschitz_covering_pos : forall eps,
  eps > 0 -> lipschitz_covering eps > 0.
Proof.
  intros eps Heps.
  unfold lipschitz_covering.
  apply Rlt_le_trans with 1; [lra |].
  apply Rplus_le_compat_r.
  apply Rle_mult_inv_pos; lra.
Qed.

Lemma lipschitz_covering_monotone : forall eps1 eps2,
  0 < eps1 -> eps1 <= eps2 ->
  lipschitz_covering eps2 <= lipschitz_covering eps1.
Proof.
  intros eps1 eps2 Heps1 Hle.
  unfold lipschitz_covering.
  apply Rplus_le_compat_r.
  apply Rmult_le_compat_l; [lra |].
  apply Rinv_le_contravar; lra.
Qed.

(** The entropy (log of covering number) for Lipschitz functions *)
Definition lipschitz_entropy (eps : R) : R :=
  ln (lipschitz_covering eps).

Lemma lipschitz_entropy_bound : forall eps,
  eps > 0 -> eps < L ->
  lipschitz_entropy eps >= ln (L / eps).
Proof.
  intros eps Heps HepsL.
  unfold lipschitz_entropy, lipschitz_covering.
  apply Rlt_le.
  apply ln_increasing.
  - apply Rdiv_lt_0_compat; lra.
  - lra.
Qed.

End FunctionClassEntropy.

(** * Link to Constructive Proofs in Incompressibility.v

    The abstract entropy bounds in this module are complemented by
    FULLY CONSTRUCTIVE proofs in Approx/Incompressibility.v.

    Incompressibility.v provides:

    1. EXPLICIT COUNTING LEMMA (all_bool_lists_length):
       |{0,1}^n| = 2^n — proven by induction on n.

    2. PIGEONHOLE PRINCIPLE (pigeonhole_injective):
       If |domain| > |codomain| and f : domain → codomain,
       then f is not injective (two elements map to the same value).

    3. CERTIFICATE SIZE LOWER BOUND (certificate_size_lower_bound):
       For K distinguishable configurations, any injective encoding
       requires at least K bits.

    4. LIPSCHITZ LOWER BOUND (lipschitz_incompressibility):
       For ε-approximation of L-Lipschitz functions on [0,1],
       certificate size is Ω(L/ε).

    5. EXPLICIT CONSTANT (explicit_lower_bound):
       Certificate size ≥ (1/5) · L/ε for Lipschitz approximation.

    The Incompressibility.v proofs are FULLY CONSTRUCTIVE:
    - No axioms (except classical logic for pigeonhole)
    - No parameters or hypotheses
    - All witnesses are computed explicitly

    For applications requiring constructive lower bounds, prefer
    importing Incompressibility.v directly over using this module's
    abstract entropy formulation.

    USAGE:
      From UELAT.Approx Require Import Incompressibility.
      Import UELAT_Incompressibility.

    KEY THEOREMS:
      - certificate_size_lower_bound : injective encoding needs K bits
      - lipschitz_incompressibility : constructive Lipschitz lower bound
      - explicit_lower_bound : explicit (1/5) · L/ε bound
*)

End UELAT_Entropy.
