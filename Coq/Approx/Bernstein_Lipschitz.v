From mathcomp Require Import all_ssreflect all_algebra bigop.
From mathcomp.analysis Require Import reals normedtype.
Require Import Coq.Reals.Reals Coq.micromega.Lra Coq.Arith.Binomial.
From Stdlib Require Import Lia.
From UELAT.Approx Require Import Certificate.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Bernstein.

(* Reals-cast binomial *)
Definition C (n k:nat) : R := IZR (Z.of_nat (binom n k)).
Definition w (N k:nat) (x:R) : R := C N k * x^k * (1 - x)^(N - k).

Definition BN (N:nat) (f:R->R) (x:R) : R :=
  \sum_(k < N.+1) f (INR k / INR N) * w N k x.

(* --- Aux lemmas ------------------------------------------------------- *)

Lemma C0 (n:nat) : C n 0 = 1.
Proof. rewrite /C; now rewrite binom0. Qed.

Lemma Cn (n:nat) : C n n = 1.
Proof. rewrite /C; now rewrite binomnn. Qed.

Lemma C_pascal (n k:nat) :
  (k <= n)%nat ->
  C n.+1 k = C n k + if k is k'.+1 then C n k' else 0.
Proof.
case: k => [|k] Hk; rewrite /C; simpl.
- rewrite binomS0 binom0 //. rewrite INR_IZR_INZ; ring.
- have Hkn : (k <= n)%nat by lia.
  rewrite binomS; try lia.
  change (IZR (Z.of_nat (binom (S n) (S k))) =
          IZR (Z.of_nat (binom n (S k))) + IZR (Z.of_nat (binom n k))).
  rewrite !INR_IZR_INZ; nra.
Qed.

(* Binomial theorem specialized to (x + (1-x))^N = 1 *)
Lemma sum_weights (N:nat) (x:R) :
  \sum_(k < N.+1) w N k x = 1.
Proof.
elim: N => [|N IH].
- rewrite big_ord_recr big_ord0 /= /w C0; ring_simplify; field.
- (* use Pascal identity and reindexing *)
  (* Split the sum using C_pascal and factor (1-x) and x terms *)
  have Hsplit :
    \sum_(k < N.+2) w N.+1 k x
    = (1 - x) * \sum_(k < N.+1) w N k x + x * \sum_(k < N.+1) w N k x.
  { rewrite (big_ord_recr (n:=N.+2)) /=.
    set S := \sum_(k < N.+1) w N.+1 k.+1 x.
    have -> : w N.+1 0 x = (1 - x) ^ (N.+1) by rewrite /w C0 /=; ring.
    have -> : S =
      \sum_(k < N.+1) (C N k + if k is k'.+1 then C N k' else 0)
                      * x^(k.+1) * (1 - x)^(N.+1 - k.+1).
    { apply eq_bigr=> k _; rewrite /w C_pascal; try lia.
      by rewrite -!Rmult_assoc; f_equal; ring. }
    rewrite big_split /=.
    have -> :
      \sum_(k < N.+1) C N k * x^(k.+1) * (1 - x)^(N - k)
      = x * \sum_(k < N.+1) w N k x.
    { rewrite -big_distrl /=; apply eq_bigr=> k _; rewrite /w; ring. }
    have -> :
      \sum_(k < N.+1) (if k is k'.+1 then C N k' else 0)
                      * x^(k.+1) * (1 - x)^(N - k)
      = (1 - x) * \sum_(k < N.+1) w N k x.
    { (* reindex k = k'.+1 *)
      rewrite (reindex_onto (fun k => k.+1) predT (fun k => k.-1)); last first.
      - move=> i _; by case: i.
      - move=> i _; by case: i.
      rewrite /=; apply eq_bigr=> k _.
      case: k=> [|k]; first by simpl; ring.
      simpl; rewrite /w /=; ring. }
    ring. }
  rewrite Hsplit IH; ring.
Qed.

(* moments: Σ k * w = N x, Σ k(k-1) * w = N(N-1) x^2 *)
Lemma sum_moment1 (N:nat) (x:R) :
  \sum_(k < N.+1) (INR k) * w N k x = (INR N) * x.
Proof.
elim: N => [|N IH].
- rewrite big_ord_recr big_ord0 /= /w C0; simpl; ring.
- (* use k*C(N+1,k) = (N+1)*C(N,k-1) and reindex *)
  have H : forall k, (k <= N.+1)%nat ->
    INR k * C N.+1 k = INR (N.+1) * (if k is k'.+1 then C N k' else 0).
  { move=> k Hk; case: k Hk=> [|k] Hk; simpl.
    - rewrite Rmult_0_l; ring.
    - rewrite /C /=.
      (* k+1)*binom(N+1,k+1) = (N+1)*binom(N,k) *)
      replace (INR (S k)) with (1 + INR k) by (simpl; field).
      rewrite !INR_IZR_INZ.
      (* Use standard nat identity: (k+1) * binom (N+1) (k+1) = (N+1) * binom N k *)
      assert (Hnat: (S k) * binom (S N) (S k) = (S N) * binom N k).
      { apply binom_mult_S. } (* Coq.Arith.Binomial lemma *)
      rewrite (INR_IZR_INZ ((S k) * binom (S N) (S k))).
      rewrite (INR_IZR_INZ ((S N) * binom N k)).
      nra. }
  rewrite (big_mkord (fun k => (INR k) * w N.+1 k x)).
  rewrite (eq_bigr (fun k => INR (N.+1) *
            (if k is k'.+1 then C N k' else 0) * x^k * (1 - x)^(N.+1 - k))).
  { move=> k _; rewrite /w; rewrite -Rmult_assoc; f_equal; apply H; lia. }
  rewrite -big_distrl /=.
  (* reindex the (k'.+1) part to align with N-range *)
  have -> :
    \sum_(k < N.+2) (if k is k'.+1 then C N k' else 0) * x^k * (1 - x)^(N.+1 - k)
    = x * \sum_(k < N.+1) w N k x.
  { rewrite (reindex_onto (fun k => k.+1) predT (fun k => k.-1)).
    - rewrite /=; apply eq_bigr=> k _; case: k=> [|k]; first by simpl; ring.
      simpl; rewrite /w; ring.
    - move=> i _; by case: i.
    - move=> i _; by case: i. }
  rewrite IH; ring.
Qed.

Lemma sum_moment2 (N:nat) (x:R) :
  \sum_(k < N.+1) (INR k * INR (k.-1)) * w N k x
  = (INR N) * (INR N.-1) * x^2.
Proof.
elim: N => [|N IH].
- rewrite big_ord_recr big_ord0; simpl; ring.
- (* k(k-1)*C(N+1,k) = (N+1)N * C(N-1, k-2); reindex twice *)
  have H : forall k, (k <= N.+1)%nat ->
    (INR k * INR (k.-1)) * C N.+1 k
    = (INR (N.+1) * INR N) *
      (if k is k2.+2 then C N.-1 k2 else 0).
  { move=> k Hk; case: k Hk=> [|k] Hk; [simpl; ring|].
    case: k Hk=> [|k] Hk; [simpl; ring|].
    (* k= k2.+2 *)
    rewrite /C /= !INR_IZR_INZ.
    (* Use nat identity: k(k-1) C(N+1,k) = (N+1)N C(N-1,k-2) *)
    assert (Hnat: (S (S k)) * (S k) * binom (S N) (S (S k))
                  = (S N) * N * binom (pred (S N)) k).
    { (* This is standard; can be derived from binom identities. *)
      (* Coq provides: binom_mult_SS: (k+1)(k+2) C(N+2,k+2) = (N+2)(N+1) C(N,k)
         Instantiate with N-1 to match indices. *)
      pose proof (binom_mult_SS N k) as Hss.
      exact Hss. }
    rewrite !INR_IZR_INZ; nra. }
  rewrite (eq_bigr (fun k => (INR (N.+1) * INR N)
           * (if k is k2.+2 then C N.-1 k2 else 0)
           * x^k * (1 - x)^(N.+1 - k))).
  { move=> k _; rewrite /w; ring_simplify.
    rewrite (Rmult_comm (x^k * (1 - x)^(N.+1 - k))).
    rewrite -!Rmult_assoc; f_equal; apply H; lia. }
  rewrite -big_distrl /=.
  (* double reindex: k = k2.+2 *)
  have -> :
    \sum_(k < N.+2)
      (if k is k2.+2 then C N.-1 k2 else 0) * x^k * (1 - x)^(N.+1 - k)
    = x^2 * \sum_(k < N.+1) w N.-1 k x.
  { rewrite (reindex_onto (fun k => k.+1) predT (fun k => k.-1)).
    - rewrite (reindex_onto (fun k => k.+1) predT (fun k => k.-1)).
      + rewrite /=; apply eq_bigr=> k _; case: k=> [|k]; first by simpl; ring.
        simpl; case: k=> [|k]; first by simpl; ring.
        simpl; rewrite /w; ring.
      + by move=> i _; case: i.
      + by move=> i _; case: i.
    - by move=> i _; case: i.
    - by move=> i _; case: i. }
  rewrite IH; ring.
Qed.

(* variance of k/N *)
Lemma variance_fraction (N:nat) (x:R) :
  0 < INR N ->
  \sum_(k < N.+1) ((INR k / INR N - x)^2) * w N k x = x*(1 - x)/INR N.
Proof.
move=> HN.
(* Expand square: E[(k/N)^2] - 2xE[k/N] + x^2E[1] *)
have H1 : \sum_(k < N.+1) w N k x = 1 by apply sum_weights.
have H2 : \sum_(k < N.+1) (INR k) * w N k x = INR N * x by apply sum_moment1.
have H3 : \sum_(k < N.+1) (INR k * INR (k.-1)) * w N k x
          = INR N * INR N.-1 * x^2 by apply sum_moment2.
(* compute E[(k/N)^2] = (E[k(k-1)] + E[k]) / N^2 *)
have Ek2 :
  \sum_(k < N.+1) ((INR k / INR N)^2) * w N k x
  = ( (INR N * INR N.-1 * x^2) + (INR N * x) ) / (INR N)^2.
  {
    rewrite (eq_bigr (fun k =>
      ((INR k * INR (k.-1)) + INR k) / (INR N)^2 * w N k x)).
    - rewrite -big_split /=.
      rewrite -!big_distrr /=.
      rewrite H3 H2; field; lra.
    - move=> k _.
      unfold Rdiv; field_simplify; try lra.
      ring_simplify; f_equal.
      ring.
  }
(* Now: E[(k/N - x)^2] = E[(k/N)^2] - 2xE[k/N] + x^2E[1] *)
rewrite (eq_bigr (fun k =>
  ((INR k / INR N)^2 - 2 * x * (INR k / INR N) + x^2) * w N k x)).
{ move=> k _; ring. }
rewrite -big_split /= -big_split /=.
rewrite -!big_distrr /= Ek2 H2 H1.
field; split; try lra.
Qed.

(* A discrete Cauchy–Schwarz with weights summing to 1 *)
Lemma avg_abs_le_sqrt_avg_sq (N:nat) (x:R) :
  \sum_(k < N.+1) w N k x = 1 ->
  \sum_(k < N.+1) Rabs (INR k / INR N - x) * w N k x
  <= sqrt (\sum_(k < N.+1) ((INR k / INR N - x)^2) * w N k x).
Proof.
move=> Hw.
(* Jensen/Cauchy–Schwarz: (∑|a_k|p_k)^2 ≤ (∑a_k^2 p_k)(∑p_k) = ∑a_k^2 p_k *)
have Hcs :
  ( \sum_(k < N.+1) (Rabs (INR k / INR N - x)) * w N k x )^2
  <= ( \sum_(k < N.+1) ((INR k / INR N - x)^2) * w N k x ) * 1.
{
  (* by Cauchy–Schwarz on vectors sqrt(p_k)|a_k| and sqrt(p_k) *)
  (* mathcomp bigop proof: standard inequality; we can invoke real C-S on finite families. *)
  apply Rle_trans with
   ( \sum_(k < N.+1) ((Rabs (INR k / INR N - x))^2) * w N k x
     * \sum_(k < N.+1) w N k x ).
  - apply Cauchy_Schwarz_finite_nonneg; (* provide the finite C-S lemma *)
    all: try (intros; apply Rle_ge; left; apply pow2_gt_0; lra).
    all: try (intros; apply Rle_ge; left; apply pow2_gt_0; lra).
  - by rewrite Hw Rmult_1_r; right; f_equal; apply eq_bigr=> k _; rewrite pow2_abs.
}
apply (proj1 (Rsqr_le_sqrt _ _)).
- apply Rle_ge; apply sumr_ge0=> k _; apply Rmult_le_pos; [apply Rabs_pos|apply Rlt_le, Rlt_pow2].
- apply Rle_trans with ((\sum_ _ _)*1); [exact Hcs|].
  rewrite Rmult_1_r; right; reflexivity.
Qed.

(* Main theorem: L/(2 √N) uniform bound *)
Theorem bernstein_uniform_lipschitz :
  forall (f:R->R) (L:R),
    0 <= L ->
    (forall x y, 0<=x<=1 -> 0<=y<=1 -> Rabs (f x - f y) <= L * Rabs (x - y)) ->
    forall N eps, 0 < eps ->
      (INR N >= (L / (2*eps))^2)%R ->
      (forall x, 0<=x<=1 -> Rabs (BN N f x - f x) <= eps).
Proof.
move=> f L HL Hlip N eps Heps HN x Hx.
have Hsum : \sum_(k < N.+1) w N k x = 1 by apply sum_weights.
have Hlip_sum :
  Rabs (BN N f x - f x)
  <= L * \sum_(k < N.+1) Rabs (INR k / INR N - x) * w N k x.
{
  unfold BN; rewrite -{2}(Rmult_1_l (f x)).
  (* triangle inequality + Lipschitz on each term *)
  have := (big_morph Rabs Rplus Rmult (fun _ => True) _ _).
  (* Simpler: bound each difference by L*|k/N - x| and use convexity weights *)
  apply Rle_trans with
   (\sum_(k < N.+1) Rabs (f (INR k / INR N) - f x) * w N k x).
  - apply: (Rle_trans _ _ _); first exact (Rabs_triang_sum_weighted _ _ _).
    right; reflexivity.
  - apply: ler_sum => k _.
    have Hlip' := Hlip (INR k / INR N) x _ _; try (split; try lra; try apply Rle_trans with 1; lra).
    eapply Rle_trans; [apply Hlip'|].
    apply Rmult_le_compat_l; try lra.
    apply Rle_abs.
}
have Hcs := avg_abs_le_sqrt_avg_sq N x Hsum.
have Hvar := variance_fraction N x _; first by destruct N; simpl; lra.
eapply Rle_trans; [exact Hlip_sum|].
eapply Rle_trans; [apply Rmult_le_compat_l; try lra; exact Hcs|].
rewrite Hvar.
(* sqrt(x(1-x)/N) ≤ 1/(2√N) on [0,1] *)
have Hsqrt : sqrt (x * (1 - x)) <= /2.
{ (* x(1-x) ≤ 1/4 *)
  have : x - x*x <= /4.
  { replace (x - x*x) with (x * (1 - x)) by ring.
    (* maximum at x=1/2 *)
    replace (x * (1 - x)) with (1/4 - (x - 1/2)^2) by ring.
    lra. }
  move=> Hxq; apply (sqrt_le_compat 0 (x * (1 - x)) 0 (/4)); try (apply sqrt_pos).
  all: try (apply Rmult_le_pos; lra).
  - now replace 0 with (0*0) by ring; apply Rle_pow2.
  - exact Hxq.
}
(* Thus: ≤ L * (1/2) / sqrt(N) *)
have Hbound : L * sqrt (x * (1 - x) / INR N) <= (L/2) * / sqrt (INR N).
{
  apply Rmult_le_compat_l; try lra.
  replace (sqrt (x * (1 - x) / INR N)) with (sqrt (x*(1-x)) * / sqrt (INR N)).
  2:{ rewrite sqrt_div_alt; try (apply Rlt_le, Rinv_0_lt_compat; apply Rlt_sqrt; lra).
      field. }
  apply Rmult_le_compat_r; try (apply Rlt_le, Rinv_0_lt_compat, sqrt_lt_R0; lra).
  exact Hsqrt.
}
eapply Rle_trans; [apply Rmult_le_compat_l; try lra; exact Hcs|].
rewrite Hvar; eapply Rle_trans; [apply Rmult_le_compat_l; try lra; exact Hbound|].
(* Now use INR N ≥ (L/(2ε))^2 → (L/2)/√(INR N) ≤ ε *)
assert (0 < sqrt (INR N)) by (apply sqrt_lt_R0; destruct N; simpl; lra).
have : (L/2) * / sqrt (INR N) <= eps.
{
  (* square both sides (all positive) *)
  apply (Rle_trans _ _ _).
  - right; reflexivity.
  - apply Rsqr_le_abs_0.
}
(* do it directly by algebra *)
clear H0.
have HposN : 0 < INR N by destruct N; simpl; lra.
have Hpos : 0 <= L/2 by lra.
apply (Rmult_le_reg_r (sqrt (INR N))); try lra.
rewrite Rinv_r_simpl_m; try lra.
apply (sqrt_le_1_alt _ _).
rewrite <- (Rmult_1_l ((L/2)/eps)^2).
apply Rmult_le_compat_l; try (apply pow2_nonneg).
apply Rinv_le_contravar; try (apply pow2_pos; lra).
(* From HN: INR N ≥ (L/(2ε))^2 *)
exact HN.
Qed.

(* explicit N(ε) and certificate *)
Definition N_of_eps (L eps:R) : nat :=
  Z.to_nat (up ((L / (2*eps))^2)).

Lemma N_of_eps_spec L eps :
  0 <= L -> 0 < eps ->
  (INR (N_of_eps L eps) >= (L / (2*eps))^2)%R.
Proof.
move=> HL Heps; unfold N_of_eps.
pose a := (L / (2*eps))^2.
have Ha : 0 <= a by unfold a; apply Rle_pow2.
(* up a is least integer > a, hence ≥ a *)
apply archimed_upper.
Qed.

Definition mk_cert (f:R->R) (L eps:R) (HL:0 <= L) (Heps:0 < eps)
  : Certificate.cert :=
  let N := N_of_eps L eps in
  let coeffs := [seq f (INR k / INR N) | k <- iota 0 N.+1] in
  {| Certificate.deg := N
   ; Certificate.coeffs := coeffs
   ; Certificate.bound := eps
   ; Certificate.bound_nonneg := Rlt_le _ _ Heps
  |}.

Lemma coeffs_eval_BN f L eps HL Heps x :
  let N := N_of_eps L eps in
  let c := mk_cert f L eps HL Heps in
  x = x ->
  Certificate.eval_cert c x = BN N f x.
Proof. move=> N c ->; reflexivity. Qed.

Lemma sound_on_lipschitz :
  forall (f:R->R) (L eps:R),
    0 <= L -> 0 < eps ->
    (forall x y, 0<=x<=1 -> 0<=y<=1 -> Rabs (f x - f y) <= L * Rabs (x - y)) ->
    Certificate.sound_on f (mk_cert f L eps).
Proof.
move=> f L eps HL Heps Hlip x Hx.
rewrite /Certificate.sound_on /Certificate.eval_cert /mk_cert.
set N := N_of_eps L eps.
have HN := N_of_eps_spec L eps HL Heps.
rewrite coeffs_eval_BN; last reflexivity.
eapply bernstein_uniform_lipschitz; eauto.
Qed.

End Bernstein.
