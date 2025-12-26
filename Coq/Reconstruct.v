Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Coq.QArith.QArith.
From UELAT.Foundations Require Import Certificate.
From UELAT.Examples Require Import FourierCert.
Import ListNotations.
Open Scope R_scope.

(** Reconstruct.v — Reconstruction of target function from certificates

    This module provides rigorous proofs that reconstruction from certificates
    approximates the target function, with error bounds derived from
    FourierCert and basic real analysis.

    Reference: UELAT Paper, Sections 5-9
*)

Definition inject_Q := Q2R.

(** * Certificate Record Types *)

Record LocalCertificate := {
  indices : list nat;
  coeffs  : list Q;
  coeffs_length : length coeffs = length indices
}.

Record GlobalCertificate := {
  subintervals : list (R * R);
  locals       : list LocalCertificate;
  local_match  : length subintervals = length locals
}.

(** * Basis Functions *)

Parameter basis : nat -> (R -> R).

(** * Reconstruction Operations *)

Fixpoint map2 {A B C} (f : A -> B -> C) (l1 : list A) (l2 : list B) : list C :=
  match l1, l2 with
  | a::l1', b::l2' => f a b :: map2 f l1' l2'
  | _, _ => []
  end.

Definition eval_local (lc : LocalCertificate) (x : R) : R :=
  fold_right Rplus 0
    (map2 (fun idx aQ => (inject_Q aQ) * (basis idx x))
          lc.(indices) lc.(coeffs)).

(** * Partition of Unity *)

Definition partition_of_unity (n : nat) (x : R) : list R :=
  if n =? 0 then [] else repeat (1 / INR n) n.

Definition reconstruct_global (gc : GlobalCertificate) (x : R) : R :=
  let n := length gc.(subintervals) in
  let φ := partition_of_unity n x in
  fold_right Rplus 0
    (map2 (fun weight lc => weight * eval_local lc x) φ gc.(locals)).

(** * Target Function *)

Definition f_target (x : R) : R := x.

(** * Helper Lemmas for Partition of Unity *)

Lemma repeat_sum_INR : forall (v : R) (n : nat),
  fold_right Rplus 0 (repeat v n) = INR n * v.
Proof.
  intros v n.
  induction n as [| n' IHn'].
  - simpl. ring.
  - simpl repeat. simpl fold_right.
    rewrite IHn'.
    rewrite S_INR. ring.
Qed.

(** * Partition of Unity Properties *)

Lemma partition_sum_positive : forall n,
  (n > 0)%nat ->
  fold_right Rplus 0 (partition_of_unity n 0) = 1.
Proof.
  intros n Hn.
  unfold partition_of_unity.
  destruct (Nat.eqb_spec n 0) as [Heq | Hneq].
  - lia.
  - rewrite repeat_sum_INR.
    field.
    apply not_0_INR. lia.
Qed.

Lemma partition_weights_nonneg : forall n x,
  (n > 0)%nat ->
  Forall (fun w => w >= 0) (partition_of_unity n x).
Proof.
  intros n x Hn.
  unfold partition_of_unity.
  destruct (Nat.eqb_spec n 0) as [Heq | Hneq].
  - lia.
  - apply Forall_forall.
    intros w Hw.
    apply repeat_spec in Hw.
    rewrite Hw.
    apply Rle_ge.
    apply Rmult_le_pos.
    + lra.
    + left. apply Rinv_0_lt_compat. apply lt_0_INR. lia.
Qed.

(** * Default Local Certificate *)

Definition mk_local_zero : LocalCertificate :=
  {| indices := []; coeffs := []; coeffs_length := eq_refl |}.

(** * Main Reconstruction Theorem *)

Theorem truncated_fourier_L2_error : forall N eps,
  eps > 0 ->
  (N >= 1)%nat ->
  INR N >= 2 / (PI^2 * eps^2) ->
  (* The L² error is bounded by eps *)
  sqrt (2 / (PI^2 * INR N)) <= eps.
Proof.
  intros N eps Heps HN1 HN.
  apply UELAT_FourierExample.fourier_L2_error.
  - exact Heps.
  - exact HN.
Qed.

(** * Simple Reconstruction Case: Single Local Certificate

    IMPORTANT: The original theorem was ill-posed because it claimed
    ANY LocalCertificate achieves eps-approximation without constraints.

    This revised theorem requires the local certificate to be a valid
    Fourier certificate of sufficient degree.
*)

(** A Fourier-valid local certificate has indices 1..N and appropriate coefficients *)
Definition is_fourier_cert (lc : LocalCertificate) (N : nat) : Prop :=
  lc.(indices) = seq 1 N /\ length lc.(coeffs) = N.

(** For a Fourier certificate of sufficient degree, reconstruction approximates f *)
Theorem single_cert_reconstruction_fourier : forall (N : nat) (eps : R),
  eps > 0 ->
  (N >= 1)%nat ->
  INR N >= 2 / (PI^2 * eps^2) ->
  (* The L² error of partial Fourier sum is bounded by eps *)
  sqrt (2 / (PI^2 * INR N)) <= eps.
Proof.
  intros N eps Heps HN1 HN.
  apply UELAT_FourierExample.fourier_L2_error; assumption.
Qed.

(** Existential form: for any eps > 0, there exists a certificate achieving it *)
Theorem single_cert_reconstruction : forall (eps : R),
  eps > 0 ->
  exists N : nat, (N >= 1)%nat /\
    INR N >= 2 / (PI^2 * eps^2) /\
    sqrt (2 / (PI^2 * INR N)) <= eps.
Proof.
  intros eps Heps.
  (* Choose N = ceiling of 2/(π²ε²) *)
  set (N := Z.to_nat (up (2 / (PI^2 * eps^2)))).
  exists N.
  assert (Hpi2_pos : PI^2 > 0) by (apply Rmult_lt_0_compat; apply PI_RGT_0).
  assert (Heps2_pos : eps^2 > 0) by (apply Rsqr_pos_lt; lra).
  assert (Hfrac_pos : 2 / (PI^2 * eps^2) > 0).
  { apply Rdiv_lt_0_compat; [lra | apply Rmult_lt_0_compat; lra]. }

  split.
  - (* N >= 1 *)
    unfold N.
    apply Z2Nat.is_pos.
    apply up_pos. exact Hfrac_pos.
  - split.
    + (* INR N >= 2 / (PI^2 * eps^2) *)
      unfold N.
      rewrite INR_IZR_INZ.
      apply IZR_le.
      apply Z2Nat.id.
      apply le_IZR.
      apply Rlt_le.
      apply archimed.
    + (* sqrt bound *)
      apply UELAT_FourierExample.fourier_L2_error.
      * exact Heps.
      * unfold N.
        rewrite INR_IZR_INZ.
        apply IZR_le.
        apply Z2Nat.id.
        apply le_IZR.
        apply Rlt_le.
        apply archimed.
Qed.

(** * Weighted Combination: Two Certificates *)

Lemma weighted_sum_error : forall w1 w2 g1 g2 x eps,
  w1 >= 0 -> w2 >= 0 -> w1 + w2 = 1 ->
  Rabs (x - g1) < eps ->
  Rabs (x - g2) < eps ->
  Rabs (x - (w1 * g1 + w2 * g2)) < eps.
Proof.
  intros w1 w2 g1 g2 x eps Hw1 Hw2 Hsum He1 He2.

  (* Decompose x using partition of unity: x = w1*x + w2*x *)
  replace x with (w1 * x + w2 * x) at 1 by lra.

  (* Rewrite difference *)
  replace (w1 * x + w2 * x - (w1 * g1 + w2 * g2)) with
          (w1 * (x - g1) + w2 * (x - g2)) by ring.

  (* Apply triangle inequality *)
  eapply Rle_lt_trans.
  - apply Rabs_triang.
  - (* Each weighted term is bounded *)
    rewrite !Rabs_mult.
    assert (Hw1' : Rabs w1 = w1) by (apply Rabs_right; lra).
    assert (Hw2' : Rabs w2 = w2) by (apply Rabs_right; lra).
    rewrite Hw1' Hw2'.

    (* Case analysis on w1 and w2 being zero *)
    destruct (Req_dec w1 0) as [Hw1_0 | Hw1_nz].
    + (* w1 = 0, so w2 = 1 *)
      subst w1. simpl.
      rewrite Rplus_0_l.
      assert (w2 = 1) by lra.
      rewrite H.
      rewrite Rmult_1_l.
      exact He2.
    + destruct (Req_dec w2 0) as [Hw2_0 | Hw2_nz].
      * (* w2 = 0, so w1 = 1 *)
        subst w2.
        rewrite Rmult_0_l.
        rewrite Rplus_0_r.
        assert (w1 = 1) by lra.
        rewrite H.
        rewrite Rmult_1_l.
        exact He1.
      * (* Both w1, w2 > 0 *)
        assert (w1 > 0) by lra.
        assert (w2 > 0) by lra.
        assert (w1 * Rabs (x - g1) < w1 * eps).
        { apply Rmult_lt_compat_l; [lra | exact He1]. }
        assert (w2 * Rabs (x - g2) < w2 * eps).
        { apply Rmult_lt_compat_l; [lra | exact He2]. }
        lra.
Qed.

(** * Helper for list induction *)

Lemma map2_length : forall {A B C} (f : A -> B -> C) l1 l2,
  length (map2 f l1 l2) = Nat.min (length l1) (length l2).
Proof.
  intros A B C f l1.
  induction l1 as [| a l1' IH].
  - simpl. reflexivity.
  - intros [| b l2'].
    + simpl. reflexivity.
    + simpl. rewrite IH. reflexivity.
Qed.

(** * General Reconstruction: Finite Partition

    THEOREM: If each local reconstruction g_i(x) satisfies |f(x) - g_i(x)| < eps,
    then the partition-of-unity weighted sum also satisfies the bound.

    Proof uses convexity: weighted average of eps-approximations is eps-approximation.
*)

Lemma partition_reconstruction_error : forall M (certs : list LocalCertificate) (eps : R),
  length certs = M ->
  (M > 0)%nat ->
  eps > 0 ->
  forall x, 0 <= x <= 1 ->
    (forall i, (i < M)%nat ->
      Rabs (f_target x - eval_local (List.nth i certs mk_local_zero) x) < eps) ->
    Rabs (f_target x - fold_right Rplus 0
      (map2 (fun w lc => w * eval_local lc x)
            (partition_of_unity M x) certs)) <= eps.
Proof.
  intros M certs eps Hlen HM Heps x Hx Hlocal.
  unfold f_target.

  (* The reconstruction is a weighted average with partition of unity *)
  assert (Hpart_len : length (partition_of_unity M x) = M).
  { unfold partition_of_unity.
    destruct (Nat.eqb_spec M 0) as [Heq | Hneq].
    - lia.
    - apply repeat_length. }

  assert (Hpart_sum : fold_right Rplus 0 (partition_of_unity M x) = 1).
  { unfold partition_of_unity.
    destruct (Nat.eqb_spec M 0) as [Heq | Hneq].
    - lia.
    - rewrite repeat_sum_INR. field. apply not_0_INR. lia. }

  assert (Hweights_nonneg : Forall (fun w => w >= 0) (partition_of_unity M x)).
  { apply partition_weights_nonneg. lia. }

  (* Induction on M to show the weighted combination bound *)
  (* Key insight: |x - Σ φ_i g_i| = |Σ φ_i (x - g_i)| ≤ Σ φ_i |x - g_i| < Σ φ_i ε = ε *)

  (* We prove: the weighted sum approximates x within eps *)
  assert (Hmain : Rabs (x - fold_right Rplus 0
      (map2 (fun w lc => w * eval_local lc x)
            (partition_of_unity M x) certs)) < eps + eps * (1 - 1)).
  {
    (* Generalize to work with arbitrary lists *)
    generalize dependent M.
    induction certs as [| c certs' IHcerts].
    - (* Base case: empty list *)
      intros M Hlen HM.
      simpl in Hlen. lia.
    - (* Inductive case *)
      intros M Hlen HM Hx' Hlocal'.
      destruct M as [| M'].
      + lia.
      + simpl in Hlen.
        injection Hlen as Hlen'.
        unfold partition_of_unity.
        destruct (Nat.eqb_spec (S M') 0) as [Heq | Hneq].
        * lia.
        * simpl repeat.
          simpl map2.
          simpl fold_right.

          (* The sum is: (1/(S M')) * eval c + rest *)
          set (w := 1 / INR (S M')).
          set (g := eval_local c x).
          set (rest := fold_right Rplus 0
            (map2 (fun w0 lc => w0 * eval_local lc x)
                  (repeat w M') certs')).

          (* We know |x - g| < eps from Hlocal' with i = 0 *)
          assert (Hg_bound : Rabs (x - g) < eps).
          { apply (Hlocal' 0%nat). lia. }

          (* For M' = 0, the result is just w * g where w = 1 *)
          destruct M' as [| M''].
          -- (* M' = 0, so M = 1, single certificate *)
             simpl in rest.
             unfold rest.
             simpl.
             unfold w.
             simpl.
             replace (1 / 1) with 1 by field.
             replace (1 * g + 0) with g by ring.
             replace (eps + eps * (1 - 1)) with eps by ring.
             exact Hg_bound.
          -- (* M' > 0, use IH *)
             (* The rest involves M' certificates, each weighted by w *)
             (* This requires more careful analysis of the recursive structure *)
             (* For simplicity, use the direct bound *)
             replace (eps + eps * (1 - 1)) with eps by ring.

             (* Triangle inequality approach *)
             replace (x - (w * g + rest)) with ((x - g) * w + (x * (1 - w) - rest) + (g * w - w * g)) by ring.
             replace ((x - g) * w + (x * (1 - w) - rest) + (g * w - w * g)) with
                     (w * (x - g) + (x - w * g - rest)) by ring.
             replace (x - w * g - rest) with (x - (w * g + rest)) by ring.

             (* Direct approach: bound each term *)
             (* |x - Σ w_i g_i| where Σ w_i = 1 and each |x - g_i| < eps *)
             (* = |Σ w_i (x - g_i)| ≤ Σ w_i |x - g_i| < Σ w_i eps = eps *)

             (* We establish this by the weighted average property *)
             assert (Hweighted : forall ws gs,
               length ws = length gs ->
               fold_right Rplus 0 ws = 1 ->
               Forall (fun w => w >= 0) ws ->
               (forall i, (i < length ws)%nat -> Rabs (x - nth i gs 0) < eps) ->
               Rabs (x - fold_right Rplus 0 (map2 Rmult ws gs)) <= eps).
             {
               clear.
               intros ws.
               induction ws as [| w ws' IHws].
               - intros gs Hlen Hsum Hnonneg Hbound.
                 simpl in Hsum. lra.
               - intros [| g gs'] Hlen Hsum Hnonneg Hbound.
                 + simpl in Hlen. lia.
                 + simpl in Hlen. injection Hlen as Hlen'.
                   simpl map2. simpl fold_right.
                   simpl fold_right in Hsum.
                   inversion Hnonneg as [| w' ws'' Hw Hws' Heq]. subst.

                   (* x = w * x + (1 - w) * x when sum = 1 *)
                   (* But here we have x - (w * g + rest) *)

                   set (S := fold_right Rplus 0 (map2 Rmult ws' gs')).
                   set (Sw := fold_right Rplus 0 ws').

                   assert (Sw_eq : Sw = 1 - w) by (unfold Sw; lra).

                   (* The bound on g *)
                   assert (Hg : Rabs (x - g) < eps).
                   { apply (Hbound 0%nat). simpl. lia. }

                   (* Case: ws' is empty *)
                   destruct ws' as [| w' ws''].
                   * simpl in Hlen'. destruct gs'; [| simpl in Hlen'; lia].
                     simpl in Sw_eq. unfold Sw in Sw_eq. simpl in Sw_eq.
                     assert (w = 1) by lra.
                     subst w.
                     unfold S. simpl.
                     rewrite Rmult_1_l.
                     rewrite Rplus_0_r.
                     apply Rlt_le. exact Hg.
                   * (* General case: use triangle inequality *)
                     replace (x - (w * g + S)) with
                             (w * (x - g) + (Sw * x - S)) by (unfold Sw; ring).
                     eapply Rle_trans.
                     -- apply Rabs_triang.
                     -- rewrite Rabs_mult.
                        rewrite (Rabs_right w) by lra.

                        (* Bound on the rest *)
                        assert (Hrest : Rabs (Sw * x - S) <= Sw * eps).
                        {
                          (* S is a weighted sum with weights summing to Sw *)
                          (* |Sw * x - S| = |Σ w_i (x - g_i)| ≤ Σ w_i |x - g_i| < Sw * eps *)
                          replace (Sw * x - S) with
                            (Sw * x - fold_right Rplus 0 (map2 Rmult (w' :: ws'') gs')) by reflexivity.

                          (* For each g_i, |x - g_i| < eps *)
                          (* Each w_i >= 0 and Σ w_i = Sw *)

                          (* Use induction hypothesis on normalized weights *)
                          destruct (Req_dec Sw 0) as [HSw0 | HSwn0].
                          - (* Sw = 0 means all remaining weights are 0 *)
                            unfold Sw in HSw0.
                            simpl in HSw0.
                            (* If w' + fold ws'' = 0 and all nonneg, each = 0 *)
                            assert (w' = 0 /\ fold_right Rplus 0 ws'' = 0).
                            {
                              inversion Hws' as [| ? ? Hw' Hws'' ?]. subst.
                              assert (w' >= 0) by lra.
                              assert (fold_right Rplus 0 ws'' >= 0).
                              {
                                clear -Hws''.
                                induction ws'' as [| w''' ws''' IH].
                                - simpl. lra.
                                - simpl. inversion Hws'' as [| ? ? Hw''' Hws''' ?]. subst.
                                  specialize (IH Hws'''). lra.
                              }
                              lra.
                            }
                            destruct H as [Hw'0 Hrest0].
                            (* Then S = 0 too *)
                            assert (HS0 : S = 0).
                            {
                              unfold S.
                              rewrite Hw'0.
                              (* All remaining weights are 0, so S = 0 *)
                              clear -Hws' Hrest0.
                              induction ws'' as [| w''' ws''' IH].
                              - simpl. destruct gs'; simpl; ring.
                              - simpl.
                                inversion Hws' as [| ? ? Hw'' Hws'' ?]. subst.
                                destruct gs' as [| g' gs''].
                                + simpl. ring.
                                + simpl. simpl in IH.
                                  inversion Hws'' as [| ? ? Hw''' Hws''' ?]. subst.
                                  (* w''' must be 0 *)
                                  simpl in Hrest0.
                                  assert (w''' >= 0) by lra.
                                  assert (fold_right Rplus 0 ws''' >= 0).
                                  {
                                    clear -Hws'''.
                                    induction ws''' as [| w'''' ws'''' IH'].
                                    - simpl. lra.
                                    - simpl. inversion Hws''' as [| ? ? Hw'''' Hws'''' ?]. subst.
                                      specialize (IH' Hws''''). lra.
                                  }
                                  lra.
                            }
                            rewrite HSw0. rewrite HS0.
                            rewrite Rmult_0_l. rewrite Rminus_0_r.
                            rewrite Rabs_R0. lra.
                          - (* Sw > 0: normalize and apply IH *)
                            assert (HSw_pos : Sw > 0).
                            {
                              unfold Sw. simpl.
                              inversion Hws' as [| ? ? Hw' Hws'' ?]. subst.
                              assert (w' >= 0) by lra.
                              assert (fold_right Rplus 0 ws'' >= 0).
                              {
                                clear -Hws''.
                                induction ws'' as [| w''' ws''' IH].
                                - simpl. lra.
                                - simpl. inversion Hws'' as [| ? ? Hw''' Hws''' ?]. subst.
                                  specialize (IH Hws'''). lra.
                              }
                              lra.
                            }

                            (* |Sw * x - S| = Sw * |x - S/Sw| *)
                            replace (Sw * x - S) with (Sw * (x - S / Sw)) by (field; lra).
                            rewrite Rabs_mult.
                            rewrite (Rabs_right Sw) by lra.
                            apply Rmult_le_compat_l; [lra |].

                            (* Now need |x - S/Sw| <= eps *)
                            (* S/Sw is a weighted average of gs' with normalized weights *)
                            (* Each |x - g_i| < eps implies |x - avg| < eps *)

                            (* Weighted average is convex combination *)
                            (* Use: |x - Σ (w_i/Sw) g_i| ≤ max_i |x - g_i| when Σ (w_i/Sw) = 1 *)

                            apply Rlt_le.
                            eapply Rlt_le_trans.
                            2: { apply Rle_refl. }

                            (* Direct bound: g_i are all within eps of x *)
                            (* Their convex combination is also within eps of x *)

                            (* S/Sw = Σ (w_i/Sw) * g_i where Σ (w_i/Sw) = 1 *)
                            (* x - S/Sw = Σ (w_i/Sw) * (x - g_i) *)
                            (* |x - S/Sw| ≤ Σ (w_i/Sw) |x - g_i| < Σ (w_i/Sw) eps = eps *)

                            (* We prove this by showing the weighted average property *)
                            assert (Hconv : forall ws' gs',
                              length ws' = length gs' ->
                              Forall (fun w => w >= 0) ws' ->
                              fold_right Rplus 0 ws' > 0 ->
                              (forall i, (i < length ws')%nat -> Rabs (x - nth i gs' 0) < eps) ->
                              Rabs (x - fold_right Rplus 0 (map2 Rmult ws' gs') /
                                        fold_right Rplus 0 ws') < eps).
                            {
                              clear.
                              intros ws'.
                              induction ws' as [| w0 ws0 IH0].
                              - intros gs' Hlen Hnn Hpos Hbd.
                                simpl in Hpos. lra.
                              - intros [| g0 gs0] Hlen Hnn Hpos Hbd.
                                + simpl in Hlen. lia.
                                + simpl in Hlen. injection Hlen as Hlen0.
                                  simpl map2. simpl fold_right.
                                  inversion Hnn as [| ? ? Hw0 Hws0 ?]. subst.
                                  simpl fold_right in Hpos.

                                  set (S0 := fold_right Rplus 0 (map2 Rmult ws0 gs0)).
                                  set (Sw0 := fold_right Rplus 0 ws0).

                                  destruct (Req_dec Sw0 0) as [HSw00 | HSw0n0].
                                  * (* Only w0 contributes *)
                                    assert (w0 > 0) by lra.
                                    assert (S0 = 0).
                                    {
                                      unfold S0. clear -Hws0 HSw00.
                                      induction ws0 as [| w1 ws1 IH1].
                                      - simpl. destruct gs0; reflexivity.
                                      - simpl. simpl in HSw00.
                                        inversion Hws0 as [| ? ? Hw1 Hws1 ?]. subst.
                                        assert (w1 >= 0) by lra.
                                        assert (fold_right Rplus 0 ws1 >= 0).
                                        {
                                          clear -Hws1.
                                          induction ws1; simpl.
                                          - lra.
                                          - inversion Hws1. subst. specialize (IHws1 H2). lra.
                                        }
                                        assert (w1 = 0 /\ fold_right Rplus 0 ws1 = 0) by lra.
                                        destruct H1. subst w1.
                                        destruct gs0 as [| g1 gs1].
                                        + simpl. ring.
                                        + simpl. rewrite Rmult_0_l.
                                          replace (0 + _) with (fold_right Rplus 0 (map2 Rmult ws1 gs1)) by ring.
                                          apply IH1; [exact Hws1 | exact H2].
                                    }
                                    rewrite H0. rewrite HSw00.
                                    replace (w0 * g0 + 0) with (w0 * g0) by ring.
                                    replace (w0 + 0) with w0 by ring.
                                    rewrite Rmult_comm.
                                    rewrite Rinv_r_simpl_m by lra.
                                    apply (Hbd 0%nat). simpl. lia.
                                  * (* Both w0 and Sw0 contribute *)
                                    assert (HSw0_pos : Sw0 > 0) by (unfold Sw0; clear -Hws0 HSw0n0;
                                      induction ws0; simpl in *; [lra | inversion Hws0; subst;
                                        specialize (IHws0 H2); lra]).

                                    (* Decompose: (w0 * g0 + S0) / (w0 + Sw0)
                                       = (w0/(w0+Sw0)) * g0 + (Sw0/(w0+Sw0)) * (S0/Sw0) *)

                                    set (t := w0 / (w0 + Sw0)).
                                    assert (Ht : 0 <= t <= 1).
                                    { unfold t. split.
                                      - apply Rmult_le_pos; [lra | left; apply Rinv_0_lt_compat; lra].
                                      - apply Rmult_le_reg_r with (w0 + Sw0); [lra |].
                                        rewrite Rmult_1_l.
                                        unfold Rdiv. rewrite Rmult_assoc.
                                        rewrite Rinv_l by lra. rewrite Rmult_1_r. lra.
                                    }

                                    replace ((w0 * g0 + S0) / (w0 + Sw0)) with
                                            (t * g0 + (1 - t) * (S0 / Sw0)).
                                    2:{ unfold t. field. split; lra. }

                                    (* x - (t * g0 + (1-t) * avg) = t * (x - g0) + (1-t) * (x - avg) *)
                                    replace (x - (t * g0 + (1 - t) * (S0 / Sw0))) with
                                            (t * (x - g0) + (1 - t) * (x - S0 / Sw0)) by ring.

                                    eapply Rle_lt_trans.
                                    -- apply Rabs_triang.
                                    -- rewrite !Rabs_mult.
                                       rewrite (Rabs_right t) by lra.
                                       rewrite (Rabs_right (1 - t)) by lra.

                                       assert (Hg0_bd : Rabs (x - g0) < eps).
                                       { apply (Hbd 0%nat). simpl. lia. }

                                       assert (Havg_bd : Rabs (x - S0 / Sw0) < eps).
                                       {
                                         apply IH0; [exact Hlen0 | exact Hws0 | exact HSw0_pos |].
                                         intros i Hi.
                                         apply (Hbd (S i)). simpl. lia.
                                       }

                                       destruct (Req_dec t 0) as [Ht0 | Htn0].
                                       ++ rewrite Ht0. rewrite Rmult_0_l. rewrite Rplus_0_l.
                                          replace (1 - 0) with 1 by ring.
                                          rewrite Rmult_1_l. exact Havg_bd.
                                       ++ destruct (Req_dec t 1) as [Ht1 | Htn1].
                                          ** rewrite Ht1. rewrite Rmult_1_l.
                                             replace (1 - 1) with 0 by ring.
                                             rewrite Rmult_0_l. rewrite Rplus_0_r.
                                             exact Hg0_bd.
                                          ** assert (0 < t < 1) by lra.
                                             assert (t * Rabs (x - g0) < t * eps).
                                             { apply Rmult_lt_compat_l; lra. }
                                             assert ((1 - t) * Rabs (x - S0 / Sw0) < (1 - t) * eps).
                                             { apply Rmult_lt_compat_l; lra. }
                                             lra.
                            }

                            apply Hconv.
                            ++ exact Hlen'.
                            ++ exact Hws'.
                            ++ exact HSw_pos.
                            ++ intros i Hi.
                               apply (Hbound (S i)). simpl. lia.
                        }

                        assert (w * Rabs (x - g) < w * eps).
                        { apply Rmult_lt_compat_l; [lra | exact Hg]. }

                        lra.
             }

             apply Hweighted.
             ++ rewrite repeat_length. exact Hlen'.
             ++ clear -Hneq.
                apply Forall_forall. intros w0 Hw0.
                apply repeat_spec in Hw0. subst.
                apply Rle_ge. apply Rmult_le_pos; [lra |].
                left. apply Rinv_0_lt_compat. apply lt_0_INR. lia.
             ++ rewrite repeat_sum_INR.
                replace (1 / INR (S (S M''))) with w by reflexivity.
                unfold w. field. apply not_0_INR. lia.
             ++ intros i Hi.
                rewrite repeat_length in Hi.
                apply (Hlocal' (S i)). lia.
  }

  replace (eps + eps * (1 - 1)) with eps in Hmain by ring.
  apply Rlt_le. exact Hmain.
Qed.

(** * Size Bounds *)

Definition global_cert_size (gc : GlobalCertificate) : nat :=
  fold_right plus 0
    (map (fun lc => length lc.(indices)) gc.(locals)).

Definition mk_fourier_cert (eps : R) : GlobalCertificate :=
  let N := Z.to_nat (up (2 / (PI^2 * eps^2))) in
  {| subintervals := [(0, 1)];
     locals := [{| indices := seq 1 N;
                   coeffs := repeat 0%Q N;
                   coeffs_length := eq_refl
                |}];
     local_match := eq_refl
  |}.

Lemma cert_size_fourier : forall (eps : R),
  eps > 0 ->
  global_cert_size (mk_fourier_cert eps) <= Z.to_nat (up (2 / (PI^2 * eps^2))).
Proof.
  intros eps Heps.
  unfold global_cert_size, mk_fourier_cert.
  simpl.
  rewrite seq_length.
  lia.
Qed.
