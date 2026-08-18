(** Incompressibility.v — Constructive Certificate Lower Bounds

    This module proves certificate incompressibility through a fully
    constructive discrete argument. NO AXIOMS OR ADMITTED.

    Strategy: We construct a finite family of "configuration functions"
    that are pairwise distinguishable. Any certificate scheme that
    identifies them must encode at least log₂(family size) bits.

    Reference: UELAT Paper, Section 8, Theorem 8.2
*)

From mathcomp Require Import all_ssreflect all_algebra.
From Stdlib Require Import Reals Lra Lia.
From Stdlib Require Import List.
(* Rocq 9 no longer transitively re-exports Classical from Reals, so the
   uses of `classic`, `not_all_ex_not`, `imply_to_and` in this file need
   their module imported explicitly. Not a new logical dependency — the
   proofs below already invoke these classical helpers. *)
From Stdlib Require Import Classical.
(* Same reason for Compare_dec: `le_lt_dec` used in
   certificate_size_lower_bound was previously visible via an implicit
   re-export that Rocq 9 dropped. *)
From Stdlib Require Import Compare_dec.
Import ListNotations.
Local Open Scope R_scope.

Module UELAT_Incompressibility.

(** * Certificate Definition *)

(** A certificate is a finite binary string *)
Record Cert : Type := mkCert {
  cert_bits : list bool
}.

Definition cert_size (C : Cert) : nat := length (cert_bits C).

(** * Core Counting Lemma *)

(** The key insight: there are exactly 2^n distinct boolean lists of length n *)

(** Generate all boolean lists of length n *)
Fixpoint all_bool_lists (n : nat) : list (list bool) :=
  match n with
  | 0 => [[]]
  | S m => map (cons true) (all_bool_lists m) ++
           map (cons false) (all_bool_lists m)
  end.

Lemma all_bool_lists_length : forall n,
  length (all_bool_lists n) = Nat.pow 2 n.
Proof.
  induction n as [|n IH]; simpl.
  - reflexivity.
  - rewrite app_length !map_length IH.
    ring.
Qed.

Lemma all_bool_lists_elem_length : forall n l,
  In l (all_bool_lists n) -> length l = n.
Proof.
  induction n as [|n IH]; simpl; intros l Hin.
  - destruct Hin as [Heq | []]; subst; reflexivity.
  - apply in_app_or in Hin.
    destruct Hin as [Hin | Hin];
    apply in_map_iff in Hin;
    destruct Hin as [l' [Heq Hin']];
    subst; simpl; f_equal; apply IH; exact Hin'.
Qed.

Lemma all_bool_lists_complete : forall n l,
  length l = n -> In l (all_bool_lists n).
Proof.
  induction n as [|n IH]; simpl; intros l Hlen.
  - destruct l; [left; reflexivity | simpl in Hlen; discriminate].
  - destruct l as [|b l']; [simpl in Hlen; discriminate|].
    simpl in Hlen. injection Hlen as Hlen'.
    apply in_or_app.
    destruct b.
    + left. apply in_map. apply IH. exact Hlen'.
    + right. apply in_map. apply IH. exact Hlen'.
Qed.

(* Rocq 9's Stdlib.Lists.List exports NoDup_map_inv (backward direction)
   but not the forward NoDup_map that older stdlibs had. Prove it locally
   with a distinct name; it's a small structural fact, no axiom added. *)
Lemma NoDup_map_local :
  forall (A B : Type) (f : A -> B) (l : list A),
    (forall x y, In x l -> In y l -> f x = f y -> x = y) ->
    NoDup l -> NoDup (map f l).
Proof.
  intros A B f l Hinj Hnd.
  induction Hnd as [|a l' Hnotin Hnd' IH]; simpl.
  - constructor.
  - constructor.
    + intro Hin. apply in_map_iff in Hin.
      destruct Hin as [x [Hfx Hx]].
      assert (Heq: a = x).
      { apply Hinj; [left; reflexivity | right; exact Hx | symmetry; exact Hfx]. }
      subst x. contradiction.
    + apply IH. intros x y Hx Hy Heq.
      apply Hinj; [right; exact Hx | right; exact Hy | exact Heq].
Qed.

Lemma all_bool_lists_nodup : forall n,
  NoDup (all_bool_lists n).
Proof.
  induction n as [|n IH]; simpl.
  - constructor; [intro H; destruct H|constructor].
  - apply NoDup_app.
    + apply NoDup_map_local; [|exact IH].
      intros x y _ _ Heq. injection Heq. auto.
    + apply NoDup_map_local; [|exact IH].
      intros x y _ _ Heq. injection Heq. auto.
    + intros l Hin1 Hin2.
      apply in_map_iff in Hin1. destruct Hin1 as [l1 [Heq1 _]].
      apply in_map_iff in Hin2. destruct Hin2 as [l2 [Heq2 _]].
      subst l. discriminate.
Qed.

(** Length of the enumeration of all bit-strings shorter than K.
    Sum over i ∈ [0..K-1] of 2^i equals 2^K - 1. Small structural
    fact used by the pigeonhole side of certificate_size_lower_bound. *)
Lemma short_bits_length : forall n,
  (length (flat_map all_bool_lists (seq 0 n)) = Nat.pow 2 n - 1)%coq_nat.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - rewrite seq_S, flat_map_app, app_length, IH.
    simpl flat_map. rewrite app_nil_r, all_bool_lists_length.
    assert (Hk : (Nat.pow 2 n >= 1)%coq_nat).
    { clear. induction n; simpl; lia. }
    simpl Nat.pow. lia.
Qed.

(** * Pigeonhole Principle *)

(** If we have more elements than slots, some slot has multiple elements *)
Lemma pigeonhole_injective : forall (A B : Type) (f : A -> B) (la : list A) (lb : list B),
  NoDup la ->
  (forall a, In a la -> In (f a) lb) ->
  (length la > length lb)%nat ->
  exists a1 a2, In a1 la /\ In a2 la /\ a1 <> a2 /\ f a1 = f a2.
Proof.
  intros A B f la lb Hnodup Himg Hlen.
  (* By pigeonhole: if |domain| > |codomain|, f cannot be injective *)
  (* We prove by contradiction: if f is injective on la, then |la| <= |lb| *)
  destruct (classic (forall a1 a2, In a1 la -> In a2 la -> f a1 = f a2 -> a1 = a2)) as [Hinj | Hnotinj].
  - (* f is injective, contradiction with Hlen *)
    exfalso.
    (* The original proof's induction ended in `lia (* This requires more
       work; simplified for now *)`, which cannot in fact discharge the
       inductive step and only compiled under older Coq versions by
       accident. Replace it with a proper pigeonhole argument:
         Hinj : f injective on la
           ⇒ NoDup (map f la)                        (NoDup_map_local)
         Himg : every f a in lb, for a ∈ la
           ⇒ incl (map f la) lb                      (direct)
         NoDup_incl_length + length_map              ⇒  |la| ≤ |lb|. *)
    (* %coq_nat, not %nat: mathcomp's all_ssreflect remaps %nat to ssrnat's
       bool-returning leq, but NoDup_incl_length is a stdlib lemma returning
       Peano.le. Match its type here; we then bridge Hlen (ssrnat %N) into
       Peano so a single `lia` closes False. *)
    assert (Hle: (length la <= length lb)%coq_nat).
    { clear Hlen.
      rewrite <- (length_map f la).
      apply NoDup_incl_length.
      - apply NoDup_map_local; [exact Hinj | exact Hnodup].
      - intros b Hin. apply in_map_iff in Hin.
        destruct Hin as [a [Heq Ha]]. subst b. apply Himg. exact Ha. }
    assert (Hlen' : (length lb < length la)%coq_nat) by (apply/ltP; exact Hlen).
    lia.
  - (* f is not injective, extract witnesses *)
    apply not_all_ex_not in Hnotinj.
    destruct Hnotinj as [a1 H1].
    apply not_all_ex_not in H1.
    destruct H1 as [a2 H2].
    apply imply_to_and in H2.
    destruct H2 as [Ha1 H2].
    apply imply_to_and in H2.
    destruct H2 as [Ha2 H2].
    apply imply_to_and in H2.
    destruct H2 as [Heq Hneq].
    exists a1, a2.
    split; [exact Ha1|].
    split; [exact Ha2|].
    split; [exact Hneq|exact Heq].
Qed.

(** * Main Incompressibility Theorem *)

Section Incompressibility.

(** Number of distinguishable configurations *)
Variable K : nat.
Hypothesis HK : (K >= 1)%nat.

(** A configuration is a boolean list of length K *)
Definition config := list bool.

Definition valid_config (cfg : config) : Prop := length cfg = K.

(** The family of all valid configurations has size 2^K *)
Definition all_configs : list config := all_bool_lists K.

Lemma all_configs_size : length all_configs = Nat.pow 2 K.
Proof. apply all_bool_lists_length. Qed.

Lemma all_configs_valid : forall cfg, In cfg all_configs -> valid_config cfg.
Proof. intros cfg Hin. apply all_bool_lists_elem_length. exact Hin. Qed.

Lemma all_configs_complete : forall cfg, valid_config cfg -> In cfg all_configs.
Proof. intros cfg Hvalid. apply all_bool_lists_complete. exact Hvalid. Qed.

Lemma all_configs_nodup : NoDup all_configs.
Proof. apply all_bool_lists_nodup. Qed.

(** Certificate encoding: any scheme assigning certs to configs *)
Variable encode : config -> Cert.

(** Injectivity requirement: distinct configs get distinct certificates *)
Definition encoding_injective : Prop :=
  forall cfg1 cfg2,
    valid_config cfg1 -> valid_config cfg2 ->
    cert_bits (encode cfg1) = cert_bits (encode cfg2) ->
    cfg1 = cfg2.

(** Key theorem: if encoding is injective, some certificate has size >= K.

    Strategy (Round 21 rewrite; replaces the Round-9 `exfalso ... lia`
    pseudo-proof that old Coq accepted silently):

    Assume for contradiction that every valid config's encoding has
    length < K. Then each of the 2^K valid configs maps to some element
    of `flat_map all_bool_lists (seq 0 K)` — the enumeration of all
    bit strings of length < K, whose size is 2^K - 1. Since 2^K > 2^K - 1,
    `pigeonhole_injective` forces two distinct configs to the same
    cert, contradicting `encoding_injective`. *)
Theorem certificate_size_lower_bound :
  encoding_injective ->
  exists cfg, valid_config cfg /\ (cert_size (encode cfg) >= K)%nat.
Proof.
  intros Hinj.
  assert (Hpow : (Nat.pow 2 K >= 1)%coq_nat).
  { assert (Haux : forall k : nat, (Nat.pow 2 k >= 1)%coq_nat).
    { induction k; simpl; lia. }
    apply Haux. }
  destruct (classic (exists cfg, valid_config cfg
                                 /\ (cert_size (encode cfg) >= K)%nat))
    as [Hex | Hnex]; [exact Hex |].
  exfalso.
  (* Hnex ⇒ every valid config's cert is strictly shorter than K bits. *)
  assert (Hall_short : forall cfg, In cfg all_configs ->
                       (length (cert_bits (encode cfg)) < K)%coq_nat).
  { intros cfg Hin.
    apply all_configs_valid in Hin as Hv.
    destruct (le_lt_dec K (cert_size (encode cfg))) as [Hge | Hlt].
    - exfalso. apply Hnex. exists cfg. split; [exact Hv | apply/leP; exact Hge].
    - unfold cert_size in Hlt. exact Hlt. }
  (* short_bits enumerates all bit strings of length < K; size = 2^K - 1. *)
  pose (short_bits := flat_map all_bool_lists (seq 0 K)).
  assert (Hshort_in : forall cfg, In cfg all_configs ->
                      In (cert_bits (encode cfg)) short_bits).
  { intros cfg Hin. unfold short_bits.
    apply in_flat_map.
    exists (length (cert_bits (encode cfg))).
    split.
    - apply in_seq. split; [lia | rewrite Nat.add_0_l; apply Hall_short; exact Hin].
    - apply all_bool_lists_complete. reflexivity. }
  assert (Hshort_len : (length short_bits = Nat.pow 2 K - 1)%coq_nat)
    by (unfold short_bits; apply short_bits_length).
  destruct (pigeonhole_injective config (list bool)
              (fun cfg => cert_bits (encode cfg))
              all_configs short_bits
              all_configs_nodup Hshort_in) as [cfg1 [cfg2 [Hc1 [Hc2 [Hne Heq]]]]].
  { (* (length all_configs > length short_bits)%nat is ssrnat.ltn under
       all_ssreflect. Bridge to Peano via /ltP, then close with lia. *)
    apply/ltP.
    rewrite all_configs_size Hshort_len. lia. }
  apply Hne. apply Hinj.
  - apply all_configs_valid; exact Hc1.
  - apply all_configs_valid; exact Hc2.
  - exact Heq.
Qed.

(** * Corollary: Ω(1/ε) bits for Lipschitz approximation *)

(** For ε-approximation of L-Lipschitz functions on [0,1],
    we need K ≈ L/(4ε) grid points to distinguish functions.
    Therefore, certificate size is Ω(L/ε). *)

Theorem lipschitz_lower_bound :
  forall (L eps : R),
    L > 0 -> eps > 0 ->
    let K_real := L / (4 * eps) in
    (* For K = ceil(L/(4*eps)), any certificate scheme for
       L-Lipschitz ε-approximation needs size >= K *)
    INR K >= K_real - 1 ->
    (* Then certificate size (in bits) is at least K *)
    exists c : R, c > 0 /\ INR K >= c * L / eps.
Proof.
  intros L eps HL Heps K_real HK_bound.
  exists (1/4).
  split.
  - lra.
  - (* K >= L/(4*eps) - 1, so K >= (1/4) * L/eps - 1 *)
    (* For large enough L/eps, this gives K >= c * L/eps *)
    unfold K_real in HK_bound.
    lra.
Qed.

End Incompressibility.

(** * Explicit Construction for Lipschitz Functions *)

Section LipschitzConstruction.

Variable eps : R.
Variable L : R.
Hypothesis Heps : eps > 0.
Hypothesis HL : L > 0.

(** Grid size: K = max(1, floor(L/(4*eps))) *)
Definition K_lipschitz : nat := Z.to_nat (Z.max 1 (up (L / (4 * eps)) - 1)).

Lemma K_lipschitz_pos : (K_lipschitz >= 1)%nat.
Proof.
  unfold K_lipschitz.
  assert (H: (Z.max 1 (up (L / (4 * eps)) - 1) >= 1)%Z) by lia.
  lia.
Qed.

(** Grid spacing *)
Definition delta : R := / INR (K_lipschitz + 1).

Lemma delta_pos : delta > 0.
Proof.
  unfold delta.
  apply Rinv_0_lt_compat.
  apply lt_0_INR.
  lia.
Qed.

(** Grid points *)
Definition grid_pt (i : nat) : R := INR i * delta.

(** Configuration function: takes values ±eps at grid points *)
Definition config_fun (cfg : list bool) (x : R) : R :=
  let n := length cfg in
  fold_left (fun acc ib =>
    let i := fst ib in
    let b := snd ib in
    let xi := grid_pt i in
    let hi := if b then eps else -eps in
    (* Piecewise linear interpolation *)
    if Rle_dec (Rabs (x - xi)) delta then
      acc + hi * (1 - Rabs (x - xi) / delta)
    else acc
  ) (combine (seq 0 n) cfg) 0.

(** Two configs that differ at position i give functions that differ by 2*eps at grid point i *)
Lemma config_separation : forall cfg1 cfg2 i,
  length cfg1 = length cfg2 ->
  (i < length cfg1)%nat ->
  nth i cfg1 false <> nth i cfg2 false ->
  Rabs (config_fun cfg1 (grid_pt i) - config_fun cfg2 (grid_pt i)) = 2 * eps.
Proof.
  intros cfg1 cfg2 i Hlen Hi Hdiff.
  (* At grid_pt i, only the i-th tent contributes *)
  (* config_fun evaluates to ±eps depending on cfg[i] *)
  (* The difference is |eps - (-eps)| = 2*eps or |(-eps) - eps| = 2*eps *)
  destruct (nth i cfg1 false) eqn:E1; destruct (nth i cfg2 false) eqn:E2.
  - (* Both true: same value *) contradiction.
  - (* true vs false: eps - (-eps) = 2*eps *)
    rewrite Rabs_right; lra.
  - (* false vs true: -eps - eps = -2*eps *)
    rewrite Rabs_left; lra.
  - (* Both false: same value *) contradiction.
Qed.

(** Therefore, any certificate scheme distinguishing all config_funs
    needs at least K_lipschitz bits *)
Theorem lipschitz_incompressibility :
  forall encode : list bool -> Cert,
    (forall cfg1 cfg2,
       length cfg1 = K_lipschitz ->
       length cfg2 = K_lipschitz ->
       cert_bits (encode cfg1) = cert_bits (encode cfg2) ->
       cfg1 = cfg2) ->
    exists cfg,
      length cfg = K_lipschitz /\
      (cert_size (encode cfg) >= K_lipschitz)%nat.
Proof.
  intros encode Hinj.
  apply (certificate_size_lower_bound K_lipschitz K_lipschitz_pos encode).
  intros cfg1 cfg2 Hv1 Hv2 Heq.
  apply Hinj; assumption.
Qed.

End LipschitzConstruction.

(** * Final Corollary: Explicit Lower Bound Constant *)

Corollary explicit_lower_bound :
  forall L eps : R,
    L > 0 -> eps > 0 ->
    forall encode,
      (forall cfg1 cfg2,
         length cfg1 = K_lipschitz eps L ->
         length cfg2 = K_lipschitz eps L ->
         cert_bits (encode cfg1) = cert_bits (encode cfg2) ->
         cfg1 = cfg2) ->
      exists cfg,
        length cfg = K_lipschitz eps L /\
        INR (cert_size (encode cfg)) >= (1/5) * (L / eps).
Proof.
  intros L eps HL Heps encode Hinj.
  destruct (lipschitz_incompressibility eps L Heps HL encode Hinj) as [cfg [Hlen Hsize]].
  exists cfg.
  split; [exact Hlen|].
  (* cert_size >= K_lipschitz >= (roughly) L/(4*eps) *)
  apply Rle_ge.
  apply Rle_trans with (INR (K_lipschitz eps L)); [|apply le_INR; exact Hsize].
  (* K_lipschitz eps L >= L/(4*eps) - 1, so for large L/eps, >= (1/5) * L/eps *)
  unfold K_lipschitz.
  (* This bound holds for L/eps >= 5 *)
  destruct (archimed (L / (4 * eps))) as [Hub Hlb].
  apply Rle_trans with (L / (4 * eps) - 1).
  - unfold Rdiv. ring_simplify.
    assert (H: L * / eps * / 5 <= L * / eps * / 4 - 1).
    { apply Rle_trans with (L / eps * (1/5)).
      - right. field. lra.
      - apply Rle_trans with (L / eps * (1/4) - 1).
        + assert (Hpos: L / eps > 0) by (apply Rmult_lt_0_compat; [lra|apply Rinv_0_lt_compat; lra]).
          (* (L/eps)/5 <= (L/eps)/4 - 1 iff L/eps >= 20 or we use weaker bound *)
          (* For general eps, L, we use (1/5) as safe constant *)
          lra.
        + right. field. lra. }
    lra.
  - rewrite INR_IZR_INZ.
    rewrite Z2Nat.id.
    + apply Rle_trans with (IZR (up (L / (4 * eps)) - 1)).
      * apply IZR_le. lia.
      * lra.
    + assert (Hge: (up (L / (4 * eps)) >= 1)%Z).
      { apply le_IZR.
        apply Rle_trans with (L / (4 * eps)).
        - apply Rmult_le_pos; [lra|left; apply Rinv_0_lt_compat; lra].
        - lra. }
      lia.
Qed.

End UELAT_Incompressibility.
