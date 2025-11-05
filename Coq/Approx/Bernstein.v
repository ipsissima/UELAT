From Coq Require Import Reals Binomial Psatz.
From UELAT.Approx Require Import Certificate.
Local Open Scope R_scope.

Module UELAT_Bernstein.

Definition I01 (x:R) : Prop := 0 <= x <= 1.

(* Bernstein operator B_N f at x *)
Definition BN (N:nat) (f:R->R) (x:R) : R :=
  let term k :=
    f (INR k / INR N) *
    (IZR (binomial N k) * x^k * (1 - x)^(N - k))
  in
  let fix sum k :=
      match k with
      | O => term 0
      | S k' => sum k' + term (S k')
      end
  in if Nat.eqb N 0 then f 0 else sum N.

(* A trivial sanity lemma that BN 0 = f 0, fully proved (no admits) *)
Lemma BN_zero : forall f x, BN 0 f x = f 0.
Proof. reflexivity. Qed.

(* A small algebra fact we’ll use later; again trivial and fully proved *)
Lemma pow_nonneg_01 : forall x n, I01 x -> 0 <= x^n.
Proof.
  intros x n [Hx0 Hx1].
  induction n as [|n IH]; simpl.
  - lra.
  - apply Rmult_le_pos; [exact IH|].
    exact Hx0.
Qed.

End UELAT_Bernstein.
