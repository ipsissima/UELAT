(** RationalPOUAssignment.v -- grouping rational nodal hats by cover patch. *)

From Coq Require Import QArith List Arith Lia Lqa Qring.
Import ListNotations.
Local Open Scope Q_scope.
From UELAT.V3 Require Import RationalHatPOU.

Module UELAT_V3_RationalPOUAssignment.
Import UELAT_V3_RationalHatPOU.

Fixpoint qsum (xs : list Q) : Q :=
  match xs with | [] => 0 | x :: rest => x + qsum rest end.
Fixpoint zero_buckets (M : nat) : list Q :=
  match M with | O => [] | S k => 0 :: zero_buckets k end.
Lemma zero_buckets_length : forall M, length (zero_buckets M) = M.
Proof. induction M; simpl; congruence. Qed.
Lemma qsum_zero_buckets : forall M, qsum (zero_buckets M) == 0.
Proof. induction M; simpl; [reflexivity|rewrite IHM; ring]. Qed.

Fixpoint add_at (i : nat) (v : Q) (bs : list Q) : list Q :=
  match i, bs with
  | O, b :: rest => (b + v) :: rest
  | S j, b :: rest => b :: add_at j v rest
  | _, [] => []
  end.
Lemma add_at_length : forall (i : nat) v bs,
  (i < length bs)%nat -> length (add_at i v bs) = length bs.
Proof.
  intros i v bs. revert i.
  induction bs as [|b rest IH]; intros i Hlt.
  - simpl in Hlt. lia.
  - destruct i as [|i].
    + reflexivity.
    + simpl. f_equal. apply IH. simpl in Hlt. lia.
Qed.
Lemma qsum_add_at : forall (i : nat) v bs,
  (i < length bs)%nat -> qsum (add_at i v bs) == v + qsum bs.
Proof.
  intros i v bs. revert i.
  induction bs as [|b rest IH]; intros i Hlt.
  - simpl in Hlt. lia.
  - destruct i as [|i].
    + simpl. ring.
    + simpl. rewrite IH by (simpl in Hlt; lia). ring.
Qed.

Fixpoint bucketize (M : nat) (entries : list (nat * Q)) : list Q :=
  match entries with
  | [] => zero_buckets M
  | (i,v) :: rest => add_at i v (bucketize M rest)
  end.
Definition entries_in_range (M : nat) (entries : list (nat * Q)) : Prop :=
  Forall (fun e => (fst e < M)%nat) entries.
Lemma bucketize_length : forall M entries,
  entries_in_range M entries -> length (bucketize M entries) = M.
Proof.
  intros M entries Hrange. induction Hrange as [|[i v] rest Hi Hrest IH]; simpl.
  - apply zero_buckets_length.
  - transitivity (length (bucketize M rest)).
    + apply add_at_length. rewrite IH. exact Hi.
    + exact IH.
Qed.

Fixpoint entry_value_sum (entries : list (nat * Q)) : Q :=
  match entries with | [] => 0 | (_,v) :: rest => v + entry_value_sum rest end.
Theorem bucketize_preserves_total : forall M entries,
  entries_in_range M entries -> qsum (bucketize M entries) == entry_value_sum entries.
Proof.
  intros M entries Hrange. induction Hrange as [|[i v] rest Hi Hrest IH]; simpl.
  - apply qsum_zero_buckets.
  - rewrite qsum_add_at.
    + rewrite IH. ring.
    + rewrite bucketize_length by exact Hrest. exact Hi.
Qed.

Record StarAssignment := {
  sa_patch_count : nat;
  sa_patch_count_positive : (0 < sa_patch_count)%nat;
  sa_vertex_patch : nat -> nat;
  sa_vertex_in_range : forall k, (sa_vertex_patch k < sa_patch_count)%nat;
  sa_star_inside : nat -> Prop;
  sa_star_inside_certified : forall k, sa_star_inside k
}.

Definition cell_entries (A : StarAssignment) (k : nat) (a b x : Q) : list (nat * Q) :=
  [ (sa_vertex_patch A k, left_hat_on_cell a b x);
    (sa_vertex_patch A (S k), right_hat_on_cell a b x) ].
Lemma cell_entries_in_range : forall A k a b x,
  entries_in_range (sa_patch_count A) (cell_entries A k a b x).
Proof. intros. unfold entries_in_range, cell_entries. simpl. repeat constructor; apply sa_vertex_in_range. Qed.
Definition cell_patch_values (A : StarAssignment) (k : nat) (a b x : Q) : list Q :=
  bucketize (sa_patch_count A) (cell_entries A k a b x).

Theorem grouped_hats_partition_cell : forall A k a b x,
  ~ Qeq a b -> qsum (cell_patch_values A k a b x) == 1.
Proof.
  intros A k a b x Hab. unfold cell_patch_values.
  rewrite bucketize_preserves_total.
  - simpl.
    transitivity (left_hat_on_cell a b x + right_hat_on_cell a b x).
    + ring.
    + apply two_hat_partition_identity. exact Hab.
  - apply cell_entries_in_range.
Qed.
Theorem grouped_hats_partition_certified_cell : forall A k c x,
  qsum (cell_patch_values A k
          (hat_left_endpoint c) (hat_right_endpoint c) x) == 1.
Proof.
  intros A k c x. apply grouped_hats_partition_cell.
  pose proof (hat_cell_positive c). lra.
Qed.

End UELAT_V3_RationalPOUAssignment.
