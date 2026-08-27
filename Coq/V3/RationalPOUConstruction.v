(** RationalPOUConstruction.v -- integrated constructor for manuscript Lemma 5.4. *)

From Coq Require Import QArith List Arith Lia.
Import ListNotations.
Local Open Scope Q_scope.
From UELAT.V3 Require Import
  RationalHatPOU RationalIntervalCover RationalPOUAssignment.

Module UELAT_V3_RationalPOUConstruction.
Import UELAT_V3_RationalHatPOU.
Import UELAT_V3_RationalIntervalCover.
Import UELAT_V3_RationalPOUAssignment.

Record FineSubdivisionCover := {
  fsc_cover : list RationalOpenInterval;
  fsc_cover_nonempty : fsc_cover <> [];
  fsc_star : nat -> RationalClosedStar;
  fsc_star_covered : forall k, CoverContainsStar fsc_cover (fsc_star k)
}.
Arguments fsc_cover _.
Arguments fsc_star _ _.

Definition assigned_patch (D : FineSubdivisionCover) (k : nat) : nat :=
  choose_covering_interval (fsc_cover D) (fsc_star D k) (fsc_star_covered D k).

Theorem assigned_patch_valid : forall D k,
  exists u, nth_error (fsc_cover D) (assigned_patch D k) = Some u
    /\ star_inside_interval (fsc_star D k) u.
Proof. intros D k. unfold assigned_patch. apply choose_covering_interval_valid. Qed.

Lemma assigned_patch_in_range : forall D k,
  assigned_patch D k < length (fsc_cover D).
Proof.
  intros D k. destruct (assigned_patch_valid D k) as [u [Hnth Hinside]].
  apply (proj1 (nth_error_Some (fsc_cover D) (assigned_patch D k))).
  rewrite Hnth. discriminate.
Qed.
Lemma cover_length_positive : forall D, 0 < length (fsc_cover D).
Proof.
  intro D. destruct (fsc_cover D) as [|u us] eqn:Hcover.
  - exfalso. apply (fsc_cover_nonempty D). exact Hcover.
  - simpl. lia.
Qed.

Definition integrated_star_assignment (D : FineSubdivisionCover) : StarAssignment.
Proof.
  refine {| sa_patch_count := length (fsc_cover D);
            sa_patch_count_positive := cover_length_positive D;
            sa_vertex_patch := assigned_patch D;
            sa_vertex_in_range := assigned_patch_in_range D;
            sa_star_inside := fun k =>
              exists u, nth_error (fsc_cover D) (assigned_patch D k) = Some u
                /\ star_inside_interval (fsc_star D k) u |}.
  intro k. apply assigned_patch_valid.
Defined.

Theorem integrated_assignment_is_subordinate : forall D k,
  exists u,
    nth_error (fsc_cover D)
      (sa_vertex_patch (integrated_star_assignment D) k) = Some u
    /\ star_inside_interval (fsc_star D k) u.
Proof. intros D k. simpl. apply assigned_patch_valid. Qed.

Theorem integrated_grouped_hats_partition_cell : forall D k a b x,
  ~ Qeq a b ->
  qsum (cell_patch_values (integrated_star_assignment D) k a b x) == 1.
Proof. intros D k a b x Hab. apply grouped_hats_partition_cell. exact Hab. Qed.
Theorem integrated_grouped_hats_partition_certified_cell : forall D k c x,
  qsum (cell_patch_values (integrated_star_assignment D) k
       (hat_left_endpoint c) (hat_right_endpoint c) x) == 1.
Proof. intros D k c x. apply grouped_hats_partition_certified_cell. Qed.
Theorem integrated_patch_value_count : forall D k a b x,
  length (cell_patch_values (integrated_star_assignment D) k a b x)
  = length (fsc_cover D).
Proof.
  intros D k a b x. unfold cell_patch_values.
  apply bucketize_length. apply cell_entries_in_range.
Qed.

End UELAT_V3_RationalPOUConstruction.
