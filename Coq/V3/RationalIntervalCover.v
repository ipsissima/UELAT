(** RationalIntervalCover.v -- finite search layer for manuscript Lemma 5.4.

    Once a rational subdivision is fine enough that every closed vertex star is
    contained in some cover interval, the required patch assignment is a finite
    decidable search.  This module implements that search over rational
    intervals and proves soundness/completeness.  RationalHatPOU and
    RationalPOUAssignment then group the nodal hats according to these indices.

    The only remaining existence step for a completely arbitrary finite open
    rational cover is the one-dimensional Lebesgue-number/refinement lemma that
    produces a sufficiently fine subdivision.
*)

From Coq Require Import QArith List Arith Lia Lqa.
Import ListNotations.
Local Open Scope Q_scope.

Module UELAT_V3_RationalIntervalCover.

Record RationalOpenInterval := {
  ri_left : Q;
  ri_right : Q;
  ri_positive : (ri_left < ri_right)%Q
}.

Record RationalClosedStar := {
  rs_left : Q;
  rs_right : Q;
  rs_ordered : (rs_left <= rs_right)%Q
}.

Definition star_inside_interval
    (s : RationalClosedStar) (u : RationalOpenInterval) : Prop :=
  (ri_left u < rs_left s)%Q /\ (rs_right s < ri_right u)%Q.

Definition star_insideb
    (s : RationalClosedStar) (u : RationalOpenInterval) : bool :=
  if Qlt_le_dec (ri_left u) (rs_left s) then
    if Qlt_le_dec (rs_right s) (ri_right u) then true else false
  else false.

Lemma star_insideb_spec : forall s u,
  star_insideb s u = true <-> star_inside_interval s u.
Proof.
  intros s u. unfold star_insideb, star_inside_interval.
  destruct (Qlt_le_dec (ri_left u) (rs_left s)) as [Hl|Hl].
  - destruct (Qlt_le_dec (rs_right s) (ri_right u)) as [Hr|Hr].
    + split; intro; [now split|reflexivity].
    + split; intro H.
      * discriminate.
      * destruct H as [_ H]. exfalso. now apply (Qlt_not_le _ _ H).
  - split; intro H.
    + discriminate.
    + destruct H as [H _]. exfalso. now apply (Qlt_not_le _ _ H).
Qed.

Fixpoint find_covering_from
    (offset : nat) (s : RationalClosedStar)
    (cover : list RationalOpenInterval) : option nat :=
  match cover with
  | [] => None
  | u :: us =>
      if star_insideb s u then Some offset
      else find_covering_from (S offset) s us
  end.

Definition find_covering_interval
    (s : RationalClosedStar)
    (cover : list RationalOpenInterval) : option nat :=
  find_covering_from 0 s cover.

Lemma find_covering_from_sound : forall offset s cover i,
  find_covering_from offset s cover = Some i ->
  exists k u,
    nth_error cover k = Some u
    /\ i = (offset + k)%nat
    /\ star_inside_interval s u.
Proof.
  intros offset s cover. revert offset.
  induction cover as [|u us IH]; intros offset i Hfind; simpl in Hfind.
  - discriminate.
  - destruct (star_insideb s u) eqn:Hinside.
    + inversion Hfind; subst.
      exists 0%nat, u.
      split; [reflexivity|].
      split; [lia|].
      apply (proj1 (star_insideb_spec s u)). exact Hinside.
    + destruct (IH (S offset) i Hfind) as [k [v [Hnth [Hi Hv]]]].
      exists (S k), v. simpl.
      split; [exact Hnth|].
      split; [lia|exact Hv].
Qed.

Theorem find_covering_interval_sound : forall s cover i,
  find_covering_interval s cover = Some i ->
  exists u,
    nth_error cover i = Some u /\ star_inside_interval s u.
Proof.
  intros s cover i H.
  unfold find_covering_interval in H.
  destruct (find_covering_from_sound 0%nat s cover i H)
    as [k [u [Hnth [Hi Hinside]]]].
  simpl in Hi. subst. now exists u.
Qed.

Lemma find_covering_from_complete : forall offset s cover k u,
  nth_error cover k = Some u ->
  star_inside_interval s u ->
  exists i, find_covering_from offset s cover = Some i.
Proof.
  intros offset s cover. revert offset.
  induction cover as [|v vs IH]; intros offset k u Hnth Hinside; simpl in Hnth.
  - discriminate.
  - destruct k as [|k].
    + injection Hnth as Hvu.
      rewrite <- Hvu in Hinside.
      simpl. rewrite (proj2 (star_insideb_spec s v) Hinside).
      eauto.
    + simpl.
      destruct (star_insideb s v) eqn:Hv; [eauto|].
      eapply IH; eauto.
Qed.

Theorem find_covering_interval_complete : forall s cover,
  (exists k u, nth_error cover k = Some u /\ star_inside_interval s u) ->
  exists i, find_covering_interval s cover = Some i.
Proof.
  intros s cover [k [u [Hnth Hinside]]].
  unfold find_covering_interval.
  eapply find_covering_from_complete; eauto.
Qed.

Definition CoverContainsStar (cover : list RationalOpenInterval)
    (s : RationalClosedStar) : Prop :=
  exists k u, nth_error cover k = Some u /\ star_inside_interval s u.

Definition choose_covering_interval
    (cover : list RationalOpenInterval) (s : RationalClosedStar)
    (H : CoverContainsStar cover s) : nat.
Proof.
  destruct (find_covering_interval_complete s cover H) as [i Hi].
  exact i.
Defined.

Theorem choose_covering_interval_valid : forall cover s H,
  exists u,
    nth_error cover (choose_covering_interval cover s H) = Some u
    /\ star_inside_interval s u.
Proof.
  intros cover s H.
  unfold choose_covering_interval.
  destruct (find_covering_interval_complete s cover H) as [i Hi].
  simpl. now apply find_covering_interval_sound.
Qed.

End UELAT_V3_RationalIntervalCover.
