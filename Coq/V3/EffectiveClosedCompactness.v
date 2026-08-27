(** EffectiveClosedCompactness.v -- generic Step 4 principle for authoritative
    Theorem 3.2. *)

From Coq Require Import List Bool Arith Lia.
Import ListNotations.
From UELAT.V3 Require Import StrictSlackSearch.

Module UELAT_V3_EffectiveClosedCompactness.
Import UELAT_V3_StrictSlackSearch.

Section ClosedCompactness.
  Context {Point BasicOpen : Type}.
  Variable member : Point -> BasicOpen -> Prop.
  Variable K : Point -> Prop.

  Definition covers (xs : list BasicOpen) (P : Point -> Prop) : Prop :=
    forall x, P x -> exists o, In o xs /\ member x o.
  Definition covers_ambient (xs : list BasicOpen) : Prop :=
    forall x, exists o, In o xs /\ member x o.

  Record AmbientFiniteCoverSemidecision := {
    ambient_cover_stage : list BasicOpen -> nat -> bool;
    ambient_cover_stage_sound : forall xs t,
      ambient_cover_stage xs t = true -> covers_ambient xs;
    ambient_cover_stage_complete : forall xs,
      covers_ambient xs -> exists t, ambient_cover_stage xs t = true
  }.

  Record CoCEClosedInCompact := {
    complement_open : nat -> BasicOpen;
    complement_open_sound : forall n x,
      member x (complement_open n) -> ~ K x;
    complement_open_complete : forall x,
      ~ K x -> exists n, member x (complement_open n);
    compact_finite_reduction : forall U,
      covers U K ->
      exists N,
        covers_ambient (U ++ map complement_open (seq 0 (S N)))
  }.

  Variable A : AmbientFiniteCoverSemidecision.
  Variable C : CoCEClosedInCompact.

  Definition complement_prefix (N : nat) : list BasicOpen :=
    map (complement_open C) (seq 0 (S N)).

  Definition closed_cover_stage
      (U : list BasicOpen) (N t : nat) : bool :=
    ambient_cover_stage A (U ++ complement_prefix N) t.

  Lemma closed_cover_stage_sound : forall U N t,
    closed_cover_stage U N t = true -> covers U K.
  Proof.
    intros U N t Hstage x Hx.
    unfold closed_cover_stage in Hstage.
    pose proof (ambient_cover_stage_sound A _ _ Hstage x)
      as [o [Hin Hmem]].
    apply in_app_or in Hin. destruct Hin as [HU|HC].
    - exists o. split; assumption.
    - exfalso. unfold complement_prefix in HC.
      apply in_map_iff in HC. destruct HC as [n [Ho Hn]]. subst o.
      pose proof (complement_open_sound C n x Hmem). contradiction.
  Qed.

  Lemma closed_cover_stage_eventually : forall U,
    covers U K -> exists N t, closed_cover_stage U N t = true.
  Proof.
    intros U HU.
    destruct (compact_finite_reduction C U HU) as [N Hambient].
    destruct (ambient_cover_stage_complete A
      (U ++ complement_prefix N) Hambient) as [t Ht].
    exists N, t. exact Ht.
  Qed.

  Definition bounded_exists_true (test : nat -> bool) (bound : nat) : bool :=
    match first_true_upto test bound with Some _ => true | None => false end.

  Definition closed_cover_square_test (U : list BasicOpen) (bound : nat) : bool :=
    bounded_exists_true
      (fun N => bounded_exists_true (fun t => closed_cover_stage U N t) bound)
      bound.

  Lemma bounded_exists_true_complete : forall test bound witness,
    witness <= bound -> test witness = true ->
    bounded_exists_true test bound = true.
  Proof.
    intros test bound witness Hle Htrue. unfold bounded_exists_true.
    destruct (first_true_upto_complete test bound witness Hle Htrue)
      as [n Hn]. rewrite Hn. reflexivity.
  Qed.

  Lemma bounded_exists_true_sound : forall test bound,
    bounded_exists_true test bound = true ->
    exists n, n <= bound /\ test n = true.
  Proof.
    intros test bound H. unfold bounded_exists_true in H.
    destruct (first_true_upto test bound) eqn:Hfirst; try discriminate.
    exists n. split.
    - now apply first_true_upto_index with (test := test).
    - now apply first_true_upto_sound with (fuel := bound).
  Qed.

  Lemma closed_cover_square_sound : forall U bound,
    closed_cover_square_test U bound = true -> covers U K.
  Proof.
    intros U bound H. unfold closed_cover_square_test in H.
    destruct (bounded_exists_true_sound _ _ H) as [N [HN Hrow]].
    destruct (bounded_exists_true_sound _ _ Hrow) as [t [Ht Hstage]].
    now apply closed_cover_stage_sound with (N := N) (t := t).
  Qed.

  Lemma closed_cover_square_eventually : forall U,
    covers U K -> exists bound, closed_cover_square_test U bound = true.
  Proof.
    intros U HU.
    destruct (closed_cover_stage_eventually U HU) as [N [t Hstage]].
    exists (Nat.max N t). unfold closed_cover_square_test.
    apply bounded_exists_true_complete with (witness := N).
    - apply Nat.le_max_l.
    - apply bounded_exists_true_complete with (witness := t).
      + apply Nat.le_max_r.
      + exact Hstage.
  Qed.

  Theorem coce_closed_subset_is_effectively_compact : forall U,
    covers U K -> exists bound, closed_cover_square_test U bound = true.
  Proof. apply closed_cover_square_eventually. Qed.
End ClosedCompactness.

End UELAT_V3_EffectiveClosedCompactness.
