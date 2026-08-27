(** StrictSlackSearch.v -- executable finite-stage search for v3 Proposition 2.5. *)

From Coq Require Import Bool Arith Lia List Logic.ConstructiveEpsilon.
Import ListNotations.

Module UELAT_V3_StrictSlackSearch.

Fixpoint first_true_upto (test : nat -> bool) (fuel : nat) : option nat :=
  match fuel with
  | O => if test 0 then Some 0 else None
  | S k =>
      match first_true_upto test k with
      | Some n => Some n
      | None => if test (S k) then Some (S k) else None
      end
  end.

Lemma first_true_upto_sound : forall test fuel n,
  first_true_upto test fuel = Some n -> test n = true.
Proof.
  intros test fuel. induction fuel as [|fuel IH]; intros n H.
  - cbn in H. destruct (test 0) eqn:Ht; try discriminate.
    injection H as Hn. subst n. exact Ht.
  - cbn in H.
    destruct (first_true_upto test fuel) as [m|] eqn:Hprev.
    + injection H as Hmn. subst n.
      exact (IH m Hprev).
    + destruct (test (S fuel)) eqn:Ht; try discriminate.
      injection H as Hn. subst n. exact Ht.
Qed.

Lemma first_true_upto_index : forall test fuel n,
  first_true_upto test fuel = Some n -> n <= fuel.
Proof.
  intros test fuel. induction fuel as [|fuel IH]; intros n H.
  - cbn in H. destruct (test 0); try discriminate.
    injection H as Hn. subst n. lia.
  - cbn in H.
    destruct (first_true_upto test fuel) as [m|] eqn:Hprev.
    + injection H as Hmn. subst n.
      specialize (IH m Hprev). lia.
    + destruct (test (S fuel)); try discriminate.
      injection H as Hn. subst n. lia.
Qed.

Lemma first_true_upto_complete : forall test fuel witness,
  witness <= fuel -> test witness = true ->
  exists n, first_true_upto test fuel = Some n.
Proof.
  intros test fuel. induction fuel as [|fuel IH]; intros witness Hle Htrue.
  - assert (witness = 0) by lia. subst. simpl. rewrite Htrue. eauto.
  - simpl. destruct (first_true_upto test fuel) eqn:Hprev.
    + eauto.
    + destruct (Nat.eq_dec witness (S fuel)) as [->|Hneq].
      * rewrite Htrue. eauto.
      * assert (witness <= fuel) by lia.
        destruct (IH witness H Htrue) as [n Hn].
        rewrite Hn in Hprev. discriminate.
Qed.

Lemma bool_true_decidable : forall (test : nat -> bool) n,
  {test n = true} + {~ test n = true}.
Proof.
  intros test n. destruct (test n) eqn:H.
  - left. reflexivity.
  - right. discriminate.
Defined.

Definition first_true
    (test : nat -> bool)
    (eventually : exists n, test n = true) : {n : nat | test n = true} :=
  constructive_indefinite_ground_description_nat
    (fun n => test n = true) (bool_true_decidable test) eventually.

Definition first_true_index
    (test : nat -> bool)
    (eventually : exists n, test n = true) : nat :=
  proj1_sig (first_true test eventually).

Theorem first_true_valid : forall test eventually,
  test (first_true_index test eventually) = true.
Proof.
  intros test eventually. unfold first_true_index.
  exact (proj2_sig (first_true test eventually)).
Qed.

Record SemidecidableSlackSearch := {
  slack_test : nat -> bool;
  slack_eventually : exists n, slack_test n = true
}.

Definition run_semidecidable_slack_search
    (S : SemidecidableSlackSearch) : nat :=
  first_true_index (slack_test S) (slack_eventually S).

Theorem semidecidable_slack_search_valid : forall S,
  slack_test S (run_semidecidable_slack_search S) = true.
Proof. intro S. apply first_true_valid. Qed.

Record EffectiveSlackSearch := {
  stage_test : nat -> bool;
  stage_bound : nat;
  stage_bound_success : exists n,
      n <= stage_bound /\ stage_test n = true
}.

Definition run_slack_search (S : EffectiveSlackSearch) : option nat :=
  first_true_upto (stage_test S) (stage_bound S).

Theorem run_slack_search_terminates_successfully : forall S,
  exists n, run_slack_search S = Some n.
Proof.
  intro S. destruct (stage_bound_success S) as [w [Hw Htest]].
  unfold run_slack_search. now apply first_true_upto_complete with (witness := w).
Qed.

Theorem run_slack_search_returns_valid_stage : forall S n,
  run_slack_search S = Some n -> stage_test S n = true.
Proof.
  intros S n H. unfold run_slack_search in H.
  now apply first_true_upto_sound with (fuel := stage_bound S).
Qed.

End UELAT_V3_StrictSlackSearch.
