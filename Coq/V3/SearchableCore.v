(** SearchableCore.v -- executable indexing of the rational core. *)

From Coq Require Import Bool Arith.
From UELAT.V3 Require Import ComputableBanach StrictSlackSearch.

Module UELAT_V3_SearchableCore.
Import UELAT_V3_ComputableBanach.
Import UELAT_V3_StrictSlackSearch.

Record SearchableCorePresentation := {
  sc_banach : RealComputableBanachPresentation;
  sc_core_eq_dec : forall p q : core_code sc_banach, {p = q} + {p <> q}
}.
Arguments sc_banach _ : clear implicits.

Definition core_eqb
    (B : SearchableCorePresentation)
    (p q : core_code (sc_banach B)) : bool :=
  if sc_core_eq_dec B p q then true else false.

Lemma core_eqb_true_iff : forall B p q,
  core_eqb B p q = true <-> p = q.
Proof.
  intros B p q. unfold core_eqb.
  destruct (sc_core_eq_dec B p q) as [Heq|Hneq].
  - split; intro; assumption.
  - split; intro H; [discriminate|contradiction].
Qed.

Lemma core_index_eventually : forall B p,
  exists n, core_eqb B (core_enum (sc_banach B) n) p = true.
Proof.
  intros B p. destruct (core_enum_surjective (sc_banach B) p) as [n Hn].
  exists n. apply core_eqb_true_iff. exact Hn.
Qed.

Definition core_index
    (B : SearchableCorePresentation)
    (p : core_code (sc_banach B)) : nat :=
  first_true_index
    (fun n => core_eqb B (core_enum (sc_banach B) n) p)
    (core_index_eventually B p).

Theorem core_index_correct : forall B p,
  core_enum (sc_banach B) (core_index B p) = p.
Proof.
  intros B p. apply core_eqb_true_iff.
  unfold core_index. apply first_true_valid.
Qed.

End UELAT_V3_SearchableCore.
