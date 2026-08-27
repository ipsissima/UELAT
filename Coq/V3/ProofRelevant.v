(** ProofRelevant.v -- v3 proof-relevant transport baseline.

    This file formalizes one of the structural points of the reconstructed
    manuscript: forgetting a chosen evidence transformation can identify
    distinct proof-relevant arrows with the same extensional map.

    It is deliberately small and foundational.  It does NOT claim that every
    analytic evidence system is captured by this toy record; later files will
    instantiate the pattern with the finite evidence interfaces used in the
    paper.
*)

From Coq Require Import Arith.PeanoNat.

Module UELAT_V3_ProofRelevant.

Record ChosenLift (A B : Type) := {
  underlying_map : A -> B;
  evidence_choice : nat
}.

Arguments underlying_map {A B} _ _.
Arguments evidence_choice {A B} _.

Definition forget {A B : Type} (f : ChosenLift A B) : A -> B :=
  underlying_map f.

Definition same_extensional_arrow {A B : Type}
    (f g : ChosenLift A B) : Prop :=
  forall x, forget f x = forget g x.

(** Distinct chosen lifts may lie above the same extensional map. *)
Theorem forgetful_nonfaithfulness_witness :
  exists (f g : ChosenLift unit unit),
    f <> g /\ same_extensional_arrow f g.
Proof.
  refine (ex_intro _ {| underlying_map := fun _ => tt;
                        evidence_choice := 0 |} _).
  refine (ex_intro _ {| underlying_map := fun _ => tt;
                        evidence_choice := 1 |} _).
  split.
  - intro H.
    pose proof (f_equal (@evidence_choice unit unit) H) as Htag.
    cbn in Htag. discriminate Htag.
  - intros []. reflexivity.
Qed.

(** Composition keeps a chosen intensional record.  Here the record is the
    additive tag; later certificate/DAG modules refine this to an actual
    evidence object and resource profile. *)
Definition compose {A B C : Type}
    (g : ChosenLift B C) (f : ChosenLift A B) : ChosenLift A C :=
  {| underlying_map := fun x => forget g (forget f x);
     evidence_choice := evidence_choice f + evidence_choice g |}.

Theorem forget_compose {A B C : Type}
    (g : ChosenLift B C) (f : ChosenLift A B) :
  forall x, forget (compose g f) x = forget g (forget f x).
Proof.
  reflexivity.
Qed.

End UELAT_V3_ProofRelevant.
