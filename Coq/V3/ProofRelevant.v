(** ProofRelevant.v -- proof-relevant transport baseline for authoritative v3.

    Forgetting a selected evidence transformation can identify distinct
    proof-relevant arrows with the same extensional map. The concrete
    non-faithfulness result is refined by EvidenceReindexing.v.
*)

From Coq Require Import Arith.PeanoNat.

Module UELAT_V3_ProofRelevant.

Record ChosenLift (A B : Type) := {
  underlying_map : A -> B;
  evidence_choice : nat
}.

Arguments underlying_map {A B} _ _.
Arguments evidence_choice {A B} _.

Definition forget {A B : Type} (f : ChosenLift A B) : A -> B := underlying_map f.

Definition same_extensional_arrow {A B : Type}
    (f g : ChosenLift A B) : Prop := forall x, forget f x = forget g x.

Theorem forgetful_nonfaithfulness_witness :
  exists (f g : ChosenLift unit unit), f <> g /\ same_extensional_arrow f g.
Proof.
  refine (ex_intro _ {| underlying_map := fun _ => tt; evidence_choice := 0 |} _).
  refine (ex_intro _ {| underlying_map := fun _ => tt; evidence_choice := 1 |} _).
  split.
  - intro H.
    assert (Htag : 0 = 1).
    { change (evidence_choice {| underlying_map := fun _ : unit => tt; evidence_choice := 0 |}) =
              evidence_choice {| underlying_map := fun _ : unit => tt; evidence_choice := 1 |}).
      now rewrite H. }
    discriminate Htag.
  - intros []. reflexivity.
Qed.

Definition compose {A B C : Type}
    (g : ChosenLift B C) (f : ChosenLift A B) : ChosenLift A C :=
  {| underlying_map := fun x => forget g (forget f x);
     evidence_choice := evidence_choice f + evidence_choice g |}.

Theorem forget_compose {A B C : Type}
    (g : ChosenLift B C) (f : ChosenLift A B) :
  forall x, forget (compose g f) x = forget g (forget f x).
Proof. reflexivity. Qed.

End UELAT_V3_ProofRelevant.
