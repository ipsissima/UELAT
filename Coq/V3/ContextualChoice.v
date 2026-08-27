(** ContextualChoice.v -- generated genealogies for v3 CCP.

    This module formalizes manuscript Definitions 8.1, 8.3, 8.4 and the closure
    calculus of Proposition 8.2 at a representation-independent interface.

    A CCP-admissible constructor carries a total evidence-level transformation,
    its underlying analytic operation and commuting equation, plus an explicit
    finite source-query plan and modulus for every input and requested output
    precision.  Finite lists make the access discipline literal, while Coq
    total functions represent terminating uniform algorithms.
*)

From Coq Require Import List Arith Lia.
Import ListNotations.

Module UELAT_V3_ContextualChoice.

(** * CCP-admissible constructors *)

Record CCPConstructor
    {A B DA DB : Type}
    (UA : A -> DA) (UB : B -> DB) := {
  ccp_evidence_map : A -> B;
  ccp_analytic_map : DA -> DB;
  ccp_commutes : forall a,
      UB (ccp_evidence_map a) = ccp_analytic_map (UA a);

  (** Query indices identify supplied source certificates/finite interfaces.
      Dependence on the finite input allows adaptive but still finite access. *)
  ccp_queries : nat -> A -> list nat;
  ccp_modulus : nat -> A -> nat
}.

Arguments ccp_evidence_map {A B DA DB UA UB} _ _.
Arguments ccp_analytic_map {A B DA DB UA UB} _ _.
Arguments ccp_queries {A B DA DB UA UB} _ _ _.
Arguments ccp_modulus {A B DA DB UA UB} _ _ _.

Definition ccp_query_count
    {A B DA DB} {UA : A -> DA} {UB : B -> DB}
    (F : CCPConstructor UA UB) (n : nat) (a : A) : nat :=
  length (ccp_queries F n a).

Theorem ccp_queries_are_finite :
  forall A B DA DB (UA : A -> DA) (UB : B -> DB)
         (F : CCPConstructor UA UB) n a,
    exists k, ccp_query_count F n a = k.
Proof.
  intros. eexists. reflexivity.
Qed.

Definition identity_ccp
    {A DA : Type} (UA : A -> DA) : CCPConstructor UA UA.
Proof.
  refine {| ccp_evidence_map := fun a => a;
            ccp_analytic_map := fun x => x;
            ccp_queries := fun _ _ => [];
            ccp_modulus := fun n _ => n |}.
  reflexivity.
Defined.

Definition compose_ccp
    {A B C DA DB DC : Type}
    {UA : A -> DA} {UB : B -> DB} {UC : C -> DC}
    (G : CCPConstructor UB UC)
    (F : CCPConstructor UA UB) : CCPConstructor UA UC.
Proof.
  refine {| ccp_evidence_map := fun a =>
              ccp_evidence_map G (ccp_evidence_map F a);
            ccp_analytic_map := fun x =>
              ccp_analytic_map G (ccp_analytic_map F x);
            ccp_queries := fun n a =>
              ccp_queries F
                (ccp_modulus G n (ccp_evidence_map F a)) a
              ++ ccp_queries G n (ccp_evidence_map F a);
            ccp_modulus := fun n a =>
              ccp_modulus F
                (ccp_modulus G n (ccp_evidence_map F a)) a |}.
  intro a.
  rewrite (ccp_commutes G (ccp_evidence_map F a)).
  rewrite (ccp_commutes F a).
  reflexivity.
Defined.

Theorem compose_query_count :
  forall A B C DA DB DC
         (UA : A -> DA) (UB : B -> DB) (UC : C -> DC)
         (G : CCPConstructor UB UC) (F : CCPConstructor UA UB) n a,
    ccp_query_count (compose_ccp G F) n a
      = ccp_query_count F (ccp_modulus G n (ccp_evidence_map F a)) a
        + ccp_query_count G n (ccp_evidence_map F a).
Proof.
  intros. unfold ccp_query_count. simpl. apply app_length.
Qed.

Definition product_ccp
    {A B C DA DB DC : Type}
    {UA : A -> DA} {UB : B -> DB} {UC : C -> DC}
    (F : CCPConstructor UA UB)
    (G : CCPConstructor UA UC) :
    CCPConstructor UA (fun bc : B * C => (UB (fst bc), UC (snd bc))).
Proof.
  refine {| ccp_evidence_map := fun a =>
              (ccp_evidence_map F a, ccp_evidence_map G a);
            ccp_analytic_map := fun x =>
              (ccp_analytic_map F x, ccp_analytic_map G x);
            ccp_queries := fun n a => ccp_queries F n a ++ ccp_queries G n a;
            ccp_modulus := fun n a =>
              Nat.max (ccp_modulus F n a) (ccp_modulus G n a) |}.
  intro a. simpl.
  rewrite (ccp_commutes F a), (ccp_commutes G a).
  reflexivity.
Defined.

Theorem product_query_count :
  forall A B C DA DB DC
         (UA : A -> DA) (UB : B -> DB) (UC : C -> DC)
         (F : CCPConstructor UA UB) (G : CCPConstructor UA UC) n a,
    ccp_query_count (product_ccp F G) n a
      = ccp_query_count F n a + ccp_query_count G n a.
Proof.
  intros. unfold ccp_query_count. simpl. apply app_length.
Qed.

Theorem ccp_structural_closure :
  (forall A DA (UA : A -> DA), CCPConstructor UA UA)
  /\
  (forall A B C DA DB DC
          (UA : A -> DA) (UB : B -> DB) (UC : C -> DC),
      CCPConstructor UA UB -> CCPConstructor UB UC -> CCPConstructor UA UC)
  /\
  (forall A B C DA DB DC
          (UA : A -> DA) (UB : B -> DB) (UC : C -> DC),
      CCPConstructor UA UB -> CCPConstructor UA UC ->
      CCPConstructor UA (fun bc : B * C => (UB (fst bc), UC (snd bc)))).
Proof.
  split.
  - intros A DA UA. exact (identity_ccp UA).
  - split.
    + intros A B C DA DB DC UA UB UC F G.
      exact (compose_ccp G F).
    + intros A B C DA DB DC UA UB UC F G.
      exact (product_ccp F G).
Qed.

(** * Operational Contextual Choice Principle *)

Section CCPDevelopment.
  Context {Obj : Type}.

  Variable Claimed : Obj -> Prop.
  Variable Primitive : Obj -> Prop.
  Variable AdmissibleOutput : Obj -> Prop.
  Variable LocalPromotion : Obj -> Prop.
  Variable PromotionJustified : Obj -> Prop.

  Definition ObeysCCP : Prop :=
    (forall x, Claimed x -> Primitive x \/ AdmissibleOutput x)
    /\
    (forall x, LocalPromotion x -> PromotionJustified x).

  Theorem ccp_claims_are_genealogically_accounted :
    ObeysCCP ->
    forall x, Claimed x -> Primitive x \/ AdmissibleOutput x.
  Proof.
    intros [Hclaims Hlocal] x Hx. now apply Hclaims.
  Qed.

  Theorem ccp_local_to_global_requires_interface :
    ObeysCCP ->
    forall x, LocalPromotion x -> PromotionJustified x.
  Proof.
    intros [Hclaims Hlocal] x Hx. now apply Hlocal.
  Qed.

End CCPDevelopment.

(** * Least generated certified universe *)

Section GeneratedUniverse.

  Context {Obj : Type}.

  Variable Primitive : Obj -> Prop.
  Variable Step0 : Obj -> Prop.
  Variable Step1 : Obj -> Obj -> Prop.
  Variable Step2 : Obj -> Obj -> Obj -> Prop.

  Inductive Generated : Obj -> Prop :=
  | generated_primitive : forall x,
      Primitive x -> Generated x
  | generated_nullary : forall out,
      Step0 out -> Generated out
  | generated_unary : forall x out,
      Generated x -> Step1 x out -> Generated out
  | generated_binary : forall x y out,
      Generated x -> Generated y -> Step2 x y out -> Generated out.

  Definition ClosedFamily (P : Obj -> Prop) : Prop :=
    (forall x, Primitive x -> P x) /\
    (forall out, Step0 out -> P out) /\
    (forall x out, P x -> Step1 x out -> P out) /\
    (forall x y out, P x -> P y -> Step2 x y out -> P out).

  Theorem generated_is_closed : ClosedFamily Generated.
  Proof.
    split.
    - intros x Hx. apply generated_primitive. exact Hx.
    - split.
      + intros out Hout. apply generated_nullary. exact Hout.
      + split.
        * intros x out Hx Hstep. eapply generated_unary; eauto.
        * intros x y out Hx Hy Hstep. eapply generated_binary; eauto.
  Qed.

  Theorem generated_least (P : Obj -> Prop) :
    ClosedFamily P ->
    forall x, Generated x -> P x.
  Proof.
    intros [Hprim [H0 [H1 H2]]] x Hgen.
    induction Hgen.
    - now apply Hprim.
    - now apply H0.
    - eapply H1; eauto.
    - eapply H2; eauto.
  Qed.

  Theorem invariant_preservation (R : Obj -> Prop) :
    (forall x, Primitive x -> R x) ->
    (forall out, Step0 out -> R out) ->
    (forall x out, R x -> Step1 x out -> R out) ->
    (forall x y out, R x -> R y -> Step2 x y out -> R out) ->
    forall x, Generated x -> R x.
  Proof.
    intros Hprim H0 H1 H2.
    apply generated_least.
    split; [exact Hprim|].
    split; [exact H0|].
    split; assumption.
  Qed.

  Corollary excluded_class_absent (R Bad : Obj -> Prop) :
    (forall x, Primitive x -> R x) ->
    (forall out, Step0 out -> R out) ->
    (forall x out, R x -> Step1 x out -> R out) ->
    (forall x y out, R x -> R y -> Step2 x y out -> R out) ->
    (forall x, Bad x -> ~ R x) ->
    forall x, Generated x -> ~ Bad x.
  Proof.
    intros Hprim H0 H1 H2 Hdisjoint x Hgen Hbad.
    apply (Hdisjoint x Hbad).
    eapply invariant_preservation; eauto.
  Qed.

End GeneratedUniverse.

End UELAT_V3_ContextualChoice.
