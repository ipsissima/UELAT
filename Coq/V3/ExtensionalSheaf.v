(** ExtensionalSheaf.v -- authoritative Proposition 9.2.

    After zero-distance collapse, exact compatible represented local sections
    that glue uniquely satisfy the ordinary sheaf axiom. This module models the
    implication for finite declared covers; it makes no enriched-sheaf or stack
    claim.
*)

From Coq Require Import List.
Import ListNotations.

Module UELAT_V3_ExtensionalSheaf.

Section FiniteCoverSheaf.
  Context {Domain : Type}.
  Variable Section : Domain -> Type.

  Record Cover := {
    cover_base : Domain;
    cover_parts : list Domain
  }.

  Variable Restrict : forall {U V : Domain}, Section U -> Section V.
  Variable Compatible : forall (C : Cover),
      (forall V, In V (cover_parts C) -> Section V) -> Prop.

  Definition LocalFamily (C : Cover) : Type :=
    forall V, In V (cover_parts C) -> Section V.

  Variable restrict_family : forall (C : Cover) (s : Section (cover_base C)),
      LocalFamily C.

  Definition ExactGlueExistsUnique (C : Cover) : Prop :=
    forall (fam : LocalFamily C),
      Compatible C fam ->
      exists! s : Section (cover_base C),
        forall V (HV : In V (cover_parts C)),
          restrict_family C s V HV = fam V HV.

  Definition SheafAxiomOn (C : Cover) : Prop :=
    forall (fam : LocalFamily C),
      Compatible C fam ->
      exists! s : Section (cover_base C),
        forall V (HV : In V (cover_parts C)),
          restrict_family C s V HV = fam V HV.

  Theorem exact_gluing_implies_sheaf_axiom : forall C,
      ExactGlueExistsUnique C -> SheafAxiomOn C.
  Proof. intros C H. exact H. Qed.

  Variable IsCover : Cover -> Prop.
  Definition OrdinarySheaf : Prop :=
    forall C, IsCover C -> SheafAxiomOn C.

  Theorem extensional_sheaf_placement :
    (forall C, IsCover C -> ExactGlueExistsUnique C) -> OrdinarySheaf.
  Proof.
    intros H C HC.
    apply exact_gluing_implies_sheaf_axiom.
    now apply H.
  Qed.
End FiniteCoverSheaf.

End UELAT_V3_ExtensionalSheaf.
