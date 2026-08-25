(** * EvidenceClosureV3.v — missing evidence-language operations from Def. 2.1

    This is a conservative extension of the existing EvidenceClosure.
    The current closure record already carries symmetry, the mixed rule,
    and AppCheck weakening.  Proposition 5.3's manuscript proof of the
    identity realizable map additionally requires finite reflexive
    approximation evidence for the canonical name of a code.

    We make that operation explicit here instead of assuming an
    identity-specific theorem. *)

From Stdlib Require Import List Qcanon.
From UELAT.V3 Require Import Presentation Evidence.
Local Open Scope Qc_scope.

Module V3_EvidenceClosureV3.

Import V3_Presentation.
Import V3_Evidence.

Record EvidenceClosureV3 (P : Presentation) : Type := {
  ecv3_base : EvidenceClosure (P := P);

  ecv3_app_refl_witness : forall p : CodeF P, list bool;
  ecv3_app_refl_ok : forall p : CodeF P,
      AppCheck P (iotaF P p) p 0 (ecv3_app_refl_witness p) = true
}.

Arguments ecv3_base {_} _.
Arguments ecv3_app_refl_witness {_} _ _.
Arguments ecv3_app_refl_ok {_} _ _.

(** Every canonical reflexive witness can be weakened to any
    nonnegative announced error, as required by the identity code
    realizer in Proposition 5.3. *)
Definition ecv3_canonical_witness
    {P : Presentation} (EC : EvidenceClosureV3 P)
    (p : CodeF P) (eta : Qc) : list bool :=
  ec_app_weaken_witness (ecv3_base EC)
    (iotaF P p) p 0 eta (ecv3_app_refl_witness EC p).

Theorem ecv3_canonical_ok :
  forall (P : Presentation) (EC : EvidenceClosureV3 P)
         (p : CodeF P) (eta : Qc),
    (0 <= eta)%Qc ->
    AppCheck P (iotaF P p) p eta
      (ecv3_canonical_witness EC p eta) = true.
Proof.
  intros P EC p eta Heta.
  unfold ecv3_canonical_witness.
  eapply ec_app_weaken_ok.
  - exact Heta.
  - apply ecv3_app_refl_ok.
Qed.

End V3_EvidenceClosureV3.
