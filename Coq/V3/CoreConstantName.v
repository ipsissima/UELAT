(** CoreConstantName.v -- canonical represented names for finite core vectors. *)

From Coq Require Import Reals.
From UELAT.V3 Require Import
  CertificateEnrichment RepresentedSpace ComputableBanach.

Module UELAT_V3_CoreConstantName.
Import UELAT_V3_CertificateEnrichment.
Import UELAT_V3_RepresentedSpace.
Import UELAT_V3_ComputableBanach.

Section ConstantName.
  Variable B : RealComputableBanachPresentation.

  Definition constant_core_fast_name (p : core_code B) : CoreFastName B.
  Proof.
    refine {| core_stage := fun _ => p |}.
    intros m n Hmn. rewrite distance_reflexive. apply dyadic_nonnegative.
  Defined.

  Definition constant_core_named_point (p : core_code B) : CoreNamedPoint B.
  Proof.
    refine {| core_named_value := core_decode p;
              core_named_name := constant_core_fast_name p;
              core_named_tail := _ |}.
    intro n. simpl. rewrite distance_reflexive. apply dyadic_nonnegative.
  Defined.

  Theorem constant_core_stage : forall p n,
    core_stage (core_named_name (constant_core_named_point p)) n = p.
  Proof. reflexivity. Qed.

  Theorem constant_core_value : forall p,
    core_named_value (constant_core_named_point p) = core_decode p.
  Proof. reflexivity. Qed.
End ConstantName.

End UELAT_V3_CoreConstantName.
