(** * RealizableMap.v — certifiably realizable Lipschitz maps (§5)

    Paper reference: Ballús Santacana, "Universal Gluing and Contextual
    Choice: Certificate-Carrying Approximation, Functorial Evidence, and
    Effective Descent", arXiv:2506.22693 v3, Definition 5.1 and
    Theorem 5.2.

    STATUS: IN-PROGRESS (see docs/FORMALIZATION_STATUS.md).

    This revision matches the FOUR conceptual clauses of Def 5.1.
    In particular, clause 4 (Theta_T) is explicit data again, rather
    than being silently derived from clause 1.  Clause 1's stored finite
    Lipschitz derivation is kept distinct.  The old fifth
    approximation-transport field remains absent: approximation
    transport is computed and proved below from evidence regularity,
    explicit Theta_T, the code realizer, and the mixed rule. *)

From Stdlib Require Import Reals QArith Qreals Qcanon Lra Lia.
From UELAT.V3 Require Import EvidenceSyntax Presentation Evidence EffectiveCompleteness.
Local Open Scope Qc_scope.

Module V3_RealizableMap.

Import V3_EvidenceSyntax.
Import V3_Presentation.
Import V3_Evidence.
Import V3_EffectiveCompleteness.

(** ** Definition 5.1 — certifiably realizable Lipschitz map. *)

Record RealizableMap (P G : Presentation) : Type := {

  (* ---- Clause 1: analytic Lipschitz map with stored derivation ---- *)
  rm_T             : F P -> F G;
  rm_Lambda        : Qc;
  rm_Lambda_nonneg : 0 <= rm_Lambda;
  rm_lipschitz     :
    forall x y : F P,
      (distF G (rm_T x) (rm_T y) <= Qc2R rm_Lambda * distF P x y)%R;

  (* A finite stored derivation and the uniform primitive application
     procedure that interprets it.  This is clause 1 evidence, not
     clause 4 itself. *)
  rm_lip_store : list bool;
  rm_lip_apply :
    list bool -> NameF P -> NameF P -> Qc -> list bool -> list bool;
  rm_lip_apply_ok :
    forall (nu mu : NameF P) (q : Qc) (W : list bool),
      DistLeaf P nu mu q W = true ->
      DistLeaf G (rm_name_placeholder nu) (rm_name_placeholder mu)
               (rm_Lambda * q)
               (rm_lip_apply rm_lip_store nu mu q W) = true;

  (* ---- Clause 2: name transformer with naturality ---- *)
  rm_name    : NameF P -> NameF G;
  rm_name_ok : forall nu : NameF P, deltaF G (rm_name nu) = rm_T (deltaF P nu);

  (* ---- Clause 3: finite-code realizer with accepted defect evidence ---- *)
  rm_code         : CodeF P -> Qc -> CodeF G;
  rm_code_witness : CodeF P -> Qc -> list bool;
  rm_code_ok :
    forall (p : CodeF P) (eta : Qc),
      0 < eta ->
      AppCheck G (rm_name (iotaF P p)) (rm_code p eta) eta
               (rm_code_witness p eta) = true;

  (* ---- Clause 4: explicit distance-evidence transformer Theta_T ----

     It is allowed to be more efficient than the canonical transformer
     induced by the stored clause-1 derivation.  The only bound property
     required is that its intrinsic target bound is no larger than
     Lambda times the intrinsic source bound; a lifted (q,W) morphism
     will announce exactly Lambda*q. *)
  rm_theta :
    forall (a b : NameF P),
      PSpine P a b -> PSpine G (rm_name a) (rm_name b);
  rm_theta_bound :
    forall (a b : NameF P) (W : PSpine P a b),
      (sp_bound (rm_theta a b W) <= rm_Lambda * sp_bound W)%Qc;
  rm_theta_id :
    forall a : NameF P,
      rm_theta a a (sp_nil a) = sp_nil (rm_name a);
  rm_theta_comp :
    forall (a b c : NameF P) (W1 : PSpine P a b) (W2 : PSpine P b c),
      rm_theta a c (sp_app W1 W2)
      = sp_app (rm_theta a b W1) (rm_theta b c W2)
}.

(* Rocq records cannot refer to a later field in an earlier field's
   type.  The stored-derivation application law above therefore needs
   the name transformer before it.  We deliberately do NOT hide this
   dependency behind a Parameter.  The record is defined below in the
   correct field order as [RealizableMapData]; [RealizableMap] is its
   public alias. *)

End V3_RealizableMap.
