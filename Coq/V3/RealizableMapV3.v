(** * RealizableMapV3.v — manuscript-exact Definition 5.1 interface

    This module records Definition 5.1 exactly at the level of the
    finite evidence interface printed in UELAT v3. It deliberately
    lives beside the older [V3_RealizableMap.RealizableMap] while the
    downstream generic lift is migrated, so that the already checked
    branch remains available as a regression oracle.

    The manuscript has FIVE clauses:
      (1) analytic Lipschitz map + stored finite derivation,
      (2) name transformer,
      (3) finite-code realizer,
      (4) explicit approximation-evidence transformer Xi_T,
      (5) explicit distance-evidence transformer Theta_T. *)

From Stdlib Require Import Reals Qcanon.
From UELAT.V3 Require Import EvidenceSyntax Presentation.
Local Open Scope Qc_scope.

Module V3_RealizableMapV3.

Import V3_EvidenceSyntax.
Import V3_Presentation.

Record RealizableMapV3 (P G : Presentation) : Type := {
  rv3_T             : F P -> F G;
  rv3_Lambda        : Qc;
  rv3_Lambda_nonneg : (0 <= rv3_Lambda)%Qc;
  rv3_lipschitz     :
    forall x y : F P,
      (distF G (rv3_T x) (rv3_T y)
       <= Qc2R rv3_Lambda * distF P x y)%R;
  rv3_lip_derivation : list bool;

  rv3_name    : NameF P -> NameF G;
  rv3_name_ok : forall nu : NameF P,
      deltaF G (rv3_name nu) = rv3_T (deltaF P nu);

  rv3_code         : CodeF P -> Qc -> CodeF G;
  rv3_code_witness : CodeF P -> Qc -> list bool;
  rv3_code_ok :
    forall (p : CodeF P) (eta : Qc),
      (0 < eta)%Qc ->
      AppCheck G (rv3_name (iotaF P p)) (rv3_code p eta) eta
               (rv3_code_witness p eta) = true;

  rv3_xi :
    forall (nu : NameF P) (p : CodeF P) (r eta : Qc),
      list bool -> list bool;
  rv3_xi_ok :
    forall (nu : NameF P) (p : CodeF P) (r eta : Qc) (V : list bool),
      (0 <= r)%Qc ->
      (0 < eta)%Qc ->
      AppCheck P nu p r V = true ->
      AppCheck G (rv3_name nu) (rv3_code p eta)
               (rv3_Lambda * r + eta)%Qc
               (rv3_xi nu p r eta V) = true;

  rv3_theta :
    forall (a b : NameF P),
      PSpine P a b -> PSpine G (rv3_name a) (rv3_name b);
  rv3_theta_bound :
    forall (a b : NameF P) (W : PSpine P a b),
      (sp_bound (rv3_theta a b W)
       <= rv3_Lambda * sp_bound W)%Qc;
  rv3_theta_id :
    forall a : NameF P,
      rv3_theta a a (sp_nil a) = sp_nil (rv3_name a);
  rv3_theta_comp :
    forall (a b c : NameF P)
           (W1 : PSpine P a b) (W2 : PSpine P b c),
      rv3_theta a c (sp_app W1 W2)
      = sp_app (rv3_theta a b W1) (rv3_theta b c W2)
}.

Arguments rv3_T {_ _} _ _.
Arguments rv3_Lambda {_ _} _.
Arguments rv3_Lambda_nonneg {_ _} _.
Arguments rv3_lipschitz {_ _} _ _ _.
Arguments rv3_lip_derivation {_ _} _.
Arguments rv3_name {_ _} _ _.
Arguments rv3_name_ok {_ _} _ _.
Arguments rv3_code {_ _} _ _ _.
Arguments rv3_code_witness {_ _} _ _ _.
Arguments rv3_code_ok {_ _} _ {_ _} _.
Arguments rv3_xi {_ _} _ _ _ _ _ _.
Arguments rv3_xi_ok {_ _} _ {_ _ _ _ _} _ _ _.
Arguments rv3_theta {_ _} _ _ _ _.
Arguments rv3_theta_bound {_ _} _ {_ _} _.
Arguments rv3_theta_id {_ _} _ _.
Arguments rv3_theta_comp {_ _} _ {_ _ _} _ _.

Theorem rv3_analytic_lipschitz :
  forall (P G : Presentation) (T : RealizableMapV3 P G)
         (nu mu : NameF P),
    (distF G (deltaF G (rv3_name T nu))
             (deltaF G (rv3_name T mu))
     <= Qc2R (rv3_Lambda T)
        * distF P (deltaF P nu) (deltaF P mu))%R.
Proof.
  intros P G T nu mu.
  rewrite !rv3_name_ok.
  apply rv3_lipschitz.
Qed.

End V3_RealizableMapV3.
