(** LocalizedPUFEMCompiler.v -- concrete finite compiler for authoritative Theorem 5.6 / 6.2.

    Each oriented overlap incidence contributes a constant number of proof
    actions and each target patch contributes one aggregation node. This makes
    the O(I+M) structural count executable and connects it to the append-only
    shared proof DAG.
*)

From Coq Require Import Reals List Arith Lia Nia.
Import ListNotations.
From UELAT.V3 Require Import ProofDAG PersistentGenealogy RationalPUFEM.

Module UELAT_V3_LocalizedPUFEMCompiler.
Import UELAT_V3_ProofDAG.
Import UELAT_V3_PersistentGenealogy.
Import UELAT_V3_RationalPUFEM.

Record IncidencePayload := {
  ip_delta0_sq : R;
  ip_delta1_sq : R;
  ip_L_sq : R
}.

Inductive PUFEMRule :=
| UseLocalDefect
| ApplyMultiplier
| RecordContribution
| AggregatePatch
| RecordScaleEstimate
| RecordTransition.

Inductive PUFEMPayload :=
| IncidenceData : IncidencePayload -> PUFEMPayload
| ScalarData : R -> PUFEMPayload
| StructuralData : nat -> PUFEMPayload.

Definition incidence_contribution
    (Cinf : R) (d : IncidencePayload) : R :=
  (Cinf^2 + 2 * ip_L_sq d) * ip_delta0_sq d
  + 2 * Cinf^2 * ip_delta1_sq d.

Fixpoint contribution_sum (Cinf : R) (ds : list IncidencePayload) : R :=
  match ds with
  | [] => 0
  | d :: rest => incidence_contribution Cinf d + contribution_sum Cinf rest
  end.

Definition patch_defect_bound
    (kappa Cinf : R) (ds : list IncidencePayload) : R :=
  kappa * contribution_sum Cinf ds.

Fixpoint incidence_steps
    (Cinf : R) (ds : list IncidencePayload) : list (PUFEMRule * PUFEMPayload) :=
  match ds with
  | [] => []
  | d :: rest =>
      (UseLocalDefect, IncidenceData d)
      :: (ApplyMultiplier, IncidenceData d)
      :: (RecordContribution, ScalarData (incidence_contribution Cinf d))
      :: incidence_steps Cinf rest
  end.

Fixpoint patch_steps (M : nat) : list (PUFEMRule * PUFEMPayload) :=
  match M with
  | O => []
  | S k => (AggregatePatch, StructuralData k) :: patch_steps k
  end.

Lemma incidence_steps_length : forall Cinf ds,
  length (incidence_steps Cinf ds) = 3 * length ds.
Proof. intros Cinf ds. induction ds; simpl; lia. Qed.

Lemma patch_steps_length : forall M,
  length (patch_steps M) = M.
Proof. induction M; simpl; lia. Qed.

Definition one_cover_steps
    (Cinf : R) (incidences : list IncidencePayload) (M : nat) :
    list (PUFEMRule * PUFEMPayload) :=
  incidence_steps Cinf incidences ++ patch_steps M.

Theorem one_cover_steps_length : forall Cinf incidences M,
  length (one_cover_steps Cinf incidences M) = 3 * length incidences + M.
Proof.
  intros. unfold one_cover_steps.
  rewrite app_length, incidence_steps_length, patch_steps_length. lia.
Qed.

Section DAGCompilation.
  Definition compile_one_cover
      (H : ProofDAG PUFEMPayload PUFEMRule)
      (Cinf : R) (incidences : list IncidencePayload) (M : nat) :
      ProofDAG PUFEMPayload PUFEMRule :=
    compile_refinement_level H (one_cover_steps Cinf incidences M).

  Theorem compile_one_cover_persistent : forall H Cinf incidences M,
    exists tail,
      dag_nodes (compile_one_cover H Cinf incidences M) = dag_nodes H ++ tail.
  Proof.
    intros H Cinf incidences M.
    unfold compile_one_cover.
    apply append_steps_persistent.
  Qed.

  Theorem compile_one_cover_node_count : forall H Cinf incidences M,
    node_count (compile_one_cover H Cinf incidences M)
      = node_count H + 3 * length incidences + M.
  Proof.
    intros H Cinf incidences M.
    unfold compile_one_cover.
    rewrite append_steps_node_count, one_cover_steps_length. lia.
  Qed.
End DAGCompilation.

Theorem compiled_patch_bound_is_manuscript_formula : forall kappa Cinf ds,
  patch_defect_bound kappa Cinf ds = kappa * contribution_sum Cinf ds.
Proof. reflexivity. Qed.

Definition scale_sensitive_incidence
    (hinv_sq delta0_sq delta1_sq : R) : R :=
  hinv_sq * delta0_sq + delta1_sq.

Theorem scale_sensitive_incidence_matches_core : forall h d0 d1,
  scale_sensitive_incidence h d0 d1 = scale_sensitive_defect h d0 d1.
Proof. reflexivity. Qed.

End UELAT_V3_LocalizedPUFEMCompiler.
