(** LocalizedPUFEMEvidence.v -- evidence-level form of authoritative Theorem 5.6.

    Packages supplied pairwise defect data, computes the finite sums in
    A_j^2/B_j^2/R_j, and turns component estimates into a finite output record.
    The only analytic primitive left abstract is the standard PUFEM component
    estimate itself.
*)

From Coq Require Import Reals List Lra Nra.
Import ListNotations.
From UELAT.V3 Require Import RationalPUFEM LocalizedPUFEMCompiler.

Module UELAT_V3_LocalizedPUFEMEvidence.
Import UELAT_V3_RationalPUFEM.
Import UELAT_V3_LocalizedPUFEMCompiler.

Fixpoint rsum (xs : list R) : R :=
  match xs with [] => 0 | x :: rest => x + rsum rest end.

Record PairwiseDefectDatum := {
  pdd_delta0 : R;
  pdd_delta1 : R;
  pdd_L : R;
  pdd_delta0_nonnegative : 0 <= pdd_delta0;
  pdd_delta1_nonnegative : 0 <= pdd_delta1;
  pdd_L_nonnegative : 0 <= pdd_L
}.

Definition delta0_sq (d : PairwiseDefectDatum) : R := pdd_delta0 d ^ 2.
Definition delta1_sq (d : PairwiseDefectDatum) : R := pdd_delta1 d ^ 2.
Definition Ldelta0_sq (d : PairwiseDefectDatum) : R :=
  pdd_L d ^ 2 * pdd_delta0 d ^ 2.

Definition sum_delta0_sq (ds : list PairwiseDefectDatum) : R := rsum (map delta0_sq ds).
Definition sum_delta1_sq (ds : list PairwiseDefectDatum) : R := rsum (map delta1_sq ds).
Definition sum_Ldelta0_sq (ds : list PairwiseDefectDatum) : R := rsum (map Ldelta0_sq ds).

Lemma rsum_nonnegative : forall xs,
  Forall (fun x => 0 <= x) xs -> 0 <= rsum xs.
Proof. intros xs H. induction H; simpl; lra. Qed.

Lemma defect_square_sums_nonnegative : forall ds,
  0 <= sum_delta0_sq ds
  /\ 0 <= sum_Ldelta0_sq ds
  /\ 0 <= sum_delta1_sq ds.
Proof.
  intro ds.
  unfold sum_delta0_sq, sum_Ldelta0_sq, sum_delta1_sq.
  repeat split; apply rsum_nonnegative;
    apply Forall_forall; intros x Hx;
    apply in_map_iff in Hx; destruct Hx as [d [<- Hin]];
    unfold delta0_sq, delta1_sq, Ldelta0_sq; nra.
Qed.

Definition manuscript_R
    (kappa Cinf : R) (ds : list PairwiseDefectDatum) : R :=
  kappa *
    (Cinf^2 * sum_delta0_sq ds
     + 2 * sum_Ldelta0_sq ds
     + 2 * Cinf^2 * sum_delta1_sq ds).

Record ComponentEvidence
    (kappa Cinf : R) (ds : list PairwiseDefectDatum) := {
  component_l2_sq : R;
  component_deriv_sq : R;
  component_l2_nonnegative : 0 <= component_l2_sq;
  component_deriv_nonnegative : 0 <= component_deriv_sq;
  component_l2_bound :
    component_l2_sq <= kappa * Cinf^2 * sum_delta0_sq ds;
  component_deriv_bound :
    component_deriv_sq <=
      2 * kappa * (sum_Ldelta0_sq ds + Cinf^2 * sum_delta1_sq ds)
}.

Record CompiledLocalizedDefect
    (kappa Cinf : R) (ds : list PairwiseDefectDatum)
    (E : ComponentEvidence kappa Cinf ds) := {
  cld_bound : R;
  cld_bound_is_manuscript_R : cld_bound = manuscript_R kappa Cinf ds;
  cld_total_defect_bound :
    component_l2_sq E + component_deriv_sq E <= cld_bound
}.

Definition compile_localized_defect
    (kappa Cinf : R)
    (Hkappa : 0 <= kappa) (HCinf : 0 <= Cinf)
    (ds : list PairwiseDefectDatum)
    (E : ComponentEvidence kappa Cinf ds) :
    CompiledLocalizedDefect kappa Cinf ds E.
Proof.
  destruct (defect_square_sums_nonnegative ds) as [H0 [HL H1]].
  refine {| cld_bound := manuscript_R kappa Cinf ds;
            cld_bound_is_manuscript_R := eq_refl |}.
  unfold manuscript_R.
  pose proof (component_l2_bound E) as Hl2.
  pose proof (component_deriv_bound E) as Hd.
  lra.
Defined.

Theorem compiled_localized_defect_is_sound :
  forall kappa Cinf Hkappa HCinf ds E,
    component_l2_sq E + component_deriv_sq E
      <= manuscript_R kappa Cinf ds.
Proof.
  intros.
  exact (cld_total_defect_bound
    (compile_localized_defect kappa Cinf Hkappa HCinf ds E)).
Qed.

Definition as_incidence_payload (d : PairwiseDefectDatum) : IncidencePayload :=
  {| ip_delta0_sq := delta0_sq d;
     ip_delta1_sq := delta1_sq d;
     ip_L_sq := pdd_L d ^ 2 |}.

Definition incidence_payloads (ds : list PairwiseDefectDatum) : list IncidencePayload :=
  map as_incidence_payload ds.

Theorem incidence_payload_count : forall ds,
  length (incidence_payloads ds) = length ds.
Proof. intro ds. unfold incidence_payloads. apply map_length. Qed.

(** Corrected from the source reconstruction: [one_cover_steps] also takes
    [Cinf], because the contribution labels store the concrete multiplier
    coefficient. *)
Theorem compiled_structural_step_count : forall Cinf ds M,
  length (one_cover_steps Cinf (incidence_payloads ds) M)
    = 3 * length ds + M.
Proof.
  intros Cinf ds M.
  rewrite one_cover_steps_length, incidence_payload_count.
  reflexivity.
Qed.

End UELAT_V3_LocalizedPUFEMEvidence.
