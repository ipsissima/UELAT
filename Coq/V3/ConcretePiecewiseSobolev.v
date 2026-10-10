(**
  ConcretePiecewiseSobolev.v -- REAL CELLWISE RIEMANN ENERGY for the actual
  [RationalPiecewiseCode] language used by v3 Definition 5.1.

  Every well-formed rational piece has a nondegenerate real interval.
  Its polynomial and code derivative have a genuine continuous Riemann
  squared-energy integral on that interval. For the whole finite chain,
  the sum of these real integrals is a concrete, nonnegative number.

  The rational seam certificates enforce agreement of the underlying
  real polynomial values at adjacent endpoints. Thus the syntactic
  "piece_chain_wf" is doing genuine analytic work; it is not an opaque
  existential interface.

  This file does NOT yet identify the piecewise derivative as a weak
  derivative in W^{1,2}(0,1), or identify the real integral with the
  existing exact Q arithmetic. Those remain explicit formal obligations.
  Candidate Rocq proof: kernel validation pending.
*)
From Stdlib Require Import Reals QArith Qreals List Lra RiemannInt.
Import ListNotations.
Local Open Scope R_scope.

From UELAT.V3 Require Import
  RationalSobolev RationalRealPolynomialSemantics
  ConcretePolynomialSobolev.

Module UELAT_V3_ConcretePiecewiseSobolev.
Import UELAT_V3_RationalSobolev.
Import UELAT_V3_RationalRealPolynomialSemantics.
Import UELAT_V3_ConcretePolynomialSobolev.

Definition rational_cell_real_order
    (c : RationalPiece) (H : piece_interval_positive c) :
    Q2R (piece_left c) <= Q2R (piece_right c).
Proof.
  apply Rlt_le.
  apply Qlt_Rlt. exact H.
Defined.

(** Not a formal stand-in: the integration domain and integrand are
    concrete real functions and real endpoints in Stdlib.Reals.RiemannInt. *)
Definition real_cell_w12_energy
    (c : RationalPiece) (H : piece_interval_positive c) : R :=
  RiemannInt
    (concrete_polynomial_integrable_interval
      (polynomial_energy_code (piece_poly c))
      (Q2R (piece_left c)) (Q2R (piece_right c))
      (rational_cell_real_order c H)).

Lemma real_cell_w12_energy_nonnegative :
    forall c H, 0 <= real_cell_w12_energy c H.
Proof.
  intros c H.
  pose proof (RiemannInt_P19
    (fct_cte 0)
    (rpoly_eval (polynomial_energy_code (piece_poly c)))
    (Q2R (piece_left c)) (Q2R (piece_right c))
    (RiemannInt_P14 (Q2R (piece_left c))
      (Q2R (piece_right c)) 0)
    (concrete_polynomial_integrable_interval
      (polynomial_energy_code (piece_poly c))
      (Q2R (piece_left c)) (Q2R (piece_right c))
      (rational_cell_real_order c H))) as Hmon.
  specialize (Hmon (rational_cell_real_order c H)).
  assert (Hpos : forall x,
    Q2R (piece_left c) < x < Q2R (piece_right c) ->
    fct_cte 0 x <= rpoly_eval
      (polynomial_energy_code (piece_poly c)) x).
  {
    intros x Hx. unfold fct_cte.
    apply polynomial_energy_pointwise_nonnegative.
  }
  specialize (Hmon Hpos).
  unfold real_cell_w12_energy.
  rewrite RiemannInt_P15 in Hmon.
  lra.
Qed.

Definition piece_chain_tail
    (c : RationalPiece) (rest : list RationalPiece) :
    piece_chain_wf (c :: rest) -> piece_chain_wf rest.
Proof.
  destruct rest as [|d tail]; simpl; intro H.
  - exact I.
  - destruct H as [_ [_ [_ Htail]]].
    exact Htail.
Defined.

(** Finite exact-Riemann sum of the cellwise W12 energies. *)
Fixpoint piecewise_real_w12_energy (cs : list RationalPiece)
    : piece_chain_wf cs -> R :=
  match cs as zs return piece_chain_wf zs -> R with
  | [] => fun _ => 0
  | c :: rest => fun H =>
      real_cell_w12_energy c (proj1 H) +
        piecewise_real_w12_energy rest (piece_chain_tail c rest H)
  end.

Theorem piecewise_real_w12_energy_nonnegative :
  forall cs (H : piece_chain_wf cs),
    0 <= piecewise_real_w12_energy cs H.
Proof.
  induction cs as [|c rest IH]; intro H; simpl.
  - lra.
  - pose proof (real_cell_w12_energy_nonnegative c (proj1 H))
      as Hcell.
    pose proof (IH (piece_chain_tail c rest H)) as Htail.
    lra.
Qed.

Definition code_real_w12_energy (u : RationalPiecewiseCode) : R :=
  piecewise_real_w12_energy (rpc_pieces u) (rpc_wf u).

Theorem every_well_formed_code_has_finite_nonnegative_real_energy :
  forall u, 0 <= code_real_w12_energy u.
Proof.
  intro u.
  unfold code_real_w12_energy.
  apply piecewise_real_w12_energy_nonnegative.
Qed.

(** Seam continuity of real values is a *derived theorem* from the
    encoded Qeq endpoint and polynomial evaluation certificates. *)
Theorem adjacent_piece_endpoints_match_over_reals :
  forall c d rest,
    piece_chain_wf (c :: d :: rest) ->
    Q2R (piece_right c) = Q2R (piece_left d).
Proof.
  intros c d rest H.
  simpl in H.
  destruct H as [_ [Heq [_ _]]].
  apply Qeq_eqR. exact Heq.
Qed.

Theorem adjacent_piece_values_match_over_reals :
  forall c d rest,
    piece_chain_wf (c :: d :: rest) ->
    rpoly_eval (piece_poly c) (Q2R (piece_right c))
      = rpoly_eval (piece_poly d) (Q2R (piece_left d)).
Proof.
  intros c d rest H.
  simpl in H.
  destruct H as [_ [_ [Heq _]]].
  repeat rewrite rpoly_rational_stage_agrees.
  apply Qeq_eqR. exact Heq.
Qed.

(** For the continuous W12 embedding still prove: the real function
    glued from these values is absolutely continuous and has as weak
    derivative the piecewise classical derivatives. This will connect
    the above genuinely integrated energy to the carrier norm. *)
End UELAT_V3_ConcretePiecewiseSobolev.
