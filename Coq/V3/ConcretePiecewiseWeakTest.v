(**
  ConcretePiecewiseWeakTest.v -- seam cancellation for the actual
  rational piecewise-polynomial codes of Definition 5.1.

  On each certified rational cell, the real Riemann integration by
  parts formula holds by ConcretePolynomialWeakTest. The rational
  Qeq seam certificates are converted to exact real equalities by
  ConcretePiecewiseSobolev. Hence the interior boundary terms cancel
  and the global integration-by-parts identity follows for a single
  real polynomial test function.

  This is a genuine theorem about real Riemann integrals and code
  continuity, NOT a postulated weak-product rule. However it only
  covers polynomial test functions. A full W^{1,2}(0,1) embedding
  additionally requires the extension to all smooth compactly
  supported tests, the equality of rational/real energies, and the
  completion of the represented metric carrier.
*)
From Stdlib Require Import Reals QArith Qreals List Lra Ring RiemannInt.
Import ListNotations.
Local Open Scope R_scope.

From UELAT.V3 Require Import RationalSobolev
  RationalRealPolynomialSemantics ConcretePiecewiseSobolev
  ConcretePolynomialWeakTest.

Module UELAT_V3_ConcretePiecewiseWeakTest.
Import UELAT_V3_RationalSobolev.
Import UELAT_V3_RationalRealPolynomialSemantics.
Import UELAT_V3_ConcretePiecewiseSobolev.
Import UELAT_V3_ConcretePolynomialWeakTest.

Fixpoint initial_boundary (cs : list RationalPiece) (phi : QPoly) : R :=
  match cs with
  | [] => 0
  | c :: rest =>
    real_polynomial_product (piece_poly c) phi
      (Q2R (piece_left c))
  end.

Fixpoint terminal_boundary (cs : list RationalPiece) (phi : QPoly) : R :=
  match cs with
  | [] => 0
  | c :: rest =>
      match rest with
      | [] => real_polynomial_product (piece_poly c) phi
                (Q2R (piece_right c))
      | _ :: _ => terminal_boundary rest phi
      end
  end.

Fixpoint boundary_sum (cs : list RationalPiece) (phi : QPoly) : R :=
  match cs with
  | [] => 0
  | c :: rest =>
      real_polynomial_product (piece_poly c) phi
        (Q2R (piece_right c))
      - real_polynomial_product (piece_poly c) phi
        (Q2R (piece_left c))
      + boundary_sum rest phi
  end.

Fixpoint cell_weak_left_total (cs : list RationalPiece) :
    piece_chain_wf cs -> QPoly -> R :=
  match cs as zs return piece_chain_wf zs -> QPoly -> R with
  | [] => fun _ _ => 0
  | c :: rest => fun H phi =>
      RiemannInt
        (weak_term_left_integrable (piece_poly c) phi
          (Q2R (piece_left c)) (Q2R (piece_right c))
          (rational_cell_real_order c (proj1 H)))
      + cell_weak_left_total rest (piece_chain_tail c rest H) phi
  end.

Fixpoint cell_weak_right_total (cs : list RationalPiece) :
    piece_chain_wf cs -> QPoly -> R :=
  match cs as zs return piece_chain_wf zs -> QPoly -> R with
  | [] => fun _ _ => 0
  | c :: rest => fun H phi =>
      RiemannInt
        (weak_term_right_integrable (piece_poly c) phi
          (Q2R (piece_left c)) (Q2R (piece_right c))
          (rational_cell_real_order c (proj1 H)))
      + cell_weak_right_total rest (piece_chain_tail c rest H) phi
  end.

(** The analytic side: FTC on every actual real interval, then
    induction on the finite rational piece chain. *)
Theorem piecewise_Riemann_integration_by_parts :
  forall cs (H : piece_chain_wf cs) phi,
    cell_weak_left_total cs H phi + cell_weak_right_total cs H phi
      = boundary_sum cs phi.
Proof.
  induction cs as [|c rest IH]; intros H phi.
  - simpl. ring.
  - simpl [cell_weak_left_total cell_weak_right_total boundary_sum].
    pose proof
      (rational_polynomial_interval_integration_by_parts
        (piece_poly c) phi
        (Q2R (piece_left c)) (Q2R (piece_right c))
        (rational_cell_real_order c (proj1 H))) as Hcell.
    pose proof (IH (piece_chain_tail c rest H) phi) as Htail.
    lra.
Qed.

Lemma adjacent_product_value_match :
  forall c d rest phi,
    piece_chain_wf (c :: d :: rest) ->
    real_polynomial_product (piece_poly c) phi
      (Q2R (piece_right c))
      = real_polynomial_product (piece_poly d) phi
          (Q2R (piece_left d)).
Proof.
  intros c d rest phi H.
  pose proof
    (adjacent_piece_endpoints_match_over_reals c d rest H) as He.
  pose proof
    (adjacent_piece_values_match_over_reals c d rest H) as Hv.
  unfold real_polynomial_product.
  rewrite Hv, He.
  reflexivity.
Qed.

(** Seam cancellation uses the ACTUAL continuity certificates,
    rather than an assumed global integration-by-parts statement. *)
Theorem piecewise_seams_telescope :
  forall cs (H : piece_chain_wf cs) phi,
    boundary_sum cs phi =
      terminal_boundary cs phi - initial_boundary cs phi.
Proof.
  induction cs as [|c rest IH]; intros H phi.
  - simpl. ring.
  - destruct rest as [|d tail].
    + simpl. ring.
    + change
        (real_polynomial_product (piece_poly c) phi
           (Q2R (piece_right c))
         - real_polynomial_product (piece_poly c) phi
           (Q2R (piece_left c))
         + boundary_sum (d :: tail) phi
         =
           terminal_boundary (d :: tail) phi
             - real_polynomial_product (piece_poly c) phi
                (Q2R (piece_left c))).
      rewrite (IH (piece_chain_tail c (d :: tail) H) phi).
      pose proof (adjacent_product_value_match c d tail phi H) as Hseam.
      simpl [initial_boundary].
      rewrite Hseam.
      ring.
Qed.

Definition code_weak_left
    (u : RationalPiecewiseCode) (phi : QPoly) : R :=
  cell_weak_left_total (rpc_pieces u) (rpc_wf u) phi.

Definition code_weak_right
    (u : RationalPiecewiseCode) (phi : QPoly) : R :=
  cell_weak_right_total (rpc_pieces u) (rpc_wf u) phi.

Theorem code_piecewise_polynomial_test_weak_derivative :
  forall (u : RationalPiecewiseCode) (phi : QPoly),
    initial_boundary (rpc_pieces u) phi = 0 ->
    terminal_boundary (rpc_pieces u) phi = 0 ->
    code_weak_right u phi = - code_weak_left u phi.
Proof.
  intros u phi Hinitial Hterminal.
  pose proof (piecewise_Riemann_integration_by_parts
    (rpc_pieces u) (rpc_wf u) phi) as Hparts.
  pose proof (piecewise_seams_telescope
    (rpc_pieces u) (rpc_wf u) phi) as Htel.
  unfold code_weak_left, code_weak_right.
  rewrite Htel in Hparts.
  rewrite Hinitial, Hterminal in Hparts.
  lra.
Qed.

End UELAT_V3_ConcretePiecewiseWeakTest.
