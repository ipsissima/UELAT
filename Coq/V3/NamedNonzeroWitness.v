(**
  NamedNonzeroWitness.v -- first constructive step of manuscript Lemma 3.1.

  Input is a REAL Type-2 name, not a bare abstract vector. From a fast
  rational core name of a nonzero represented vector and the executable
  core norm approximation, we COMPUTE a positive rational lower bound
  on its norm by unbounded semidecidable strict-slack search.

  This is a proved preparatory algorithm, NOT the approximate
  Hahn--Banach extension operator. No choice of a functional is assumed
  or constructed by this module. The extension step remains open.

  Candidate source: needs Rocq 9.2, coqchk, Print Assumptions.
*)
From Coq Require Import Reals QArith Qreals Lra.
From UELAT.V3 Require Import
  CertificateEnrichment RepresentedSpace ComputableBanach
  StrictSlackSearch DyadicVanishing GenericSlackCertification.

Module UELAT_V3_NamedNonzeroWitness.
Import UELAT_V3_CertificateEnrichment.
Import UELAT_V3_RepresentedSpace.
Import UELAT_V3_ComputableBanach.
Import UELAT_V3_StrictSlackSearch.
Import UELAT_V3_DyadicVanishing.
Import UELAT_V3_GenericSlackCertification.
Local Open Scope R_scope.

Section EffectiveNonzeroName.
  Variable B : RealComputableBanachPresentation.

  (** A terminating program on a name and a natural precision index. *)
  Definition named_norm_approx (x : CoreNamedPoint B) (n : nat) : Q :=
    core_norm_approx B (core_stage (core_named_name B x) n) n.

  Lemma named_norm_error : forall (x : CoreNamedPoint B) n,
    Rabs (Q2R (named_norm_approx x n)
       - cb_norm B (core_named_value B x))
      <= 2 * dyadic n.
  Proof.
    intros x n.
    set (p := core_stage (core_named_name B x) n).
    pose proof (core_norm_approx_sound B p n) as Hcore.
    pose proof (core_named_tail B x n) as Htail.
    pose proof (distance_triangle (cb_metric B)
      (core_named_value B x) (core_decode p) (cb_zero B)) as Hto.
    pose proof (distance_triangle (cb_metric B)
      (core_decode p) (core_named_value B x) (cb_zero B)) as Hfrom.
    assert (Hback :
      distance (core_decode p) (core_named_value B x)
        <= dyadic n).
    { pose proof (distance_symmetric (cb_metric B)
          (core_decode p) (core_named_value B x)) as Hsym.
      rewrite Hsym.
      exact Htail. }
    apply Rabs_le in Hcore.
    unfold named_norm_approx, cb_norm.
    apply Rabs_le.
    destruct Hcore as [Hcorelow Hcorehigh].
    split; lra.
  Qed.

  (** A boolean semidecision on the name: there is explicit strict
      slack between the approximated norm and the error tolerance. *)
  Definition named_nonzero_test (x : CoreNamedPoint B) (n : nat) : bool :=
    qltb (2 * qdyadic n)%Q (named_norm_approx x n).

  Lemma named_nonzero_test_sound :
    forall (x : CoreNamedPoint B) n,
      named_nonzero_test x n = true ->
      0 < cb_norm B (core_named_value B x).
  Proof.
    intros x n Htest.
    unfold named_nonzero_test in Htest.
    apply qltb_true_iff in Htest.
    pose proof (Qlt_Rlt _ _ Htest) as Hreal.
    rewrite Q2R_mult, qdyadic_real, Q2R_two in Hreal.
    pose proof (named_norm_error x n) as Herror.
    apply Rabs_le in Herror.
    lra.
  Qed.

  Lemma named_nonzero_test_eventually :
    forall (x : CoreNamedPoint B),
      0 < cb_norm B (core_named_value B x) ->
      exists n, named_nonzero_test x n = true.
  Proof.
    intros x Hpos.
    destruct (four_dyadic_eventually_below
      (cb_norm B (core_named_value B x)) Hpos) as [n Hsmall].
    exists n.
    unfold named_nonzero_test.
    apply qltb_true_iff.
    apply Rlt_Qlt.
    rewrite Q2R_mult, qdyadic_real, Q2R_two.
    pose proof (named_norm_error x n) as Herror.
    apply Rabs_le in Herror.
    lra.
  Qed.

  (** Uses the already-audited finite-stage semidecision combinator:
      the proof of eventual success lives in Prop, while the stage
      test uses the actual computable rational data from the name. *)
  Definition named_nonzero_stage
      (x : CoreNamedPoint B)
      (Hpos : 0 < cb_norm B (core_named_value B x)) : nat :=
    first_true_index (named_nonzero_test x)
      (named_nonzero_test_eventually x Hpos).

  Lemma named_nonzero_stage_accepted :
    forall x Hpos, named_nonzero_test x
        (named_nonzero_stage x Hpos) = true.
  Proof.
    intros x Hpos.
    unfold named_nonzero_stage.
    apply first_true_valid.
  Qed.

  Definition named_positive_lower_bound
      (x : CoreNamedPoint B)
      (Hpos : 0 < cb_norm B (core_named_value B x)) : Q :=
    (named_norm_approx x (named_nonzero_stage x Hpos)
     - 2 * qdyadic (named_nonzero_stage x Hpos))%Q.

  (** Actual strict rational certificate of positivity, obtained
      without requiring a numerical lower bound as an extra input. *)
  Theorem named_positive_lower_bound_sound :
    forall x Hpos,
      0 < Q2R (named_positive_lower_bound x Hpos)
      /\ Q2R (named_positive_lower_bound x Hpos)
           <= cb_norm B (core_named_value B x).
  Proof.
    intros x Hpos.
    set (n := named_nonzero_stage x Hpos).
    pose proof (named_nonzero_stage_accepted x Hpos) as Htest.
    unfold named_nonzero_test in Htest.
    apply qltb_true_iff in Htest.
    pose proof (Qlt_Rlt _ _ Htest) as Hreal.
    rewrite Q2R_mult, qdyadic_real, Q2R_two in Hreal.
    pose proof (named_norm_error x n) as Herror.
    apply Rabs_le in Herror.
    unfold named_positive_lower_bound.
    fold n.
    rewrite Q2R_minus, Q2R_mult, qdyadic_real, Q2R_two.
    lra.
  Qed.

  (** Nonzero is a PROMISE on the represented vector. The returned
      rational positive witness can then be passed to later
      constructive finite-dimensional extension stages. *)
End EffectiveNonzeroName.

End UELAT_V3_NamedNonzeroWitness.
