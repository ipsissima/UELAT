(**
  Category44FiniteCompilerClosure.v -- explicit analytic/category closure
  component of the manuscript's Definition 4.4.

  This is a REAL-PRECISION compiler layer. It proves, rather than
  postulates, that executable finite-code realizers (with named
  Type-2 realizers and Lipschitz bounds) compose and admit identities.
  The output precision is split so that the intermediate code
  approximation and final approximation remain strictly below eps.

  The manuscript's typed rational evidence witnesses and exact Q
  tolerance implementation remain separate obligations; accordingly
  this is NOT yet a full machine-checked Definition 4.4.

  Candidate proof: compile/coqchk/audit pending.
*)
From Coq Require Import Reals Lra Ring Field.
From UELAT.V3 Require Import CertificateEnrichment.

Module UELAT_V3_Category44FiniteCompilerClosure.
Import UELAT_V3_CertificateEnrichment.
Local Open Scope R_scope.

Definition first_tolerance (L eps : R) : R :=
  eps / (3 * (1 + L)).
Definition second_tolerance (eps : R) : R :=
  eps / 3.

Lemma first_tolerance_positive : forall L eps,
  0 <= L -> 0 < eps -> 0 < first_tolerance L eps.
Proof.
  intros L eps HL Heps.
  unfold first_tolerance.
  apply Rdiv_lt_0_compat; lra.
Qed.

Lemma second_tolerance_positive : forall eps,
  0 < eps -> 0 < second_tolerance eps.
Proof.
  intros eps Heps.
  unfold second_tolerance.
  apply Rdiv_lt_0_compat; lra.
Qed.

Lemma finite_compiler_budget_strict :
  forall L eps,
    0 <= L -> 0 < eps ->
    L * first_tolerance L eps + second_tolerance eps < eps.
Proof.
  intros L eps HL Heps.
  assert (Hden : 0 < 1 + L) by lra.
  assert (Hinv : 0 <= / (1 + L)).
  { left. apply Rinv_0_lt_compat. exact Hden. }
  assert (Hfraction : L * / (1 + L) <= 1).
  {
    replace 1 with ((1 + L) * / (1 + L)).
    - apply Rmult_le_compat_r; [exact Hinv|lra].
    - field. lra.
  }
  assert (Hfirst : L * first_tolerance L eps <= eps / 3).
  {
    unfold first_tolerance.
    replace (L * (eps / (3 * (1 + L))))
      with ((eps / 3) * (L * / (1 + L))) by (field; lra).
    replace (eps / 3) with ((eps / 3) * 1) at 2 by ring.
    apply Rmult_le_compat_l; [lra|exact Hfraction].
  }
  unfold second_tolerance. lra.
Qed.

Record FiniteCodeRealizer
    (X Y : MetricPresentation)
    (CX CY : Type)
    (rhoX : CX -> carrier X)
    (rhoY : CY -> carrier Y) := {
  fc_map : carrier X -> carrier Y;
  fc_names : name X -> name Y;
  fc_names_correct : forall nu,
    decode_name (fc_names nu) = fc_map (decode_name nu);
  fc_lipschitz_constant : R;
  fc_lipschitz_nonnegative : 0 <= fc_lipschitz_constant;
  fc_lipschitz : forall x y,
    distance (fc_map x) (fc_map y)
      <= fc_lipschitz_constant * distance x y;
  fc_compile : CX -> R -> CY;
  fc_compile_correct : forall p eps,
    0 < eps ->
    distance (fc_map (rhoX p)) (rhoY (fc_compile p eps)) < eps
}.

Arguments fc_map {X Y CX CY rhoX rhoY} _ _.
Arguments fc_names {X Y CX CY rhoX rhoY} _ _.
Arguments fc_names_correct {X Y CX CY rhoX rhoY} _ _.
Arguments fc_lipschitz_constant {X Y CX CY rhoX rhoY} _.
Arguments fc_lipschitz_nonnegative {X Y CX CY rhoX rhoY} _.
Arguments fc_lipschitz {X Y CX CY rhoX rhoY} _ _ _.
Arguments fc_compile {X Y CX CY rhoX rhoY} _ _ _.
Arguments fc_compile_correct {X Y CX CY rhoX rhoY} _ _ _ _.

Definition identity_finite_compiler
    (X : MetricPresentation) (C : Type)
    (rho : C -> carrier X) : FiniteCodeRealizer X X C C rho rho.
Proof.
  refine {| fc_map := fun x => x;
            fc_names := fun nu => nu;
            fc_lipschitz_constant := 1;
            fc_compile := fun p _ => p |}.
  - intro nu. reflexivity.
  - lra.
  - intros x y. simpl. ring_simplify. apply Rle_refl.
  - intros p eps Heps. simpl.
    rewrite distance_reflexive. exact Heps.
Defined.

Definition compose_finite_compiler
    {X Y Z : MetricPresentation}
    {CX CY CZ : Type}
    {rhoX : CX -> carrier X}
    {rhoY : CY -> carrier Y}
    {rhoZ : CZ -> carrier Z}
    (F : FiniteCodeRealizer X Y CX CY rhoX rhoY)
    (G : FiniteCodeRealizer Y Z CY CZ rhoY rhoZ) :
    FiniteCodeRealizer X Z CX CZ rhoX rhoZ.
Proof.
  refine {| fc_map := fun x => fc_map G (fc_map F x);
            fc_names := fun nu => fc_names G (fc_names F nu);
            fc_lipschitz_constant :=
              fc_lipschitz_constant G * fc_lipschitz_constant F;
            fc_compile := fun p eps =>
              fc_compile G
                (fc_compile F p
                   (first_tolerance (fc_lipschitz_constant G) eps))
                (second_tolerance eps) |}.
  - intro nu. rewrite (fc_names_correct G).
    rewrite (fc_names_correct F). reflexivity.
  - apply Rmult_le_pos;
      apply fc_lipschitz_nonnegative.
  - intros x y.
    pose proof (fc_lipschitz F x y) as HF.
    pose proof (fc_lipschitz G (fc_map F x) (fc_map F y)) as HG.
    eapply Rle_trans; [exact HG|].
    replace
      (fc_lipschitz_constant G * fc_lipschitz_constant F * distance x y)
      with
      (fc_lipschitz_constant G *
        (fc_lipschitz_constant F * distance x y)) by ring.
    apply Rmult_le_compat_l.
    + apply fc_lipschitz_nonnegative.
    + exact HF.
  - intros p eps Heps.
    set (L := fc_lipschitz_constant G).
    set (q := fc_compile F p (first_tolerance L eps)).
    set (r := fc_compile G q (second_tolerance eps)).
    assert (HL : 0 <= L).
    { unfold L. apply fc_lipschitz_nonnegative. }
    assert (Hfirst :
      distance (fc_map F (rhoX p)) (rhoY q)
        < first_tolerance L eps).
    { unfold q, L.
      apply fc_compile_correct.
      apply first_tolerance_positive; assumption. }
    assert (Hsecond :
      distance (fc_map G (rhoY q)) (rhoZ r)
        < second_tolerance eps).
    { unfold r.
      apply fc_compile_correct.
      apply second_tolerance_positive. exact Heps. }
    pose proof
      (fc_lipschitz G (fc_map F (rhoX p)) (rhoY q)) as Hlip.
    pose proof
      (@distance_triangle Z
        (fc_map G (fc_map F (rhoX p)))
        (fc_map G (rhoY q)) (rhoZ r)) as Htri.
    assert (Hamp :
      fc_lipschitz_constant G *
        distance (fc_map F (rhoX p)) (rhoY q)
      <= L * first_tolerance L eps).
    { unfold L.
      apply Rmult_le_compat_l.
      - apply fc_lipschitz_nonnegative.
      - lra. }
    pose proof (finite_compiler_budget_strict L eps HL Heps) as Hbudget.
    eapply Rle_lt_trans.
    + exact Htri.
    + eapply Rle_lt_trans.
      * pose proof (fc_lipschitz_nonnegative G) as Hnonnegative.
        lra.
      * exact Hbudget.
Defined.

(** Extensional arrow equality disregards implementation details:
    the compiler and its proof are witnesses of admissibility. *)
Definition analytic_arrow_equal
    {X Y : MetricPresentation} {CX CY : Type}
    {rhoX : CX -> carrier X} {rhoY : CY -> carrier Y}
    (F G : FiniteCodeRealizer X Y CX CY rhoX rhoY) : Prop :=
  forall x, fc_map F x = fc_map G x.

Theorem finite_composition_pointwise_associative :
  forall {X Y Z W : MetricPresentation}
    {CX CY CZ CW : Type}
    {rhoX : CX -> carrier X} {rhoY : CY -> carrier Y}
    {rhoZ : CZ -> carrier Z} {rhoW : CW -> carrier W}
    (F : FiniteCodeRealizer X Y CX CY rhoX rhoY)
    (G : FiniteCodeRealizer Y Z CY CZ rhoY rhoZ)
    (H : FiniteCodeRealizer Z W CZ CW rhoZ rhoW) x,
    fc_map (compose_finite_compiler (compose_finite_compiler F G) H) x
     = fc_map (compose_finite_compiler F (compose_finite_compiler G H)) x.
Proof.
  intros. reflexivity.
Qed.

End UELAT_V3_Category44FiniteCompilerClosure.
