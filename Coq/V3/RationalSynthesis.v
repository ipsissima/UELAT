(** RationalSynthesis.v -- v3 Proposition 5.5.

    On the rational piecewise-polynomial code language, synthesis is an exact
    finite fold of multiplication by partition codes followed by addition.
    This module proves both the semantic fold equation and the corresponding
    finite structural evidence compilation theorem.
*)

From Coq Require Import List Arith.
Import ListNotations.
From UELAT.V3 Require Import RationalSobolev.

Module UELAT_V3_RationalSynthesis.
Import UELAT_V3_RationalSobolev.

Definition raw_zero : RawRationalCode := {| raw_pieces := [] |}.

Fixpoint synthesize_raw
    (terms : list (RawRationalCode * RawRationalCode)) : RawRationalCode :=
  match terms with
  | [] => raw_zero
  | (psi,p) :: ts => raw_add (raw_mul psi p) (synthesize_raw ts)
  end.

Theorem finite_synthesis_computes : forall terms,
  exists pG : RawRationalCode, pG = synthesize_raw terms.
Proof. intro terms. eexists. reflexivity. Qed.

Section SemanticExactness.
  Context {A : Type}.
  Variable zeroA : A.
  Variable addA mulA : A -> A -> A.
  Variable interpret : RawRationalCode -> A.

  Hypothesis interpret_zero : interpret raw_zero = zeroA.
  Hypothesis interpret_add : forall u v,
      interpret (raw_add u v) = addA (interpret u) (interpret v).
  Hypothesis interpret_mul : forall u v,
      interpret (raw_mul u v) = mulA (interpret u) (interpret v).

  Fixpoint semantic_synthesis
      (terms : list (RawRationalCode * RawRationalCode)) : A :=
    match terms with
    | [] => zeroA
    | (psi,p) :: ts =>
        addA (mulA (interpret psi) (interpret p)) (semantic_synthesis ts)
    end.

  Theorem exact_synthesis_semantics : forall terms,
    interpret (synthesize_raw terms) = semantic_synthesis terms.
  Proof.
    induction terms as [|[psi p] ts IH].
    - simpl. exact interpret_zero.
    - simpl. rewrite interpret_add, interpret_mul, IH. reflexivity.
  Qed.
End SemanticExactness.

Record SynthesisRuleSystem := {
  SynthEvidence : Type;
  synth_valid : SynthEvidence -> Prop;

  synth_zero_evidence : SynthEvidence;
  synth_multiply_evidence : RawRationalCode -> SynthEvidence -> SynthEvidence;
  synth_add_evidence : SynthEvidence -> SynthEvidence -> SynthEvidence;

  synth_zero_valid : synth_valid synth_zero_evidence;
  synth_multiply_valid : forall psi e,
      synth_valid e -> synth_valid (synth_multiply_evidence psi e);
  synth_add_valid : forall e1 e2,
      synth_valid e1 -> synth_valid e2 ->
      synth_valid (synth_add_evidence e1 e2)
}.

Arguments SynthEvidence _ : clear implicits.

Fixpoint compile_synthesis_evidence
    (R : SynthesisRuleSystem)
    (terms : list (RawRationalCode * SynthEvidence R)) : SynthEvidence R :=
  match terms with
  | [] => synth_zero_evidence R
  | (psi,e) :: ts =>
      synth_add_evidence R
        (synth_multiply_evidence R psi e)
        (compile_synthesis_evidence R ts)
  end.

Theorem compiled_synthesis_evidence_is_valid :
  forall (R : SynthesisRuleSystem)
         (terms : list (RawRationalCode * SynthEvidence R)),
    Forall (fun t => synth_valid R (snd t)) terms ->
    synth_valid R (compile_synthesis_evidence R terms).
Proof.
  intros R terms Hvalid.
  induction Hvalid as [|[psi e] ts He Hts IH]; simpl.
  - apply synth_zero_valid.
  - apply synth_add_valid.
    + apply synth_multiply_valid. exact He.
    + exact IH.
Qed.

Definition SynthesisInput (R : SynthesisRuleSystem) :=
  list (RawRationalCode * RawRationalCode * SynthEvidence R).

Fixpoint synthesis_code_terms
    {R : SynthesisRuleSystem} (xs : SynthesisInput R) :
    list (RawRationalCode * RawRationalCode) :=
  match xs with
  | [] => []
  | (psi,p,e) :: xs' => (psi,p) :: synthesis_code_terms xs'
  end.

Fixpoint synthesis_evidence_terms
    {R : SynthesisRuleSystem} (xs : SynthesisInput R) :
    list (RawRationalCode * SynthEvidence R) :=
  match xs with
  | [] => []
  | (psi,p,e) :: xs' => (psi,e) :: synthesis_evidence_terms xs'
  end.

Record ExactSynthesisOutput (R : SynthesisRuleSystem) := {
  synthesized_code : RawRationalCode;
  synthesized_evidence : SynthEvidence R
}.

Definition compile_exact_synthesis
    (R : SynthesisRuleSystem) (xs : SynthesisInput R) :
    ExactSynthesisOutput R :=
  {| synthesized_code := synthesize_raw (synthesis_code_terms xs);
     synthesized_evidence :=
       compile_synthesis_evidence R (synthesis_evidence_terms xs) |}.

Theorem exact_finite_synthesis_with_evidence :
  forall (R : SynthesisRuleSystem) (xs : SynthesisInput R),
    Forall (fun t => synth_valid R (snd t)) (synthesis_evidence_terms xs) ->
    synthesized_code R (compile_exact_synthesis R xs)
      = synthesize_raw (synthesis_code_terms xs)
    /\
    synth_valid R (synthesized_evidence R (compile_exact_synthesis R xs)).
Proof.
  intros R xs Hvalid.
  split; [reflexivity|].
  simpl. now apply compiled_synthesis_evidence_is_valid.
Qed.

Fixpoint synthesis_input_count {R : SynthesisRuleSystem}
    (xs : SynthesisInput R) : nat :=
  match xs with | [] => 0 | _ :: xs' => S (synthesis_input_count xs') end.

Theorem synthesis_input_count_is_length : forall R (xs : SynthesisInput R),
  synthesis_input_count xs = length xs.
Proof. intros R xs. induction xs; simpl; congruence. Qed.

End UELAT_V3_RationalSynthesis.
