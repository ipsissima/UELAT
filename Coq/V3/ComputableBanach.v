(** ComputableBanach.v -- represented/computable Banach interface for v3 Section 2.

    This file implements the data interface of manuscript Definition 2.1.  The
    semantic carrier is explicitly required to satisfy the real vector-space
    laws, norm/metric compatibility and metric completeness; the effective
    presentation then adds a countable rational core, executable rational
    linear operations, computable norm approximations and fast-Cauchy names.

    It also packages the effective/countable part of Definition 2.2: the finite
    certificate code language is explicitly enumerable and dense in the named
    represented domain.  Coq functions are total, so the operations/checkers
    carried by these records are terminating programs in the formal model.
*)

From Coq Require Import Reals QArith Qreals List.
From UELAT.V3 Require Import CertificateEnrichment RepresentedSpace.

Module UELAT_V3_ComputableBanach.
Import UELAT_V3_CertificateEnrichment.
Import UELAT_V3_RepresentedSpace.

Record RealComputableBanachPresentation := {
  cb_metric : MetricPresentation;

  (** Semantic real vector-space structure. *)
  cb_zero : carrier cb_metric;
  cb_add : carrier cb_metric -> carrier cb_metric -> carrier cb_metric;
  cb_scale : R -> carrier cb_metric -> carrier cb_metric;

  cb_add_assoc : forall x y z,
      cb_add x (cb_add y z) = cb_add (cb_add x y) z;
  cb_add_comm : forall x y, cb_add x y = cb_add y x;
  cb_add_zero_l : forall x, cb_add cb_zero x = x;
  cb_scale_one : forall x, cb_scale 1 x = x;
  cb_scale_assoc : forall a b x,
      cb_scale a (cb_scale b x) = cb_scale (a * b) x;
  cb_scale_add_vectors : forall a x y,
      cb_scale a (cb_add x y) = cb_add (cb_scale a x) (cb_scale a y);
  cb_scale_add_scalars : forall a b x,
      cb_scale (a + b) x = cb_add (cb_scale a x) (cb_scale b x);
  cb_scale_zero_scalar : forall x, cb_scale 0 x = cb_zero;
  cb_scale_zero_vector_law : forall a, cb_scale a cb_zero = cb_zero;

  (** The metric is the norm metric.  Translation invariance and homogeneity
      are the properties consumed by the functional-analysis layer. *)
  cb_distance_translation : forall x y z,
      distance (cb_add x z) (cb_add y z) = distance x y;
  cb_norm_homogeneous : forall a x,
      distance (cb_scale a x) cb_zero
        = Rabs a * distance x cb_zero;

  (** Metric completeness, stated for Cauchy sequences carrying an explicit
      modulus.  This is semantic Banach completeness, not a claim that a
      computable limit can be extracted without a represented modulus. *)
  cb_complete : forall (u : nat -> carrier cb_metric) (modulus : nat -> nat),
      (forall s m n,
          (modulus s <= m)%nat -> (modulus s <= n)%nat ->
          distance (u m) (u n) <= dyadic s) ->
      exists x : carrier cb_metric,
        forall s n,
          (modulus s <= n)%nat ->
          distance x (u n) <= 2 * dyadic s;

  (** Countable rational vector core. *)
  core_code : Type;
  core_enum : nat -> core_code;
  core_enum_surjective : forall p : core_code, exists n, core_enum n = p;
  core_decode : core_code -> carrier cb_metric;

  core_zero : core_code;
  core_add : core_code -> core_code -> core_code;
  core_scale : Q -> core_code -> core_code;

  core_zero_sound : core_decode core_zero = cb_zero;
  core_add_sound : forall p q,
      core_decode (core_add p q) = cb_add (core_decode p) (core_decode q);
  core_scale_sound : forall a p,
      core_decode (core_scale a p) = cb_scale (Q2R a) (core_decode p);

  (** A rational approximation to the norm of a core point. *)
  core_norm_approx : core_code -> nat -> Q;
  core_norm_approx_sound : forall p n,
      Rabs (Q2R (core_norm_approx p n)
            - distance (core_decode p) cb_zero) <= dyadic n;

  (** Density of the rational core in the semantic Banach carrier. *)
  core_dense : forall x eps,
      0 < eps -> exists p : core_code,
        distance x (core_decode p) < eps
}.

Arguments cb_metric _ : clear implicits.
Arguments core_code _ : clear implicits.
Arguments core_decode {B} _.

Definition cb_neg (B : RealComputableBanachPresentation)
    (x : carrier (cb_metric B)) : carrier (cb_metric B) :=
  cb_scale B (-1) x.

Definition cb_sub (B : RealComputableBanachPresentation)
    (x y : carrier (cb_metric B)) : carrier (cb_metric B) :=
  cb_add B x (cb_neg B y).

Lemma cb_add_zero_r : forall B x,
  cb_add B x (cb_zero B) = x.
Proof.
  intros B x.
  rewrite cb_add_comm.
  apply cb_add_zero_l.
Qed.

Lemma cb_scale_zero_vector : forall B a,
  cb_scale B a (cb_zero B) = cb_zero B.
Proof.
  intros B a. apply cb_scale_zero_vector_law.
Qed.

Definition cb_norm (B : RealComputableBanachPresentation)
    (x : carrier (cb_metric B)) : R :=
  distance x (cb_zero B).

Lemma cb_norm_nonnegative : forall B x, 0 <= cb_norm B x.
Proof.
  intros B x. unfold cb_norm. apply distance_nonnegative.
Qed.

Lemma cb_norm_zero : forall B, cb_norm B (cb_zero B) = 0.
Proof.
  intro B. unfold cb_norm. apply distance_reflexive.
Qed.

Lemma cb_norm_scale : forall B a x,
  cb_norm B (cb_scale B a x) = Rabs a * cb_norm B x.
Proof.
  intros B a x. unfold cb_norm. apply cb_norm_homogeneous.
Qed.

Record CoreFastName (B : RealComputableBanachPresentation) := {
  core_stage : nat -> core_code B;
  core_stage_fast : forall m n,
      n <= m ->
      distance (core_decode (core_stage m))
               (core_decode (core_stage n)) <= dyadic n
}.

Arguments core_stage {B} _ _.

Record CoreNamedPoint (B : RealComputableBanachPresentation) := {
  core_named_value : carrier (cb_metric B);
  core_named_name : CoreFastName B;
  core_named_tail : forall n,
      distance core_named_value (core_decode (core_stage core_named_name n))
        <= dyadic n
}.

(** A Type-2 realizer is a program on names together with extensional
    correctness on every supplied named input. *)
Record Type2Realizer
    (B C : RealComputableBanachPresentation)
    (T : carrier (cb_metric B) -> carrier (cb_metric C)) := {
  realize_name : CoreFastName B -> CoreFastName C;
  realize_correct : forall x : CoreNamedPoint B,
      exists y : CoreNamedPoint C,
        core_named_value y = T (core_named_value x) /\
        core_named_name y = realize_name (core_named_name x)
}.

(** Effective certificate enrichment over the computable Banach presentation.
    The base CertificateEnrichment already contains executable finite checkers
    and their sound structural constructors.  This record adds an explicit
    enumeration and a density condition for the finite code language. *)
Record EffectiveCertificateEnrichment
    (B : RealComputableBanachPresentation) := {
  ece_base : CertificateEnrichment (cb_metric B);
  ece_code_enum : nat -> code ece_base;
  ece_code_enum_surjective : forall p : code ece_base,
      exists n, ece_code_enum n = p;
  ece_code_dense : forall x eps,
      0 < eps -> exists p : code ece_base,
        distance x (decode_code p) < eps
}.

Arguments ece_base {B} _.

(** The representation inherited from a core name is a fast-Cauchy sequence in
    the ambient metric presentation. *)
Definition core_name_as_fast_cauchy
    (B : RealComputableBanachPresentation)
    (nu : CoreFastName B) : FastCauchyName (cb_metric B).
Proof.
  refine {| approximant := fun n => core_decode (core_stage nu n) |}.
  intros m n Hmn.
  exact (core_stage_fast nu m n Hmn).
Defined.

Theorem core_named_point_has_represented_point
    (B : RealComputableBanachPresentation)
    (x : CoreNamedPoint B) :
  exists rx : RepresentedPoint (cb_metric B),
    represented_value rx = core_named_value x.
Proof.
  refine (ex_intro _
    {| represented_value := core_named_value x;
       represented_name := core_name_as_fast_cauchy B (core_named_name x);
       represented_tail := core_named_tail x |} _).
  reflexivity.
Qed.

End UELAT_V3_ComputableBanach.
