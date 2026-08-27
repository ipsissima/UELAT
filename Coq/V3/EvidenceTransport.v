(** EvidenceTransport.v -- v3 Theorem 4.2.

    This module now contains both the analytic Lipschitz estimate and the
    checker-level evidence-local constructor.  A finite-code compiler is
    represented by an executable code action together with finite target
    evidence constructors for approximation and distance witnesses.  The
    canonical lift asks the source certificate system once at

        eps / (3 max(1,Lambda))

    and calls the finite-code compiler once at defect eps/3.  It never invokes
    an independent generic certificate generator for the semantic target.
*)

From Coq Require Import Reals Lra Nra.
From UELAT.V3 Require Import CertificateEnrichment EvidenceCategory.

Module UELAT_V3_EvidenceTransport.
Import UELAT_V3_CertificateEnrichment.
Import UELAT_V3_EvidenceCategory.

Section AnalyticTransport.
  Context {X Y : MetricPresentation}.
  Variable T : carrier X -> carrier Y.
  Variable Lambda : R.

  Hypothesis Lambda_nonnegative : 0 <= Lambda.
  Hypothesis T_lipschitz : forall x x',
      distance (T x) (T x') <= Lambda * distance x x'.

  Theorem transported_approximation_bound
      (x : carrier X) (p : carrier X) (q : carrier Y)
      (r eta : R) :
    distance x p <= r ->
    distance (T p) q <= eta ->
    distance (T x) q <= Lambda * r + eta.
  Proof.
    intros Hsrc Hcompiler.
    eapply Rle_trans.
    - apply distance_triangle with (y := T p).
    - pose proof (T_lipschitz x p) as Hlip.
      nra.
  Qed.

  Theorem transported_distance_bound
      (x x' : carrier X) (r : R) :
    distance x x' <= r ->
    distance (T x) (T x') <= Lambda * r.
  Proof.
    intro Hsrc.
    pose proof (T_lipschitz x x') as Hlip.
    nra.
  Qed.

End AnalyticTransport.

Section CheckerLevelLift.

  Context {X Y : MetricPresentation}.
  Variable EX : CertificateEnrichment X.
  Variable EY : CertificateEnrichment Y.

  Variable T : carrier X -> carrier Y.
  Variable Tname : name X -> name Y.
  Variable Lambda : R.

  Hypothesis Lambda_nonnegative : 0 <= Lambda.
  Hypothesis Tname_correct : forall nu,
      decode_name (Tname nu) = T (decode_name nu).

  Definition max_one_lambda : R :=
    if Rle_dec Lambda 1 then 1 else Lambda.

  Lemma max_one_lambda_ge_one : 1 <= max_one_lambda.
  Proof.
    unfold max_one_lambda.
    destruct (Rle_dec Lambda 1); simpl; lra.
  Qed.

  Lemma lambda_le_max_one : Lambda <= max_one_lambda.
  Proof.
    unfold max_one_lambda.
    destruct (Rle_dec Lambda 1); simpl; lra.
  Qed.

  Lemma max_one_lambda_pos : 0 < max_one_lambda.
  Proof.
    pose proof max_one_lambda_ge_one. lra.
  Qed.

  Definition source_tolerance (eps : R) : R :=
    eps / (3 * max_one_lambda).

  Definition compiler_tolerance (eps : R) : R := eps / 3.

  Lemma source_tolerance_pos : forall eps,
    0 < eps -> 0 < source_tolerance eps.
  Proof.
    intros eps Heps.
    unfold source_tolerance.
    apply Rdiv_lt_0_compat.
    - exact Heps.
    - pose proof max_one_lambda_pos. nra.
  Qed.

  Lemma compiler_tolerance_pos : forall eps,
    0 < eps -> 0 < compiler_tolerance eps.
  Proof.
    intros eps Heps. unfold compiler_tolerance. lra.
  Qed.

  Record EvidenceLocalCompiler := {
    compile_code : code EX -> R -> code EY;

    compile_app : forall nu p r (w : app_witness EX) eta,
      app_check nu p r w = true ->
      0 <= eta ->
      { wy : app_witness EY |
        app_check (Tname nu) (compile_code p eta)
          (Lambda * r + eta) wy = true };

    compile_dist : forall nu mu r (w : dist_witness EX),
      dist_check nu mu r w = true ->
      { wy : dist_witness EY |
        dist_check (Tname nu) (Tname mu) (Lambda * r) wy = true }
  }.

  Arguments compile_code _ _ _.

  Lemma source_part_below_third : forall eps r,
    0 < eps ->
    0 <= r ->
    r < source_tolerance eps ->
    Lambda * r < eps / 3.
  Proof.
    intros eps r Heps Hr Hsmall.
    pose proof lambda_le_max_one as Hlam.
    pose proof max_one_lambda_pos as Hmpos.
    assert (Hmr : Lambda * r <= max_one_lambda * r) by nra.
    assert (Hscale : max_one_lambda * source_tolerance eps = eps / 3).
    { unfold source_tolerance.
      field_simpl.
      nra. }
    eapply Rle_lt_trans; [exact Hmr|].
    eapply Rlt_le_trans.
    - apply Rmult_lt_compat_l; assumption.
    - rewrite Hscale. lra.
  Qed.

  Definition lift_certificate_system
      (C : EvidenceLocalCompiler)
      (nu : name X)
      (c : CertificateSystem EX nu) :
      CertificateSystem EY (Tname nu).
  Proof.
    intros eps Heps.
    pose (a := source_tolerance eps).
    pose (eta := compiler_tolerance eps).
    pose (src_at := c a (source_tolerance_pos eps Heps)).
    pose (src := certificate_at_record EX src_at).
    destruct (compile_app C nu
                (cert_code EX src)
                (cert_bound EX src)
                (cert_evidence EX src)
                eta
                (cert_accepted EX src)
                (Rlt_le _ _ (compiler_tolerance_pos eps Heps)))
      as [wy Hwy].
    refine {| certificate_at_record :=
                {| cert_code := compile_code C (cert_code EX src) eta;
                   cert_bound := Lambda * cert_bound EX src + eta;
                   cert_bound_nonnegative := _;
                   cert_evidence := wy;
                   cert_accepted := Hwy |};
              certificate_at_strict := _ |}.
    - pose proof (cert_bound_nonnegative EX src).
      pose proof (compiler_tolerance_pos eps Heps).
      nra.
    - pose proof (certificate_at_strict EX src) as Hsrc.
      pose proof (cert_bound_nonnegative EX src) as Hsrc0.
      pose proof (source_part_below_third eps (cert_bound EX src)
                    Heps Hsrc0 Hsrc) as Hthird.
      unfold eta, compiler_tolerance.
      lra.
  Defined.

  Definition lift_distance
      (C : EvidenceLocalCompiler)
      {a b : EvidenceObject EX}
      (f : EvidenceArrow EX a b) :
      EvidenceArrow EY
        {| ev_name := Tname (ev_name EX a);
           ev_system := lift_certificate_system C (ev_name EX a) (ev_system EX a) |}
        {| ev_name := Tname (ev_name EX b);
           ev_system := lift_certificate_system C (ev_name EX b) (ev_system EX b) |}.
  Proof.
    destruct (compile_dist C
                (ev_name EX a) (ev_name EX b)
                (arrow_bound EX f) (arrow_witness EX f)
                (arrow_accepted EX f)) as [wy Hwy].
    refine {| arrow_bound := Lambda * arrow_bound EX f;
              arrow_bound_nonnegative := _;
              arrow_witness := wy;
              arrow_accepted := Hwy |}.
    pose proof (arrow_bound_nonnegative EX f). nra.
  Defined.

  Theorem qualitative_local_transport_saturation
      (C : EvidenceLocalCompiler) :
    (forall nu c, exists out,
       out = lift_certificate_system C nu c)
    /\
    (forall a b (f : EvidenceArrow EX a b),
       exists out, out = lift_distance C f).
  Proof.
    split; intros.
    - eexists. reflexivity.
    - eexists. reflexivity.
  Qed.

End CheckerLevelLift.

End UELAT_V3_EvidenceTransport.
