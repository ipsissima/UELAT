(** CertificateEnrichment.v -- v3 finite evidence over represented metric spaces.

    This module matches the interface of manuscript Definition 2.2 and supplies
    the certificate-system object used by Definitions 2.3 and 2.6.  The
    represented object remains the extensional carrier; finite certificates are
    an enrichment over a supplied name.
*)

From Coq Require Import Reals Bool.
Local Open Scope R_scope.

Module UELAT_V3_CertificateEnrichment.

Record MetricPresentation := {
  carrier : Type;
  name : Type;
  decode_name : name -> carrier;
  distance : carrier -> carrier -> R;
  distance_nonnegative : forall x y, 0 <= distance x y;
  distance_reflexive : forall x, distance x x = 0;
  distance_symmetric : forall x y, distance x y = distance y x;
  distance_triangle : forall x y z,
      distance x z <= distance x y + distance y z;
  (** The analytic carrier is a genuine metric space, not merely a
      pseudometric presentation.  Proof evidence may later be quotiented, but
      represented analytic points are already separated. *)
  distance_separates : forall x y, distance x y = 0 -> x = y
}.

Arguments carrier _ : clear implicits.
Arguments name _ : clear implicits.
Arguments decode_name {m} _.
Arguments distance {m} _ _.

Record CertificateEnrichment (X : MetricPresentation) := {
  code : Type;
  decode_code : code -> carrier X;

  app_witness : Type;
  dist_witness : Type;

  app_check : name X -> code -> R -> app_witness -> bool;
  dist_check : name X -> name X -> R -> dist_witness -> bool;

  app_sound : forall nu p q w,
      app_check nu p q w = true ->
      0 <= q /\ distance (decode_name nu) (decode_code p) <= q;

  dist_sound : forall nu mu q w,
      dist_check nu mu q w = true ->
      0 <= q /\ distance (decode_name nu) (decode_name mu) <= q;

  app_weaken : forall nu p q q' w,
      app_check nu p q w = true -> q <= q' ->
      { w' : app_witness | app_check nu p q' w' = true };

  dist_weaken : forall nu mu q q' w,
      dist_check nu mu q w = true -> q <= q' ->
      { w' : dist_witness | dist_check nu mu q' w' = true };

  dist_identity : forall nu,
      { w : dist_witness | dist_check nu nu 0 w = true };

  dist_symmetry : forall nu mu q w,
      dist_check nu mu q w = true ->
      { w' : dist_witness | dist_check mu nu q w' = true };

  dist_compose : forall nu mu xi q r w1 w2,
      dist_check nu mu q w1 = true ->
      dist_check mu xi r w2 = true ->
      { w3 : dist_witness | dist_check nu xi (q + r) w3 = true }
}.

Arguments code {X} _.
Arguments decode_code {X c} _.
Arguments app_witness {X} _.
Arguments dist_witness {X} _.
Arguments app_check {X c} _ _ _ _.
Arguments dist_check {X c} _ _ _ _.

Section Certificates.
  Context {X : MetricPresentation} (E : CertificateEnrichment X).

  Record Certificate (nu : name X) := {
    cert_code : code E;
    cert_bound : R;
    cert_bound_nonnegative : 0 <= cert_bound;
    cert_evidence : app_witness E;
    cert_accepted : app_check nu cert_code cert_bound cert_evidence = true
  }.

  Record CertificateAt (nu : name X) (eps : R) := {
    certificate_at_record : Certificate nu;
    certificate_at_strict : cert_bound certificate_at_record < eps
  }.

  Definition CertificateSystem (nu : name X) : Type :=
    forall eps : R, 0 < eps -> CertificateAt nu eps.

  Lemma certificate_sound (nu : name X) (c : Certificate nu) :
    distance (decode_name nu) (decode_code (cert_code c)) <= cert_bound c.
  Proof.
    destruct c as [p q Hq w Hw]. simpl.
    pose proof (@app_sound X E nu p q w Hw) as [_ H].
    exact H.
  Qed.

End Certificates.

(** Keep the section parameters stable at call sites.  In particular, the
    represented name and tolerance are inferable from the certificate value;
    making that explicit here prevents Rocq-version-dependent projection
    elaboration in downstream manuscript modules. *)
Arguments cert_code {X} E {nu} _.
Arguments cert_bound {X} E {nu} _.
Arguments cert_bound_nonnegative {X} E {nu} _.
Arguments cert_evidence {X} E {nu} _.
Arguments cert_accepted {X} E {nu} _.
Arguments certificate_at_record {X} E {nu eps} _.
Arguments certificate_at_strict {X} E {nu eps} _.

End UELAT_V3_CertificateEnrichment.
