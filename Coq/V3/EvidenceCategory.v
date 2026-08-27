(** EvidenceCategory.v -- proof-relevant evidence category for v3.

    Matches the structural content of manuscript Definition 2.6.  Objects are
    represented names equipped with certificate systems; arrows are finite
    accepted distance witnesses.  The module proves identity and composition
    directly from the enrichment interface.
*)

From Coq Require Import Reals.
Local Open Scope R_scope.
From UELAT.V3 Require Import CertificateEnrichment.

Module UELAT_V3_EvidenceCategory.
Import UELAT_V3_CertificateEnrichment.

Section Evidence.
  Context {X : MetricPresentation} (E : CertificateEnrichment X).

  Record EvidenceObject := {
    ev_name : name X;
    ev_system : CertificateSystem E ev_name
  }.

  Record EvidenceArrow (a b : EvidenceObject) := {
    arrow_bound : R;
    arrow_bound_nonnegative : 0 <= arrow_bound;
    arrow_witness : dist_witness E;
    arrow_accepted :
      dist_check (ev_name a) (ev_name b) arrow_bound arrow_witness = true
  }.

  Arguments arrow_bound {a b} _.
  Arguments arrow_bound_nonnegative {a b} _.
  Arguments arrow_witness {a b} _.
  Arguments arrow_accepted {a b} _.

  Definition id_arrow (a : EvidenceObject) : EvidenceArrow a a.
  Proof.
    destruct (@dist_identity X E (ev_name a)) as [w Hw].
    refine {| arrow_bound := 0;
              arrow_bound_nonnegative := Rle_refl 0;
              arrow_witness := w;
              arrow_accepted := Hw |}.
  Defined.

  Definition compose_arrow {a b c : EvidenceObject}
      (g : EvidenceArrow b c) (f : EvidenceArrow a b) : EvidenceArrow a c.
  Proof.
    destruct (@dist_compose X E
              (ev_name a) (ev_name b) (ev_name c)
              (arrow_bound f) (arrow_bound g)
              (arrow_witness f) (arrow_witness g)
              (arrow_accepted f) (arrow_accepted g)) as [w Hw].
    refine {| arrow_bound := arrow_bound f + arrow_bound g;
              arrow_bound_nonnegative := Rplus_le_le_0_compat
                (arrow_bound_nonnegative f) (arrow_bound_nonnegative g);
              arrow_witness := w;
              arrow_accepted := Hw |}.
  Defined.

  Lemma arrow_sound {a b : EvidenceObject} (f : EvidenceArrow a b) :
    distance (decode_name (ev_name a)) (decode_name (ev_name b)) <= arrow_bound f.
  Proof.
    pose proof (@dist_sound X E _ _ _ _ (arrow_accepted f)) as [_ H].
    exact H.
  Qed.

End Evidence.
End UELAT_V3_EvidenceCategory.
