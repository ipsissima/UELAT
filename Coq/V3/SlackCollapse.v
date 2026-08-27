(** SlackCollapse.v -- conditional extensional collapse, authoritative v3 §2.2. *)

From Coq Require Import Reals Lra.
From UELAT.V3 Require Import CertificateEnrichment EvidenceCategory.

Module UELAT_V3_SlackCollapse.
Import UELAT_V3_CertificateEnrichment.
Import UELAT_V3_EvidenceCategory.

Section Collapse.
  Context {X : MetricPresentation} (E : CertificateEnrichment X).

  Definition StrictSlackComplete : Prop :=
    forall (nu mu : name X) (q : R),
      distance (decode_name nu) (decode_name mu) < q ->
      { w : dist_witness E | dist_check nu mu q w = true }.

  Definition EvidenceBound (nu mu : name X) (q : R) : Prop :=
    exists w : dist_witness E, dist_check nu mu q w = true.

  Definition LowerBound (S : R -> Prop) (a : R) : Prop :=
    forall q, S q -> a <= q.

  Definition GreatestLowerBound (S : R -> Prop) (a : R) : Prop :=
    LowerBound S a /\ forall b, LowerBound S b -> b <= a.

  Theorem evidence_bounds_are_sound
      (nu mu : name X) (q : R) :
    EvidenceBound nu mu q ->
    distance (decode_name nu) (decode_name mu) <= q.
  Proof.
    intros [w Hw].
    pose proof (dist_sound E _ _ _ _ Hw) as [_ H]. exact H.
  Qed.

  Theorem strict_slack_supplies_every_larger_bound
      (Hcomplete : StrictSlackComplete)
      (nu mu : name X) (q : R) :
    distance (decode_name nu) (decode_name mu) < q ->
    EvidenceBound nu mu q.
  Proof.
    intro Hlt. destruct (Hcomplete nu mu q Hlt) as [w Hw]. now exists w.
  Qed.

  Theorem evidence_distance_is_represented_distance
      (Hcomplete : StrictSlackComplete)
      (nu mu : name X) :
    GreatestLowerBound (EvidenceBound nu mu)
      (distance (decode_name nu) (decode_name mu)).
  Proof.
    split.
    - intros q Hq. now apply evidence_bounds_are_sound.
    - intros b Hb.
      set (d := distance (decode_name nu) (decode_name mu)).
      destruct (Rle_dec b d) as [Hbd|Hbd].
      + exact Hbd.
      + assert (Hdb : d < b) by lra.
        set (mid := (d + b) / 2).
        assert (Hdmid : d < mid) by (unfold mid, d; lra).
        assert (Hmidb : mid < b) by (unfold mid, d; lra).
        pose proof (strict_slack_supplies_every_larger_bound
                      Hcomplete nu mu mid Hdmid) as Hacc.
        specialize (Hb mid Hacc). lra.
  Qed.

  Corollary zero_evidence_distance_iff_zero_metric_glb
      (Hcomplete : StrictSlackComplete)
      (nu mu : name X) :
    distance (decode_name nu) (decode_name mu) = 0 ->
    GreatestLowerBound (EvidenceBound nu mu) 0.
  Proof.
    intro Hz. rewrite <- Hz.
    apply evidence_distance_is_represented_distance. exact Hcomplete.
  Qed.
End Collapse.

End UELAT_V3_SlackCollapse.
