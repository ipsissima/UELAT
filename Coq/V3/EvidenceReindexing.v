(** EvidenceReindexing.v -- authoritative Proposition 4.6.

    Certificate systems can be reindexed to answer a tolerance eps using their
    answer at eps/2^k. This changes no represented point and acts identically on
    distance arrows, while changing the selected object-level evidence schedule.
*)

From Coq Require Import Reals Lra Lia.
From UELAT.V3 Require Import CertificateEnrichment EvidenceCategory.

Module UELAT_V3_EvidenceReindexing.
Import UELAT_V3_CertificateEnrichment.
Import UELAT_V3_EvidenceCategory.

Fixpoint shrink (k : nat) (eps : R) : R :=
  match k with O => eps | S j => shrink j eps / 2 end.

Lemma shrink_pos : forall k eps, 0 < eps -> 0 < shrink k eps.
Proof. induction k; simpl; intros eps Heps; try lra. specialize (IHk eps Heps). lra. Qed.

Lemma shrink_nonnegative : forall k eps, 0 <= eps -> 0 <= shrink k eps.
Proof.
  intros k eps Heps. destruct Heps as [Heps|Heps].
  - left. now apply shrink_pos.
  - subst eps. induction k; simpl; lra.
Qed.

Lemma shrink_le_original : forall k eps, 0 <= eps -> shrink k eps <= eps.
Proof.
  induction k; simpl; intros eps Heps.
  - lra.
  - pose proof (IHk eps Heps) as Hle.
    pose proof (shrink_nonnegative k eps Heps) as Hnonneg. lra.
Qed.

Lemma shrink_successor_strict : forall k eps,
  0 < eps -> shrink (S k) eps < shrink k eps.
Proof. simpl. intros k eps Heps. pose proof (shrink_pos k eps Heps). lra. Qed.

Lemma shrink_strict_of_lt : forall k l eps,
  0 < eps -> k < l -> shrink l eps < shrink k eps.
Proof.
  intros k l eps Heps Hkl. revert k Hkl.
  induction l as [|l IH]; intros k Hkl; [lia|].
  destruct (Nat.eq_dec k l) as [Heq|Hneq].
  - subst k. apply shrink_successor_strict. exact Heps.
  - assert (Hklt : k < l) by lia.
    eapply Rlt_trans; [apply shrink_successor_strict; exact Heps|].
    apply IH. exact Hklt.
Qed.

Lemma shrink_pairwise_distinct : forall k l eps,
  0 < eps -> k <> l -> shrink k eps <> shrink l eps.
Proof.
  intros k l eps Heps Hneq Heq.
  destruct (Nat.lt_ge_cases k l) as [Hkl|Hlk].
  - pose proof (shrink_strict_of_lt k l eps Heps Hkl). lra.
  - assert (Hlk' : l < k) by lia.
    pose proof (shrink_strict_of_lt l k eps Heps Hlk'). lra.
Qed.

Lemma shrink_add : forall k l eps,
  shrink (k + l) eps = shrink k (shrink l eps).
Proof. induction k; simpl; intros l eps; [reflexivity|rewrite IHk; reflexivity]. Qed.

Section Reindex.
  Context {X : MetricPresentation} (E : CertificateEnrichment X).

  Definition reindex_system (k : nat) {nu : name X}
      (c : CertificateSystem E nu) : CertificateSystem E nu.
  Proof.
    intros eps Heps.
    pose (small := c (shrink k eps) (shrink_pos k eps Heps)).
    refine {| certificate_at_record := certificate_at_record E small |}.
    eapply Rlt_le_trans.
    - exact (certificate_at_strict E small).
    - apply shrink_le_original. lra.
  Defined.

  Definition reindex_object (k : nat) (a : EvidenceObject E) : EvidenceObject E :=
    {| ev_name := ev_name E a; ev_system := reindex_system k (ev_system E a) |}.

  Definition reindex_arrow (k : nat) {a b : EvidenceObject E}
      (f : EvidenceArrow E a b) :
      EvidenceArrow E (reindex_object k a) (reindex_object k b).
  Proof.
    refine {| arrow_bound := arrow_bound E f;
              arrow_bound_nonnegative := arrow_bound_nonnegative E f;
              arrow_witness := arrow_witness E f |}.
    exact (arrow_accepted E f).
  Defined.

  Lemma reindex_preserves_underlying_name : forall k a,
    ev_name E (reindex_object k a) = ev_name E a.
  Proof. reflexivity. Qed.

  Lemma reindex_arrow_preserves_bound : forall k a b (f : EvidenceArrow E a b),
    arrow_bound E (reindex_arrow k f) = arrow_bound E f.
  Proof. reflexivity. Qed.

  Definition exact_half_system
      (nu : name X) (p : code E) (w0 : app_witness E)
      (Hw0 : app_check nu p 0 w0 = true) : CertificateSystem E nu.
  Proof.
    intros eps Heps.
    assert (Hhalfpos : 0 < eps / 2) by lra.
    assert (Hhalfnonneg : 0 <= eps / 2) by lra.
    destruct (app_weaken E nu p 0 (eps / 2) w0 Hw0) as [w Hw].
    - lra.
    - refine {| certificate_at_record :=
                  {| cert_code := p; cert_bound := eps / 2;
                     cert_bound_nonnegative := Hhalfnonneg;
                     cert_evidence := w; cert_accepted := Hw |};
                certificate_at_strict := _ |}.
      lra.
  Defined.

  Lemma exact_half_reindexed_bound : forall k nu p w0 Hw0 eps Heps,
    cert_bound E
      (certificate_at_record E
        (reindex_system k (exact_half_system nu p w0 Hw0) eps Heps))
      = shrink k eps / 2.
  Proof. reflexivity. Qed.

  Theorem reindexings_pairwise_distinct_on_exact_system :
    forall k l nu p w0 Hw0 eps Heps,
      k <> l ->
      cert_bound E
        (certificate_at_record E
          (reindex_system k (exact_half_system nu p w0 Hw0) eps Heps))
      <>
      cert_bound E
        (certificate_at_record E
          (reindex_system l (exact_half_system nu p w0 Hw0) eps Heps)).
  Proof.
    intros k l nu p w0 Hw0 eps Heps Hneq Heq.
    repeat rewrite exact_half_reindexed_bound in Heq.
    pose proof (shrink_pairwise_distinct k l eps Heps Hneq). nra.
  Qed.

  Theorem reindex_tolerance_monoid : forall k l eps,
    shrink k (shrink l eps) = shrink (k + l) eps.
  Proof. intros. symmetry. apply shrink_add. Qed.
End Reindex.

End UELAT_V3_EvidenceReindexing.
