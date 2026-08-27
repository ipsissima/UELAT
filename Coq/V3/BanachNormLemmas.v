(** BanachNormLemmas.v -- elementary consequences of the v3 Banach interface.

    These lemmas are used by the effective universality branch: additive
    inverses, norm-of-difference = metric distance, the norm triangle inequality
    and reverse-triangle estimates.  They are derived from the vector-space and
    metric compatibility fields rather than assumed separately.
*)

From Coq Require Import Reals Lra Ring.
From UELAT.V3 Require Import CertificateEnrichment ComputableBanach.

Module UELAT_V3_BanachNormLemmas.
Import UELAT_V3_CertificateEnrichment.
Import UELAT_V3_ComputableBanach.

Lemma cb_add_neg_l : forall B x,
  cb_add B (cb_neg B x) x = cb_zero B.
Proof.
  intros B x.
  unfold cb_neg.
  pose proof (cb_scale_add_scalars B (-1) 1 x) as H.
  replace ((-1 + 1)%R) with 0%R in H by ring.
  rewrite cb_scale_zero_scalar, cb_scale_one in H.
  symmetry. exact H.
Qed.

Lemma cb_add_neg_r : forall B x,
  cb_add B x (cb_neg B x) = cb_zero B.
Proof.
  intros B x.
  rewrite cb_add_comm.
  apply cb_add_neg_l.
Qed.

Lemma cb_sub_self : forall B x,
  cb_sub B x x = cb_zero B.
Proof.
  intros. unfold cb_sub. apply cb_add_neg_r.
Qed.

Lemma cb_sub_add_right : forall B x y,
  cb_add B (cb_sub B x y) y = x.
Proof.
  intros B x y.
  unfold cb_sub.
  rewrite <- cb_add_assoc.
  rewrite cb_add_neg_l.
  apply cb_add_zero_r.
Qed.

Lemma cb_norm_sub_is_distance : forall B x y,
  cb_norm B (cb_sub B x y) = distance x y.
Proof.
  intros B x y.
  unfold cb_norm, cb_sub.
  pose proof (cb_distance_translation B x y (cb_neg B y)) as H.
  rewrite cb_add_neg_r in H.
  rewrite cb_add_zero_r in H.
  exact H.
Qed.

Lemma cb_distance_add_same_right : forall B x y z,
  distance (cb_add B x z) (cb_add B y z) = distance x y.
Proof.
  intros. apply cb_distance_translation.
Qed.

Lemma cb_distance_add_to_left : forall B x y,
  distance (cb_add B x y) x = cb_norm B y.
Proof.
  intros B x y.
  unfold cb_norm.
  rewrite (cb_add_comm B x y).
  rewrite <- (cb_add_zero_l B x) at 2.
  apply cb_distance_translation.
Qed.

Lemma cb_norm_triangle : forall B x y,
  cb_norm B (cb_add B x y) <= cb_norm B x + cb_norm B y.
Proof.
  intros B x y.
  unfold cb_norm at 1.
  eapply Rle_trans.
  - apply distance_triangle with (y := x).
  - rewrite cb_distance_add_to_left.
    lra.
Qed.

Lemma cb_norm_reverse_triangle_left : forall B x y,
  cb_norm B x - cb_norm B y <= distance x y.
Proof.
  intros B x y.
  unfold cb_norm.
  pose proof (@distance_triangle (cb_metric B) x y (cb_zero B)) as H.
  lra.
Qed.

Lemma cb_norm_reverse_triangle_right : forall B x y,
  cb_norm B y - cb_norm B x <= distance x y.
Proof.
  intros B x y.
  rewrite distance_symmetric.
  apply cb_norm_reverse_triangle_left.
Qed.

Lemma cb_norm_lipschitz : forall B x y,
  Rabs (cb_norm B x - cb_norm B y) <= distance x y.
Proof.
  intros B x y.
  apply Rabs_le.
  split.
  - pose proof (cb_norm_reverse_triangle_right B x y). lra.
  - apply cb_norm_reverse_triangle_left.
Qed.

Lemma cb_nonzero_has_positive_norm : forall B x,
  x <> cb_zero B -> 0 < cb_norm B x.
Proof.
  intros B x Hneq.
  pose proof (cb_norm_nonnegative B x) as Hnonneg.
  destruct (Req_dec (cb_norm B x) 0) as [Hz|Hnz].
  - exfalso. apply Hneq.
    unfold cb_norm in Hz.
    apply (distance_separates (cb_metric B) x (cb_zero B)).
    exact Hz.
  - lra.
Qed.

End UELAT_V3_BanachNormLemmas.
