(** ResourceProfile.v -- concrete resource coordinates used in v3.

    Matches manuscript Definition 4.9 at the level of data: generation cost G,
    verification cost V, transport cost T, encoded proof size S, query/lookahead
    Q, and the evidence-locality flag L.  No representation-invariance theorem
    is asserted.
*)

From Coq Require Import Arith Bool.

Module UELAT_V3_ResourceProfile.

Record ResourceProfile := {
  generation_cost : nat;
  verification_cost : nat;
  transport_cost : nat;
  encoded_size : nat;
  query_lookahead : nat;
  evidence_local : bool
}.

Definition zero_profile : ResourceProfile :=
  {| generation_cost := 0;
     verification_cost := 0;
     transport_cost := 0;
     encoded_size := 0;
     query_lookahead := 0;
     evidence_local := true |}.

Definition compose_profile (a b : ResourceProfile) : ResourceProfile :=
  {| generation_cost := generation_cost a + generation_cost b;
     verification_cost := verification_cost a + verification_cost b;
     transport_cost := transport_cost a + transport_cost b;
     encoded_size := encoded_size a + encoded_size b;
     query_lookahead := Nat.max (query_lookahead a) (query_lookahead b);
     evidence_local := andb (evidence_local a) (evidence_local b) |}.

Lemma compose_profile_local a b :
  evidence_local a = true ->
  evidence_local b = true ->
  evidence_local (compose_profile a b) = true.
Proof.
  intros Ha Hb. simpl. now rewrite Ha, Hb.
Qed.

Lemma compose_profile_query a b :
  query_lookahead (compose_profile a b) =
  Nat.max (query_lookahead a) (query_lookahead b).
Proof. reflexivity. Qed.

End UELAT_V3_ResourceProfile.
