(** * RealizableMap.v — v3 certifiably realizable Lipschitz maps
       and the achievable-bound content of the generic lifting
       theorem (§5, Def 5.1 and Thm 5.2 partial)

    Paper reference: Ballús Santacana, "Universal Gluing and Contextual Choice: Certificate-Carrying Approximation, Functorial Evidence, and Effective Descent", arXiv:2506.22693 v3, Definition 5.1, Theorem
    5.2, Proposition 5.3.

    STATUS: IN-PROGRESS (see docs/FORMALIZATION_STATUS.md).

    ***CORRESPONDENCE MISMATCH — TO BE RECONCILED.***

    v3 Def 5.1 has FOUR clauses: (1) analytic Lipschitz map with a
    STORED FINITE DERIVATION in the evidence language; (2) name
    transformer with naturality; (3) finite-code realizer with defect
    witness; (4) distance-evidence transformer Θ_T with the STRICT
    identity/composition preservation property.

    The current Rocq record has FIVE components: it inserts a separate
    `rm_app_promote` (Ξ_T-style) transformer that Def 5.1 does not
    have, it does not represent the stored derivation as evidence, and
    it does not encode the strict identity/composition laws for
    `rm_dist_promote`. The extra transformer is a real object of the
    paper's constructions but sits at the theorem-proof layer of Thm
    5.2, not as a datum of Def 5.1.

    A follow-up commit will restructure this record to match the
    paper's four clauses (drop `rm_app_promote`; add a stored-
    derivation evidence-language field; add strict identity /
    composition laws for `rm_dist_promote`). Until then, do NOT read
    a Rocq value of `RealizableMap P G` as a v3 certifiably realizable
    Lipschitz map — it is a working proxy.

    This module formalizes:

    1. [RealizableMap P G] — Def 5.1 as a record collecting the
       five data items of a certifiably realizable Lipschitz map
       T : F(P) → F(G):

         (rm_T, rm_Lambda, rm_lipschitz) — the analytic map and its
           stored Lipschitz constant with the analytic estimate.
         (rm_name, rm_name_ok) — the uniform name transformer T^#
           with the naturality δ_G(T^# ν) = T(δ_F ν).
         (rm_code, rm_code_witness, rm_code_ok) — the uniform
           finite-code realizer τ_T with its acceptance witness.
         (rm_app_promote, rm_app_promote_ok) — the uniform
           approximation-evidence transformer Ξ_T.
         (rm_dist_promote, rm_dist_promote_ok) — the uniform
           distance-evidence transformer Θ_T.

    2. [lift_dist_accepted] and [analytic_lipschitz] — the
       achievable-bound-level content of Thm 5.2's metric-Lipschitz
       clause. Every accepted rational bound q on names in F lifts
       to an accepted rational bound Λ_T q on the transported names
       in G; the analytic distance is bounded by Λ_T times the
       source-side analytic distance.

    Not in this commit (all IN-PROGRESS in
    docs/FORMALIZATION_STATUS.md):

    - Object-level [T_* : EvidenceObject P → EvidenceObject G] as a
      real construction — Thm 5.2 requires assembling a target
      certificate system c' over rm_name(ν) from an input
      certificate system c over ν, invoking c at the reduced
      tolerance α_T(ε) = ε / (3 max(1, Λ_T)) and the code realizer
      at defect ε/3. This is a self-contained but non-trivial
      Q-arithmetic bookkeeping exercise, and is left for a
      subsequent commit so this checkpoint stays reviewable.
    - Morphism-level [T_* : EvidenceMorphism P c d → …] as a real
      function — same reason; the achievable-bound-level statement
      here already captures the mathematical content.
    - Prop 5.3 (identity is certifiably realizable; composition of
      realizable maps is realizable). Both need Q-arithmetic to
      match up rational bounds through Qmult_1_l etc.; deferred.
    - Cor 5.4 [CAn↑] category and Thm 5.6 [Grothendieck opfibration]
      — depend on the full functor construction.

    No axiom, no Admitted. *)

From Stdlib Require Import Reals QArith Lra Lia.
From UELAT.V3 Require Import Presentation Evidence.
Local Open Scope Q_scope.

Module V3_RealizableMap.

Import V3_Presentation.
Import V3_Evidence.

(** ** Def 5.1 — Certifiably realizable Lipschitz map. *)

Record RealizableMap (P G : Presentation) : Type := {
  (* --- analytic data --- *)
  rm_T             : F P -> F G;
  rm_Lambda        : Q;
  rm_Lambda_nonneg : (0 <= rm_Lambda)%Q;
  rm_lipschitz     : forall x y : F P,
                       (distF G (rm_T x) (rm_T y)
                        <= Q2R rm_Lambda * distF P x y)%R;

  (* --- name transformer T^# with the naturality equation --- *)
  rm_name          : NameF P -> NameF G;
  rm_name_ok       : forall nu : NameF P,
                       deltaF G (rm_name nu) = rm_T (deltaF P nu);

  (* --- finite-code realizer τ_T with defect witness E_T --- *)
  rm_code          : CodeF P -> Q -> CodeF G;
  rm_code_witness  : CodeF P -> Q -> list bool;
  rm_code_ok       :
    forall (p : CodeF P) (eta : Q),
      (0 < eta)%Q ->
      AppCheck G
        (rm_name (iotaF P p))
        (rm_code p eta)
        eta
        (rm_code_witness p eta) = true;

  (* --- approximation-evidence transformer Ξ_T --- *)
  rm_app_promote   :
    NameF P -> CodeF P -> Q -> list bool -> Q -> list bool;
  rm_app_promote_ok :
    forall nu p r V (eta : Q),
      (0 < eta)%Q ->
      AppCheck P nu p r V = true ->
      AppCheck G
        (rm_name nu)
        (rm_code p eta)
        (rm_Lambda * r + eta)
        (rm_app_promote nu p r V eta) = true;

  (* --- distance-evidence transformer Θ_T --- *)
  rm_dist_promote  :
    NameF P -> NameF P -> Q -> list bool -> list bool;
  rm_dist_promote_ok :
    forall nu mu r W,
      DistCheck P nu mu r W = true ->
      DistCheck G
        (rm_name nu)
        (rm_name mu)
        (rm_Lambda * r)
        (rm_dist_promote nu mu r W) = true
}.

Arguments rm_T             {P G} _ _.
Arguments rm_Lambda        {P G} _.
Arguments rm_Lambda_nonneg {P G} _.
Arguments rm_lipschitz     {P G} _ _ _.
Arguments rm_name          {P G} _ _.
Arguments rm_name_ok       {P G} _ _.
Arguments rm_code          {P G} _ _ _.
Arguments rm_code_witness  {P G} _ _ _.
Arguments rm_code_ok       {P G} _ _ _ _.
Arguments rm_app_promote   {P G} _ _ _ _ _ _.
Arguments rm_app_promote_ok {P G} _ _ _ _ _ _ _ _.
Arguments rm_dist_promote  {P G} _ _ _ _ _.
Arguments rm_dist_promote_ok {P G} _ _ _ _ _ _.

(** ** Achievable-bound-level content of Thm 5.2. *)

Section WithMap.
Variables (P G : Presentation).
Variable T : RealizableMap P G.

(** Every accepted distance witness in F lifts to an accepted
    distance witness in G at Λ_T-scaled bound. This is the
    concrete-witness form; the "Λ_T-Lipschitz on Lawvere metrics"
    statement of Thm 5.2 follows once d_Cert is a term. *)

Lemma lift_dist_accepted :
  forall (nu mu : NameF P) (q : Q),
    (exists W, DistCheck P nu mu q W = true) ->
    exists W',
      DistCheck G (rm_name T nu) (rm_name T mu)
                (rm_Lambda T * q) W' = true.
Proof.
  intros nu mu q [W HW].
  exists (rm_dist_promote T nu mu q W).
  apply rm_dist_promote_ok. exact HW.
Qed.

(** Analytic-level Lipschitz estimate on the transported names,
    obtained by combining [rm_lipschitz] with the name-transformer
    naturality [rm_name_ok]. *)

Lemma analytic_lipschitz :
  forall (nu mu : NameF P),
    (distF G (deltaF G (rm_name T nu)) (deltaF G (rm_name T mu))
     <= Q2R (rm_Lambda T)
        * distF P (deltaF P nu) (deltaF P mu))%R.
Proof.
  intros nu mu.
  rewrite !rm_name_ok.
  apply rm_lipschitz.
Qed.

End WithMap.

(** ** What this file DOES NOT contain

    - The full functor [T_* : Cert_ev(F) → Cert_ev(G)]. Object-level
      requires constructing a target certificate system over
      [rm_name T ν] from a source certificate system over ν, using
      the α_T bookkeeping of Thm 5.2. Morphism-level uses
      [rm_dist_promote] but must produce an [EvidenceMorphism] whose
      endpoints are the lifted objects. Both require the object
      lift first.
    - Prop 5.3 identity + composition of realizable maps. Needs
      Q-arithmetic manipulations that align 1*r with r etc.
    - Def 5.4 [CAn↑] category. Depends on Prop 5.3.
    - Thm 5.6 Grothendieck opfibration. Depends on Def 5.4 and the
      full functor of Thm 5.2.

    Correspondence with v3:

      Paper theorem:
        Definition 5.1 (Certifiably realizable Lipschitz map).
      Rocq definition:
        V3_RealizableMap.RealizableMap.
      Correspondence: NOT EXACT — see the mismatch notice in the
      module header. v3 Def 5.1 has FOUR clauses; this record has
      FIVE components. The current field-to-clause picture is:
        clause (1): rm_T, rm_Lambda, rm_Lambda_nonneg, rm_lipschitz
                    — but the STORED FINITE DERIVATION of the
                      Lipschitz estimate in the evidence language is
                      MISSING; only the analytic Prop is present.
        clause (2): rm_name, rm_name_ok                      — matches.
        clause (3): rm_code, rm_code_witness, rm_code_ok     — matches.
        clause (4): rm_dist_promote, rm_dist_promote_ok
                    — but the STRICT identity/composition laws for
                      Θ_T are MISSING.
        (no clause): rm_app_promote, rm_app_promote_ok
                    — an EXTRA field with no counterpart in Def 5.1.
                      It belongs to the proof of Thm 5.2, where it
                      should be DERIVED from the stored Lipschitz
                      derivation, the finite-code realizer defect, and
                      the triangle/weakening rules — not assumed.

      An earlier revision of this comment claimed "EXACT for all five
      clauses", contradicting both this module's header and
      docs/FORMALIZATION_STATUS.md. That claim was wrong and is
      retracted here.

      Paper theorem:
        Theorem 5.2 (Generic lifting theorem) — Lipschitz-on-Lawvere
        clause.
      Rocq theorems:
        V3_RealizableMap.lift_dist_accepted (achievable-bound lift),
        V3_RealizableMap.analytic_lipschitz (analytic Lipschitz on
        transported names).
      Correspondence: CHECKED-RESTRICTED. The Λ_T-scaling of
      achievable rational bounds is proved exactly. The metric
      Lipschitz statement d_Cert,G(T_*c, T_*d) ≤ Λ_T d_Cert,F(c,d)
      requires the object-level functor T_* and a d_Cert-as-term
      construction; both deferred. *)

End V3_RealizableMap.
