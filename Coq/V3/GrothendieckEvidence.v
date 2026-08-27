(** GrothendieckEvidence.v -- v3 Proposition 4.7.

    The manuscript invokes only the standard Grothendieck construction for a
    strict covariant Cat-valued assignment.  This file formalizes the structural
    content needed there: strict fibre transport, total objects, chosen lifts,
    split identity/composition laws, and the universal factor in the target
    fibre.  No probes-models adjunction is involved.
*)

Module UELAT_V3_GrothendieckEvidence.

Record BaseCategory := {
  BObj : Type;
  BHom : BObj -> BObj -> Type;
  bid : forall x, BHom x x;
  bcomp : forall {x y z}, BHom y z -> BHom x y -> BHom x z
}.

Arguments BObj _ : clear implicits.
Arguments BHom {b} _ _.
Arguments bid {b} _.
Arguments bcomp {b x y z} _ _.

(** Object and morphism data of a strict Cat-valued assignment.  The base and
    fibre category laws themselves are semantic background; the equations used
    by the split construction are stored explicitly. *)
Record StrictIndexed (B : BaseCategory) := {
  fibre_obj : BObj B -> Type;
  fibre_hom : forall x, fibre_obj x -> fibre_obj x -> Type;
  fibre_id : forall x (a : fibre_obj x), fibre_hom x a a;

  push_obj : forall {x y}, BHom x y -> fibre_obj x -> fibre_obj y;
  push_hom : forall {x y} (f : BHom x y) {a b},
      fibre_hom x a b -> fibre_hom y (push_obj f a) (push_obj f b);

  push_id : forall x (a : fibre_obj x), push_obj (bid x) a = a;
  push_comp : forall x y z (f : BHom x y) (g : BHom y z) (a : fibre_obj x),
      push_obj (bcomp g f) a = push_obj g (push_obj f a)
}.

Arguments fibre_obj {B} _ _.
Arguments fibre_hom {B} _ _ _ _.
Arguments fibre_id {B} _ _ _.
Arguments push_obj {B s x y} _ _.
Arguments push_hom {B s x y} _ _.
Arguments push_id {B} s x a.
Arguments push_comp {B} s x y z f g a.

Definition transport_source
    {A : Type} (P : A -> Type) {x y : A}
    (e : x = y) (u : P x) : P y :=
  match e with eq_refl => u end.

Section Construction.
  Context {B : BaseCategory} (I : StrictIndexed B).

  Record TotalObject := {
    total_base : BObj B;
    total_fibre : fibre_obj I total_base
  }.

  Record ChosenLift {x y : BObj B}
      (f : BHom x y) (a : fibre_obj I x) := {
    lift_target : fibre_obj I y;
    lift_target_is_push : lift_target = push_obj f a
  }.

  Arguments lift_target {x y f a} _.
  Arguments lift_target_is_push {x y f a} _.

  Definition chosen_lift {x y : BObj B}
      (f : BHom x y) (a : fibre_obj I x) : ChosenLift f a :=
    {| lift_target := push_obj f a;
       lift_target_is_push := eq_refl |}.

  Theorem chosen_lift_identity : forall x (a : fibre_obj I x),
    lift_target (chosen_lift (bid x) a) = a.
  Proof.
    intros. simpl. apply push_id.
  Qed.

  Theorem chosen_lift_composition :
    forall x y z (f : BHom x y) (g : BHom y z) (a : fibre_obj I x),
      lift_target (chosen_lift (bcomp g f) a)
      = lift_target (chosen_lift g (lift_target (chosen_lift f a))).
  Proof.
    intros. simpl. apply push_comp.
  Qed.

  Record TotalArrow (a b : TotalObject) := {
    total_arrow_base : BHom (total_base a) (total_base b);
    total_arrow_fibre :
      fibre_hom I (total_base b)
        (push_obj total_arrow_base (total_fibre a))
        (total_fibre b)
  }.

  (** The chosen arrow over f has identity fibre component. *)
  Definition chosen_total_lift
      {x y : BObj B} (f : BHom x y) (a : fibre_obj I x) :
      TotalArrow
        {| total_base := x; total_fibre := a |}
        {| total_base := y; total_fibre := push_obj f a |}.
  Proof.
    refine (@Build_TotalArrow
      {| total_base := x; total_fibre := a |}
      {| total_base := y; total_fibre := push_obj f a |}
      f _).
    cbn. exact (fibre_id I y (push_obj f a)).
  Defined.

  (** Universal factor in the target fibre.  Given an arrow whose base factors
      as g o f, strict functoriality identifies its fibre source with
      g_!(f_!a); transport along that equality yields the unique factor used by
      the Grothendieck opcartesian lift. *)
  Definition opcartesian_factor
      {x y z : BObj B}
      (f : BHom x y) (g : BHom y z)
      (a : fibre_obj I x) (c : fibre_obj I z)
      (h : fibre_hom I z (push_obj (bcomp g f) a) c) :
      fibre_hom I z (push_obj g (push_obj f a)) c :=
    transport_source
      (fun s => fibre_hom I z s c)
      (push_comp I x y z f g a) h.

  Theorem opcartesian_factor_exists_unique :
    forall x y z (f : BHom x y) (g : BHom y z)
           (a : fibre_obj I x) (c : fibre_obj I z)
           (h : fibre_hom I z (push_obj (bcomp g f) a) c),
      exists! k : fibre_hom I z (push_obj g (push_obj f a)) c,
        k = opcartesian_factor f g a c h.
  Proof.
    intros.
    exists (opcartesian_factor f g a c h).
    - reflexivity.
    - intros y0 Hy0. exact Hy0.
  Qed.

  Record SplitOpfibrationData := {
    split_lift : forall {x y}, BHom x y -> fibre_obj I x -> fibre_obj I y;
    split_lift_id : forall x a, split_lift (bid x) a = a;
    split_lift_comp : forall x y z (f : BHom x y) (g : BHom y z) a,
        split_lift (bcomp g f) a = split_lift g (split_lift f a);
    split_factor : forall x y z (f : BHom x y) (g : BHom y z)
                          (a : fibre_obj I x) (c : fibre_obj I z),
        fibre_hom I z (push_obj (bcomp g f) a) c ->
        fibre_hom I z (push_obj g (push_obj f a)) c
  }.

  Definition grothendieck_split_opfibration : SplitOpfibrationData.
  Proof.
    refine {| split_lift := fun _ _ f a => push_obj f a;
              split_factor := fun _ _ _ f g a c h =>
                opcartesian_factor f g a c h |}.
    - apply push_id.
    - apply push_comp.
  Defined.

End Construction.

End UELAT_V3_GrothendieckEvidence.
