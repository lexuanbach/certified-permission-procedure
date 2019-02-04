Require Import msl.msl_standard.
Require Import share_dec_base.
Require Import borders.
Require Import FMaps.

Open Scope ord.

Module Type BOUND_MAP (sv : SV).
  (* Bounds *)
  Definition bound_type : Type := (share * share)%type.
  Definition bound_prop (b : bound_type) : Prop :=
    fst b <= snd b.
  Definition bound : Type := {b : bound_type | bound_prop b}.
  Definition o_bound (b: bound) : bound_type :=
    projT1 b.
  Definition p_bound (b : bound) : bound_prop (o_bound b) :=
    projT2 b.
  Axiom bound_eq_dec : EqDec bound.
  Existing Instance bound_eq_dec.
  Definition bound_map (f : share * share -> share * share) 
                       (Pf : forall rb, bound_prop rb -> bound_prop (f rb))
                       (b : bound) : bound :=
    exist _ (f (o_bound b)) (Pf (o_bound b) (p_bound b)).

  Program Definition initial_bound : bound := (bot,top).
  Next Obligation.
    red.
    simpl.
    rewrite <- leq_join_sub.
    auto with ba.
  Defined.
  
  (* Maps *)
  Parameter bmap : Type.
  Parameter initial_bmap : bmap.
  Parameter lookup : bmap -> sv.t -> bound.
  Parameter update : bmap -> sv.t -> bound -> bmap.
  Definition mappable : Type := 
    {f : bound -> bound | f initial_bound = initial_bound}.
  Definition app_mappable (f:mappable) : bound -> bound := proj1_sig f.
  Coercion app_mappable : mappable >-> Funclass.
  Definition mappable_prop (f:mappable) : f initial_bound = initial_bound :=
    proj2_sig f.  
  Parameter map : mappable -> bmap -> bmap.

  Axiom lookup_initial_bmap: forall v, 
    lookup (initial_bmap) v = initial_bound.
  Axiom lookup_update_eq: forall v b bm,
    lookup (update bm v b) v = b.
  Axiom lookup_update_neq: forall v b bm v',
    v <> v' ->
    lookup (update bm v b) v' = lookup bm v'.
  Axiom lookup_map : forall f bm v,
    lookup (map f bm) v = f (lookup bm v).
End BOUND_MAP.

Module BoundMap (sv : SV) <: BOUND_MAP(sv).

  Definition bound_type : Type := (share * share)%type.
  Definition bound_prop (b : share * share) : Prop :=
    fst b <= snd b.
  Definition bound : Type := {b : share * share | bound_prop b}.
  Definition o_bound (b: bound) : (share * share) :=
    projT1 b.
  Definition p_bound (b : bound) : bound_prop (projT1 b) :=
    projT2 b.

  Lemma bound_eq_dec : EqDec bound.
  Proof.
    do 2 intro.
    destruct a as [[l u] pf1].
    destruct a' as [[l' u'] pf2].
    case (eq_dec l l').
    case (eq_dec u u').
    left.
    apply exist_ext. congruence.
    right.
    intro.
    inversion H. auto.
    right.
    intro.
    inversion H.
    auto.
  Defined.
  Existing Instance bound_eq_dec.

  Definition bound_map (f : share * share -> share * share) 
                       (Pf : forall rb, bound_prop rb -> bound_prop (f rb))
                       (b : bound) : bound :=
    exist _ (f (o_bound b)) (Pf (o_bound b) (p_bound b)).
  Program Definition initial_bound : bound := (bot,top).
  Next Obligation.
    red.
    simpl.
    rewrite <- leq_join_sub.
    auto with ba.
  Defined.

(* ***** *)

  (* This lemma may or may not be useful enough in general... *)

  Lemma gt_pf {A} `{O : borders.Ord A} `{TO: @TOrd A O} : forall x y : A,
    x <> y ->
    ~ (x < y) ->
    y < x.
  Proof.
    intros.
    destruct (tord_total x y). destruct H0. split; trivial.
    split; trivial. intro; auto. 
  Qed.

  Module SV_MiniOrderedType <: MiniOrderedType.
    Definition t := sv.t.
    Definition eq (t1 t2 : t) := t1 = t2.
    Definition lt (t1 t2 : t) := sord t1 t2.
    
    Lemma eq_refl : forall x : t, eq x x.
    Proof. reflexivity. Qed.
    Lemma eq_sym : forall x y : t, eq x y -> eq y x.
    Proof. symmetry. trivial. Qed.
    Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
    Proof. intros. transitivity y; trivial. Qed.
    
    Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
    Proof. apply sord_trans. Qed.
    
    Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
    Proof. intros. apply sord_neq in H. trivial. Qed.

    Definition compare (x y : t) : Compare lt eq x y :=
      match eq_dec x y with
        | left peq => EQ peq
        | right pnq => match sv.t_lt_dec x y with
          | left plt => LT plt
          | right pnlt => GT (gt_pf _ _ pnq pnlt)
        end
      end.

    Hint Immediate eq_sym.
    Hint Resolve eq_refl eq_trans lt_not_eq lt_trans.
  End SV_MiniOrderedType.

  Module SV_OrderedType <: OrderedType := MOT_to_OT(SV_MiniOrderedType).

  Module ContextMap := Make(SV_OrderedType).
  
  Definition bmap : Type := ContextMap.t bound.
  Definition initial_bmap : bmap := ContextMap.empty bound.
  Definition lookup (bm : bmap) (v : sv.t) : bound :=
    match ContextMap.find v bm with Some b => b | None => initial_bound end.
  Definition update (bm : bmap) (v : sv.t) (b : bound) : bmap :=
    ContextMap.add v b bm.

  Definition mappable : Type := 
    {f : bound -> bound | f initial_bound = initial_bound}.
  Definition app_mappable (f:mappable) : bound -> bound := proj1_sig f.
  Coercion app_mappable : mappable >-> Funclass.
  Definition mappable_prop (f:mappable) : f initial_bound = initial_bound :=
    proj2_sig f.  
  Definition map (f : mappable) (bm : bmap) : bmap :=
    ContextMap.map f bm.
  (* Not in the interface right now, but could be added if useful *)
  Definition cm_map (f : share * share -> share * share) 
                    (Pf : forall rb, bound_prop rb -> bound_prop (f rb))
                    (m : ContextMap.t bound) : ContextMap.t bound :=
    ContextMap.map (bound_map f Pf) m.

  Lemma lookup_initial_bmap: forall v, lookup (initial_bmap) v = initial_bound.
  Proof. auto. Qed.
  
  Lemma lookup_update_eq: forall v b bm,
    lookup (update bm v b) v = b.
  Proof.
    intros. unfold lookup, update.
    assert (ContextMap.MapsTo v b (ContextMap.add v b bm)). apply ContextMap.add_1. trivial.
    apply ContextMap.find_1 in H.
    rewrite H.
    trivial.
  Qed.
  
  Lemma lookup_update_neq: forall v b bm v',
    v <> v' ->
    lookup (update bm v b) v' = lookup bm v'.
  Proof.
    intros. unfold lookup, update.
    case_eq (ContextMap.find (elt := bound) v' bm); intros.
    apply ContextMap.find_2 in H0.
    assert (ContextMap.MapsTo v' b0 (ContextMap.add v b bm)).
      apply ContextMap.add_2; trivial.
    apply ContextMap.find_1 in H1.
    rewrite H1. trivial.
    case_eq (ContextMap.find (elt := bound) v' (ContextMap.add v b bm)); trivial.
    intros.
    apply ContextMap.find_2 in H1.
    apply ContextMap.add_3 in H1; trivial.
    apply ContextMap.find_1 in H1. rewrite H0 in H1. disc.
  Qed.

  Lemma lookup_map : forall f bm v,
    lookup (map f bm) v = f (lookup bm v).
  Proof with auto.
    intros. unfold lookup, map.
    case_eq (ContextMap.find (elt := bound) v bm); intros.
    apply ContextMap.find_2 in H.
    apply (@ContextMap.map_1 _ _ _ _ _ f) in H.
    apply ContextMap.find_1 in H. rewrite H...
    case_eq (@ContextMap.find bound v (ContextMap.map f bm)); intros.
    2: symmetry; apply mappable_prop.
    apply ContextMap.find_2 in H0.
    assert (ContextMap.In v (ContextMap.map f bm)).
      exists b...
    apply ContextMap.map_2 in H1.
    destruct H1.
    apply ContextMap.find_1 in H1.
    rewrite H in H1; disc.
  Qed.
End BoundMap.

Module BoundMap_nat : BOUND_MAP(sv_nat) :=
  BoundMap(sv_nat).







