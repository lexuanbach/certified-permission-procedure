Require Import Orders.
Require Import List.
Require Import borders.
Require Import base.
Require Import share_equation_system.
Require Import share_dec_base.
Require Import uf.UF_interface.
Require Import part.partition_base.
Require Import part.partition_interface.
Require Import part.partition_implementation.

Module Input_of_SV (sv : SV) <: INPUT with Definition e := sv.t.

 Definition e := sv.t.
 Definition e_eq_dec : EqDec e := sv.t_eq_dec.
 Existing Instance e_eq_dec.

End Input_of_SV.

Module OrderedType_of_SV (sv : SV) <: OrderedType with Definition t := sv.t
                                                with Definition eq := @Logic.eq sv.t.
  Definition t := sv.t.
  Definition eq := @Logic.eq t.
  Instance eq_equiv : Equivalence eq := _.
  Definition lt := fun (t1 t2:t) => (t1 < t2)%ord.
  Lemma lt_strorder : StrictOrder lt.
   Proof.
    split;repeat intro.
    apply sord_neq in H.
    apply H. trivial.
    apply sord_trans with y;trivial.
   Qed.
  Lemma lt_compat : Morphisms.Proper (eq ==> eq ==> iff) lt.
   Proof.
    repeat intro.
    inv H. inv H0. tauto.
   Qed.
  Definition compare := fun (t1 t2:t) =>
    if sv.t_leq_dec t1 t2
    then (if sv.t_lt_dec t1 t2 then Lt else Eq)
    else Gt.
  Lemma compare_spec :
    forall x y : t, CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
   Proof.
    intros.
    unfold compare.
    icase (sv.t_leq_dec x y);
    icase (sv.t_lt_dec x y).
    apply CompEq.
    generalize (sv.t_eq_dec x y);intro.
    destruct H. trivial. elimtype False. apply n. split;tauto.
    apply CompGt.
    elimtype False. apply n. apply sord_leq;trivial.
    apply CompGt.
    assert ((y <= x)%ord).
    generalize (sv.t_leq_dec y x);intro.
    icase H.
    generalize (sv.t_tord x y);intro. elimtype False. tauto.
    split;auto.
    intro. apply n. rewrite H0. apply ord_refl.
   Qed.

  Definition eq_dec: forall x y : t, {eq x y} + {~ eq x y}
    := sv.t_eq_dec.

End  OrderedType_of_SV.

Instance vars_transform {A B} (VAB : share_dec_base.varsable A B) : varsable A B.
constructor. intros. apply (share_dec_base.vars X).
Defined.
Instance eval_transform {A B} (E : share_dec_base.evalable A B) : evalable A B.
constructor. intros. apply (share_dec_base.eval X X0).
Defined.
Instance EqDec_transform {A} {ED : eq_dec.EqDec A} : EqDec A := ED.
(*
Instance override_transform {A B} `{eq_dec.EqDec A}: overridable (A -> B) A := 
 Overridable (@share_dec_base.override A B _).
*)
Module Partition_Input_of_SV (sv : SV) 
                             (es : EQUATION_SYSTEM sv) 
                             (esf : SYSTEM_FEATURES sv es) <: 
                             PARTITION_INPUT.

  Definition equation := es.equation.
  Instance eqn_eq_dec : EqDec equation := _.
  Definition var := es.var.
  Instance var_eq_dec : EqDec var := _.
  Instance varsable_equation : varsable equation var := _.

  Definition context := es.context.
  Definition a_context : context := fun v => es.dom.bot.
  Instance context_override : overridable context var := Overridable (@share_dec_base.override es.var es.s _).
  Instance eval : evalable context equation := _.
  
  Lemma eval_override_disjoint_object: forall
    (l :list var) (ctx ctx' : context) (obj : es.object),
    disjoint l (share_dec_base.vars obj) -> get ([l => ctx']ctx) obj = get ctx obj.
  Proof.
   intros. icase obj.
   unfold disjoint in H;simpl in *.
   spec H v.
   assert (~In v l) by tauto.
   rewrite override_not_in;trivial.
  Qed.

  Lemma eval_override_disjoint: forall 
    (l : list var) (ctx ctx' : context) (eqn : equation),
    disjoint l (vars eqn) ->
    (ctx |= eqn <-> ([l => ctx'] ctx) |= eqn).
  Proof.
   intros.
   destruct eqn as [[obj1 obj2] obj3].
   simpl in *.
   repeat rewrite disjoint_app_iff in H.
   destruct H as [H0 [H1 H2]].
   generalize (eval_override_disjoint_object _ ctx ctx' _ H0);intro.
   generalize (eval_override_disjoint_object _ ctx ctx' _ H1);intro.
   generalize (eval_override_disjoint_object _ ctx ctx' _ H2);intro.
   simpl in *. rewrite H. rewrite H3. rewrite H4. tauto.
  Qed.

  Lemma eval_override_sublist_object: forall
    (l : list var) (ctx ctx' : context) (obj : es.object),
    sublist (share_dec_base.vars obj) l ->
    get ([l => ctx] ctx') obj = get ctx obj.
  Proof.
   intros.
   icase obj.
   unfold sublist in H;simpl in *.
   spec H v.
   assert (In v l) by tauto.
   rewrite override_in;trivial.
  Qed.

  Lemma eval_override_sublist: forall
    (l : list var) (ctx ctx' : context) (eqn : equation),
    ctx |= eqn -> sublist (vars eqn) l ->
    ([l => ctx] ctx') |= eqn.
  Proof.
   intros.
   destruct eqn as [[obj1 obj2] obj3].
   simpl in *.
   repeat rewrite sublist_app_iff in H0.
   destruct H0 as [? [? ?]].
   generalize (eval_override_sublist_object _ ctx ctx' _ H0);intro.
   generalize (eval_override_sublist_object _ ctx ctx' _ H1);intro.
   generalize (eval_override_sublist_object _ ctx ctx' _ H2);intro.
   simpl in *. rewrite H3. rewrite H4. rewrite H5. tauto.
  Qed.
  
End Partition_Input_of_SV.

Inductive eqnS {A B C}: Type :=
 |NZV : A -> eqnS
 |EL  : B -> eqnS
 |EQ  : C -> eqnS.

Instance EqDec_eqnS (A B C : Type) `{EqDec A} `{EqDec B} `{EqDec C} : EqDec (@eqnS A B C).
 Proof with try tauto;try congruence.
 repeat intro.
 icase a;icase a'.
 destruct (eq_dec a a0);subst...
 right... right... right... right...
 destruct (eq_dec b b0);subst...
 right... right... right... right...
 destruct (eq_dec c c0);subst... right...
 Defined.

Instance varsable_eqnS (A B C: Type) `{varsable B A} 
 `{varsable C A}: varsable (@eqnS A B C) A.
 constructor. intros. destruct X. apply (a::nil).
 apply (vars b).
 apply (vars c).
Defined.

Instance evalable_eqnS  (A B C D: Type) 
 `{evalable D A}
 `{evalable D B}
 `{evalable D C}:
  evalable D (@eqnS A B C).
 constructor. intros.
 destruct X0.
 apply (X |= a)%part_scope.
 apply (X |= b)%part_scope.
 apply (X |= c)%part_scope.
Defined.

Module Partition_Input_of_SV_nz (sv : SV) (es : EQUATION_SYSTEM sv) 
                                (esf : SYSTEM_FEATURES sv es) <: 
                                PARTITION_INPUT 
                                with Definition equation := @eqnS es.var es.equality es.equation
                                with Definition var := es.var
                                with Definition context := es.context
                                with Definition eval := evalable_eqnS es.var es.equality es.equation es.context.
 
  Definition equation := @eqnS es.var es.equality es.equation.
  Instance obj_eq_dec : EqDec es.object := _.
  Instance eqn_eq_dec : EqDec equation := _.

  Definition var := es.var.
  Instance var_eq_dec : EqDec var := _.
  Instance varsable_equation : varsable equation var := _.

  Definition context := es.context.
  Definition a_context : context := fun v => es.dom.bot.
  Instance context_override : overridable context var := Overridable (@share_dec_base.override es.var es.s _).
  Instance eval : evalable context equation := _.

  Lemma eval_override_disjoint_object: forall
    (l :list var) (ctx ctx' : context) (obj : es.object),
    disjoint l (vars obj) -> get ([l => ctx'] ctx) obj = get ctx obj.
  Proof with tauto.
   intros.
   icase obj.
   spec H v. simpl in *.
   assert (~In v l) by tauto.
   rewrite override_not_in...
  Qed.

  Lemma eval_override_disjoint: forall 
    (l : list var) (ctx ctx' : context) (eqn : equation),
    disjoint l (vars eqn) ->
    (ctx |= eqn <-> ([l => ctx'] ctx) |= eqn)%part_scope.
  Proof with tauto.
   intros.
   icase eqn.
   spec H v. simpl in *.
   assert (~In v l) by tauto.
   rewrite override_not_in...
   destruct e as [obj1 obj2].
   simpl in *.
   rewrite disjoint_app_iff in H.
   destruct H as [H0 H1].
   generalize (eval_override_disjoint_object _ ctx ctx' _ H0);intro.
   generalize (eval_override_disjoint_object _ ctx ctx' _ H1);intro.
   simpl in *. rewrite H. rewrite H2. tauto. 
   destruct e as [[obj1 obj2] obj3].
   simpl in *.
   repeat rewrite disjoint_app_iff in H.
   destruct H as [H0 [H1 H2]].
   generalize (eval_override_disjoint_object _ ctx ctx' _ H0);intro.
   generalize (eval_override_disjoint_object _ ctx ctx' _ H1);intro.
   generalize (eval_override_disjoint_object _ ctx ctx' _ H2);intro.
   simpl in *.
   rewrite H. rewrite H3. rewrite H4. tauto.
  Qed.

  Lemma eval_override_sublist_object: forall
    (l : list var) (ctx ctx' : context) (obj : es.object),
    sublist (vars obj) l ->
    get ([l => ctx] ctx') obj = get ctx obj.
  Proof with tauto.
   intros.
   icase obj.
   spec H v. simpl in *.
   assert (In v l) by tauto.
   rewrite override_in...
  Qed.

  Lemma eval_override_sublist: forall
    (l : list var) (ctx ctx' : context) (eqn : equation),
    (ctx |= eqn)%part_scope -> sublist (vars eqn) l ->
    (([l => ctx] ctx') |= eqn)%part_scope.
  Proof with tauto.
   intros.
   icase eqn. 
   spec H0 v. simpl in *.
   assert (In v l) by tauto.
   rewrite override_in...
   destruct e as [obj1 obj2].
   simpl in *.
   repeat rewrite sublist_app_iff in H0.
   destruct H0 as [? ?].
   generalize (eval_override_sublist_object _ ctx ctx' _ H0);intro.
   generalize (eval_override_sublist_object _ ctx ctx' _ H1);intro.
   simpl in *. rewrite H2. rewrite H3. tauto.
   destruct e as [[obj1 obj2] obj3].
   simpl in *.
   repeat rewrite sublist_app_iff in H0.
   destruct H0 as [? [? ?]].
   generalize (eval_override_sublist_object _ ctx ctx' _ H0);intro.
   generalize (eval_override_sublist_object _ ctx ctx' _ H1);intro.
   generalize (eval_override_sublist_object _ ctx ctx' _ H2);intro.
   simpl in *. rewrite H3. rewrite H4. rewrite H5. tauto.
  Qed.
  
End Partition_Input_of_SV_nz.

 Inductive varT {A B}: Type :=
 |Univ : A -> varT
 |Ex : A -> B -> varT.

 Instance varT_eq_dec {A B} `{EqDec A} `{EqDec B} : EqDec (@varT A B).
 Proof with try congruence.
  repeat intro. icase a; icase a'.
  destruct (eq_dec a a0).
  left... right...
  right... right...
  destruct (eq_dec a a0).
  destruct (eq_dec b b0).
  left... right... right...
 Defined.

Module Input_of_SV_nz_ex (sv : SV) <: INPUT with Definition e := @varT sv.t bool.

 Definition e := @varT sv.t bool.
 Instance e_eq_dec : EqDec e := _.

End Input_of_SV_nz_ex.

Module OrderedType_of_SV_nz_ex (sv : SV) <: OrderedType with Definition t := @varT sv.t bool
                                                      with Definition eq := @Logic.eq (@varT sv.t bool).

  Definition t := @varT sv.t bool.
  Definition eq := @Logic.eq (@varT sv.t bool).
  Instance eq_equiv : Equivalence eq := _.
  Definition lt := fun (t1 t2: t) => 
  match (t1,t2) with 
   |(Univ v1, Univ v2) => (v1<v2)%ord 
   |(Ex v1 b1, Ex v2 b2) => match (b1,b2) with
                            |(true,true)
                            |(false,false) => (v1<v2)%ord
                            |(true,false) => False
                            |(false,true) => True
                            end 
   |(Ex v1 b1, Univ v2) => True
   |(Univ v1, Ex v2 b2) => False
  end.
  Lemma lt_strorder : StrictOrder lt.
   Proof with try tauto.
    split;repeat intro.
    destruct x as [x|x b];
    try icase b;
    apply sord_neq in H...
    destruct x as [x|x b1];
    destruct y as [y|y b2];
    destruct z as [z|z b3];
    try icase b1;try icase b2;try icase b3;
    try apply sord_trans with y...
   Qed.

  Instance lt_compat : Morphisms.Proper (eq ==> eq ==> iff) lt.
   Proof with tauto.
    repeat intro.
    inv H. inv H0...
   Qed.
  Definition compare := fun (t1 t2:t) =>
   match (t1 ,t2) with 
   |(Univ v1, Univ v2)=> if sv.t_leq_dec v1 v2
                          then (if sv.t_lt_dec v1 v2 then Lt else Eq)
                          else Gt
   |(Ex v1 b1, Ex v2 b2) => match (b1,b2) with
                            |(true,true)
                            |(false,false) => if sv.t_leq_dec v1 v2
                                              then (if sv.t_lt_dec v1 v2 then Lt else Eq)
                                              else Gt
                            |(false,true) => Lt
                            |(true,false) => Gt
                            end
   |(Ex v1 b1, Univ v2) => Lt
   |(Univ v1, Ex v2 b2) => Gt
   end.

  Lemma compare_spec :
    forall x y : t, CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
  Proof with auto.
    intros.
    unfold compare.
    destruct x as [x|x b1];destruct y as [y|y b2]. 
    icase (sv.t_leq_dec x y);
    icase (sv.t_lt_dec x y).
    apply CompEq.
    unfold eq. f_equal.
    generalize (eq_dec x y);intro.
    destruct H... elimtype False. apply n. split...
    apply CompGt.
    elimtype False. apply n. apply sord_leq...
    apply CompGt.
    assert ((y <= x)%ord).
    generalize (sv.t_leq_dec y x);intro.
    icase H.
    generalize (sv.t_tord x y);intro. elimtype False. tauto.
    split;auto.
    intro. apply n. rewrite H0. apply ord_refl.
    apply CompGt.  
    unfold lt...
    apply CompLt.
    unfold lt...
    icase (sv.t_leq_dec x y);
    icase (sv.t_lt_dec x y);
    icase b1;icase b2;
    try apply CompEq;
    try apply CompLt; try unfold lt;
    try apply CompGt; try unfold gt...
    unfold eq. f_equal.
    generalize (eq_dec x y);intro;
    destruct H... elimtype False. apply n. split...
    unfold eq. f_equal.
    generalize (eq_dec x y);intro;
    destruct H... elimtype False. apply n. split...
    assert ((y <= x)%ord).
    generalize (sv.t_leq_dec y x);intro.
    icase H.
    generalize (sv.t_tord x y);intro. elimtype False. tauto.
    split;auto.
    intro. apply n. rewrite H0. apply ord_refl.
    assert ((y <= x)%ord).
    generalize (sv.t_leq_dec y x);intro.
    icase H.
    generalize (sv.t_tord x y);intro. elimtype False. tauto.
    split;auto.
    intro. apply n. rewrite H0. apply ord_refl.
    assert ((y <= x)%ord).
    generalize (sv.t_leq_dec y x);intro.
    icase H.
    generalize (sv.t_tord x y);intro. elimtype False. tauto.
    split;auto.
    intro. apply n. rewrite H0. apply ord_refl.
    assert ((y <= x)%ord).
    generalize (sv.t_leq_dec y x);intro.
    icase H.
    generalize (sv.t_tord x y);intro. elimtype False. tauto.
    split;auto.
    intro. apply n. rewrite H0. apply ord_refl.
  Qed.

  Instance eq_dec: EqDec t := _.

End  OrderedType_of_SV_nz_ex.

 Instance varsable_eqnS' (V EL EQ B : Type) `{varsable EL V} `{varsable EQ V} `{EqDec V} : varsable ((@eqnS V EL EQ)*(list V)*B) (@varT V B).
  constructor. repeat intro.
  destruct X as [[? ?] ?].
  destruct e.
  destruct (in_dec eq_dec v l).
  apply ((Ex v b)::nil).
  apply ((Univ v)::nil).
  apply (map (fun v => if (in_dec eq_dec v l) then Ex v b else Univ v) (vars e)).
  apply (map (fun v => if (in_dec eq_dec v l) then Ex v b else Univ v) (vars e)).
 Defined.

 Definition extract_Univ {A B} :=
  fun (l : list (@varT A B)) =>
   filter (fun (vT : @varT A B) => match vT with Univ v => true |_ => false end) l.

 Lemma extract_Univ_correct: forall {A B} (l : list (@varT A B)) vt,
  In vt (extract_Univ l) <-> In vt l /\ exists v, vt = Univ v.
 Proof with try tauto.
  intros.
  unfold extract_Univ.
  split;intros.
  apply filter_In in H.
  destruct H.
  split... destruct vt. inv H0.
  exists a... inv H0.
  destruct H as [? [? ?]].
  apply filter_In.
  split... inv H0...
 Qed.

 Definition varT_unwrap {A B} := 
  fun (vT : @varT A B) =>
  match vT with
  |Univ v => v
  |Ex v b => v
  end.

 Lemma unwrap_extract: forall {A B} l (v : A),
  In (@Univ A B v) l <-> In v (map varT_unwrap (extract_Univ l)).
 Proof with try tauto.
  induction l;intros.
  simpl...
  split;intros.
  destruct H. subst.
  simpl. left...
  apply IHl in H.
  simpl. icase a...
  simpl.  right...
  simpl in H. icase a.
  destruct H. subst.
  simpl. left...
  simpl. right. apply IHl...
  simpl. right. apply IHl...
 Qed.
    
 Module Partition_Input_of_SV_nz_ex (sv : SV) (es : EQUATION_SYSTEM sv) (esf : SYSTEM_FEATURES sv es) <:
                                     PARTITION_INPUT 
                                     with Definition var := @varT es.var bool
                                     with Definition equation := ((@eqnS es.var es.equality es.equation)*(list es.var)*bool)%type.

  Definition equation := ((@eqnS es.var es.equality es.equation)*(list es.var)*bool)%type.

  Instance eqn_eq_dec : EqDec equation.
  Proof with congruence.
   repeat intro.
   destruct a as [[eqn1 l1] b1]; destruct a' as [[eqn2 l2] b2].
   destruct (eq_dec eqn1 eqn2).
   destruct (list_eq_dec eq_dec l1 l2).
   destruct (Bool.bool_dec b1 b2).
   left... right... right... right...
  Defined.

  Definition var := @varT sv.t bool.
  Instance var_eq_dec : EqDec var := _.
  Instance varsable_equation : varsable equation var := _ . 
  
  Definition context := es.context.
  Definition a_context : context := fun v => es.dom.bot.

  Instance eval : evalable context equation.
   constructor. intros. apply True.
  Defined.

  Definition ctx_override 
  (ctx ctx' : context) (l :list var) : context := ctx.
  Instance context_override : overridable context var := Overridable ctx_override.

  Lemma eval_override_disjoint: forall 
    (l : list var) (ctx ctx' : context) (eqn : equation),
    disjoint l (vars eqn) ->
    (ctx |= eqn <-> ([l => ctx'] ctx) |= eqn)%part_scope.
  Proof with try tauto.
   intros. simpl...
  Qed.

  Lemma eval_override_sublist: forall
    (l : list var) (ctx ctx' : context) (eqn : equation),
    (ctx |= eqn)%part_scope -> sublist (vars eqn) l ->
    (([l => ctx] ctx') |= eqn)%part_scope.
  Proof with try tauto.
   intros. simpl...
  Qed.
  
End Partition_Input_of_SV_nz_ex.

Module System_Partition (sv : SV) (Import es : EQUATION_SYSTEM sv) (Import esf : SYSTEM_FEATURES sv es).

 Definition equationS := @eqnS es.var es.equality es.equation.

 Class eqnS_transform (A B C D : Type) : Type :=
  transformS : D -> @eqnS A B C.

 Class eqnS_transformB (A B C: Type) : Type := {
  transformSB : @eqnS A B C -> (A + (B + C)) :=
    fun eqn => match eqn with
               |NZV v => inl v
               |EL eql => inr (inl eql)
               |EQ eqn => inr (inr eqn)
              end
  }.
 Implicit Arguments inl [A B].
 Implicit Arguments inr [A B].

 Definition eqnS_list_transformB {A B C : Type} `{eqnS_transformB A B C} (l : list (@eqnS A B C)) : (list A * (list B * list C)) :=
  fold_right (fun eqn tl' => match transformSB eqn with
                             |inl a => (a::(fst tl'), snd tl') 
                             |inr (inl b) => (fst tl', (b::(fst (snd tl')), snd (snd tl')))
                             |inr (inr c) => (fst tl', ((fst (snd tl')), c::(snd (snd tl'))))
                             end
              ) (nil,(nil,nil)) l.

 Lemma transformSB_eval: forall {A B C D}  `{evalable D A} 
  `{evalable D B} `{evalable D C} `{eqnS_transformB A B C}
  ctx (l : list (@eqnS A B C)) l1 l2 l3 ,
  eqnS_list_transformB l = (l1, (l2, l3)) ->
  (ctx |= l <-> ctx |= l1 /\ ctx |= l2 /\ ctx |= l3)%part_scope.
 Proof with try tauto.
  induction l;intros;inv H3;simpl...
  destruct (eqnS_list_transformB l) as [la [lb lc]].
  icase a;inv H5;simpl.
  spec IHl la l2 l3...
  spec IHl l1 lb l3...
  spec IHl l1 l2 lc...
 Qed.

 Class list_map {A B} (f : A -> B) := {
  lmap : list A -> list B := map f}.

 Class preserved_eval {A B} (C : Type) (f : A -> B) `{evalable C A} `{evalable C B}: Type :=
  eval_map : forall a c, (c |= a <-> c |= (f a))%part_scope.

 Instance eqnS_list_transform {A B C D} `{eqnS_transform A B C D} : list_map transformS.
 constructor. Defined.
 
 Instance preserved_eval_list {A B} (C : Type) (f : A -> B) 
 `{evalable C A} `{evalable C B} `{@preserved_eval A B C f _ _ } `{@list_map A B f}: 
  preserved_eval C lmap.
 Proof with try tauto.
  repeat intro. induction a;intros...
  spec H1 a c;simpl in *...
 Defined.

 Instance var2eqnS : eqnS_transform var equality equation var := fun v => NZV v.
 Instance eql2eqnS : eqnS_transform var equality equation equality := fun eql => EL eql.
 Instance eqn2eqnS : eqnS_transform var equality equation equation := fun eqn => EQ eqn.
 Instance eqnSback : eqnS_transformB var equality equation. constructor. Defined.

 Instance var2eqnS_eval : @preserved_eval var equationS context transformS _ _.
 Proof with try tauto. repeat intro... Defined.
 Instance eql2eqnS_eval : @preserved_eval equality equationS context transformS _ _.
 Proof with try tauto. repeat intro... Defined.
 Instance eqn2eqnS_eval : @preserved_eval equation equationS context transformS _ _.
 Proof with try tauto. repeat intro... Defined.

 Lemma eval_app : forall {A B} `{evalable A B} (l1 l2 : list B) (ctx : A),
  eval_list ctx (l1++l2) <-> eval_list ctx l1 /\ eval_list ctx l2.
 Proof with try tauto.
  induction l1;intros;simpl...
  rewrite IHl1...
 Qed.

 Definition ses2eqnS (ses : sat_equation_system) : list equationS := 
  (lmap (sat_nzvars ses))++(lmap (sat_equalities ses))++(lmap (sat_equations ses)).

 Definition eqnS2ses (l : list equationS) : sat_equation_system :=
  match eqnS_list_transformB l with
  (l1,(l2,l3)) => Sat_equation_system l1 l2 l3 
  end.

 Lemma ses2eqnS_correct: forall ses ctx,
  ctx |= ses <-> (ctx |= (ses2eqnS ses))%part_scope.
 Proof with try tauto.
  intros.
  destruct ses as [l1 l2 l3]. simpl.
  unfold eval_sat_equation_system,ses2eqnS. simpl.
  repeat rewrite eval_app.
  generalize (@eval_map (list var) (list equationS) context lmap _ _ _ l1 ctx);intro.
  generalize (@eval_map (list equality) (list equationS) context lmap _ _ _ l2 ctx);intro.
  generalize (@eval_map (list equation) (list equationS) context lmap _ _ _ l3 ctx);intro.
  tauto.
 Qed.

 Lemma eqnS2ses_correct: forall l ctx',
  (ctx' |= l)%part_scope <-> ctx' |= eqnS2ses l.
 Proof with try tauto.
  intros. unfold eqnS2ses.
  case_eq (eqnS_list_transformB l);intros.
  destruct p.
  apply transformSB_eval with (ctx:=ctx') in H.
  simpl in *. unfold eval_sat_equation_system...
 Qed.

 Module input1 := Input_of_SV sv.
 Module ot1 := OrderedType_of_SV sv.
 Module pi1 := Partition_Input_of_SV_nz sv es esf.
 Module SatP := Partition_SAT input1 ot1 pi1.

 Definition ses_partition (ses : sat_equation_system) : list (sat_equation_system) :=
  map eqnS2ses (SatP.partition_SAT (ses2eqnS ses)).

 Lemma ses_partition_correct : forall ses,
  SAT ses <-> forall ses', In ses' (ses_partition ses) -> SAT ses'.
 Proof with try tauto.
  intros. unfold ses_partition.
  split;intros.
  destruct H as [ctx H].
  apply ses2eqnS_correct in H.
  assert (SatP.SAT (ses2eqnS ses)).
   exists ctx...
  apply in_map_iff in H0.
  destruct H0 as [? [? ?]];subst.
  apply SatP.partition_SAT_correct1 in H2...
  destruct H2 as [ctx' H2]. exists ctx'. apply eqnS2ses_correct...

  assert (SatP.SAT (ses2eqnS ses)).
   apply SatP.partition_SAT_correct2.
   intros.
   spec H (eqnS2ses l'). spec H.
   apply in_map... destruct H as [ctx H].
   exists ctx. apply eqnS2ses_correct in H...
  destruct H0 as [ctx H0].
  exists ctx. apply ses2eqnS_correct in H0...
 Qed.

 Definition equationI := ((@eqnS var equality equation)*(list var)*bool)%type.

 (*Extract elements that are both in l and l'*)
 Definition el_filter {A} `{EqDec A} (l l' : list A) : list A :=
  filter (fun a => if in_dec eq_dec a l' then true else false) l.

 Definition nzvar2eqnI (l : list var) (b : bool) (v : var) : equationI :=
  (NZV v,el_filter (vars v) l,b).
 Definition eql2eqnI (l : list var) (b : bool) (eql : equality) : equationI :=
  (EL eql,el_filter (vars eql) l,b).
 Definition eqn2eqnI (l : list var) (b : bool) (eqn : equation) : equationI :=
  (EQ eqn,el_filter (vars eqn) l,b).
 Definition lnzvar2eqnI (l : list var) (b : bool) (lnz : list var) : list equationI :=
  map (nzvar2eqnI l b) lnz.
 Definition leql2eqnI (l : list var) (b : bool) (leql : list equality) : list equationI :=
  map (eql2eqnI l b) leql.
 Definition leqn2eqnI (l : list var) (b : bool) (leqn : list equation) : list equationI :=
  map (eqn2eqnI l b) leqn.
 Definition ies2eqnI (ies : impl_equation_system) (b : bool) : list equationI :=
  let (lex,lnz,leql,leqn) := ies in 
   (lnzvar2eqnI lex b lnz)++(leql2eqnI lex b leql)++(leqn2eqnI lex b leqn).
 Definition is2eqnI (is : impl_system) : list equationI :=
  let (ies1,ies2) := is in
   (ies2eqnI ies1 false)++(ies2eqnI ies2 true).

 Definition tupleI : Type := (list var * bool * list var * list equality * list equation)%type.

 Definition eqnI2tupleI (ei : equationI) : tupleI :=
  match ei with (es,l,b) =>
   match es with
   |NZV v => (l,b,v::nil,nil,nil)
   |EL eql => (l,b,nil,eql::nil,nil)
   |EQ eqn => (l,b,nil,nil,eqn::nil)
   end
  end.

 Definition leqnI2tupleI (lei : list equationI) : list tupleI :=
  map eqnI2tupleI lei.
 
 Definition emp_tupleI (b : bool): tupleI := (nil,b,nil,nil,nil). 

 Fixpoint removeDup {A : Type} `{EqDec A} (l : list A) : list A :=
  match l with
  |nil => nil
  |a::l' => match in_dec eq_dec a l' with
            |left _ => removeDup l'
            |right _ => a::(removeDup l')
            end
  end.

 (*merge 2 tuples together, list by list, keep the bool value of ti'*)
 Definition merge_tupleI (ti ti' : tupleI) : tupleI :=
  match ti with (lex,b,lnz,leql,leqn) =>
   match ti' with (lex',b',lnz',leql',leqn') =>
    (lex++lex',b',lnz++lnz',leql++leql',leqn++leqn')
   end
  end.

  Definition merge_list_tupleI (l : list tupleI) : tupleI :=
   fold_right merge_tupleI (emp_tupleI false) l.
  
 Definition tuple_simpl (ti : tupleI) : tupleI :=
  match ti with (lex,b,lnz,leql,leqn) =>
   (removeDup lex,b,removeDup lnz,removeDup leql,removeDup leqn)
  end.

 Definition tupleI2ies (ti : tupleI) : impl_equation_system :=
  match tuple_simpl ti with (lex,b,lnz,leql,leqn) =>
   Impl_equation_system lex lnz leql leqn
  end.
 
 Definition eqnI2ies (l : list equationI) : impl_equation_system :=
  tupleI2ies (merge_list_tupleI (leqnI2tupleI l)).

 Definition eqnI2is (pl : (list equationI)*(list equationI)) : impl_system :=
  let (l1,l2) := pl in
  (eqnI2ies l1, eqnI2ies l2).
 
 Module input2 := Input_of_SV_nz_ex sv.
 Module ot2 := OrderedType_of_SV_nz_ex sv.
 Module pi2 := Partition_Input_of_SV_nz_ex sv es esf.
 Module ImplP := Partition_IMPL input2 ot2 pi2.

 Definition impl_partition (is : impl_system) :=
  let (ies1,ies2) := is in
   map eqnI2is (ImplP.partition_IMPL (ies2eqnI ies1 false) (ies2eqnI ies2 true)).

 (*Starting tedious proofs...*)

 (*Check wether ies is a subsystem of ies'*)
 Definition subsystem (ies ies' : impl_equation_system) : Prop :=
  let (lex,lnz,leql,leqn) := ies in 
  let (lex',lnz',leql',leqn') := ies' in
   (sublist lex lex') /\ (sublist lnz lnz') /\ 
   (sublist leql leql') /\ (sublist leqn leqn').

 Definition disjointsystem (ies ies' : impl_equation_system) : Prop :=
  disjoint (vars ies) (vars ies').

 (*Some problematic conditions for ies*)
 Definition sub_Cond (l : list impl_equation_system) (ies : impl_equation_system) : Prop :=
  forall ies', In ies' l -> subsystem ies' ies.
 
 Definition disjoint_Cond (l : list impl_equation_system) : Prop :=
  forall i j ies1 ies2,
  nth_op i l = Some ies1 ->
  nth_op j l = Some ies2 ->
  i <> j -> disjointsystem ies1 ies2.

 Definition exist_nz_Cond (l : list impl_equation_system) (ies : impl_equation_system) : Prop :=
  forall v,
  In v (impl_nzvars ies) ->
  exists ies', In ies' l /\ In v (impl_nzvars ies').

 Definition exist_eql_Cond (l : list impl_equation_system) (ies : impl_equation_system) : Prop :=
  forall eql,
  In eql (impl_equalities ies) ->
  exists ies', In ies' l /\ In eql (impl_equalities ies').

 Definition exist_eqn_Cond (l : list impl_equation_system) (ies : impl_equation_system) : Prop :=
  forall eqn,
  In eqn (impl_equations ies) ->
  exists ies', In ies' l /\ In eqn (impl_equations ies').

 Definition exist_Cond (l : list impl_equation_system) (ies : impl_equation_system) : Prop :=
  exist_nz_Cond l ies /\
  exist_eql_Cond l ies /\
  exist_eqn_Cond l ies.

 Definition ies_preserve_Cond (ies ies' : impl_equation_system) : Prop :=
  forall v,
  In v ((vars (impl_nzvars ies'))++(vars (impl_equalities ies'))++(vars (impl_equations ies'))) ->
  In v (impl_exvars ies) ->
  In v (impl_exvars ies').

 Definition preserve_Cond (l : list impl_equation_system) (ies : impl_equation_system) : Prop :=
  forall ies', In ies' l -> ies_preserve_Cond ies ies'.

 Lemma list_eval_rewrite: 
  forall {A B} `{share_dec_base.evalable A B} (a : A)(l : list B),
   a |= l <-> (forall b, In b l -> a |= b).
 Proof with try tauto.
  induction l;intros.
  simpl...
  split;intros. simpl in H0.
  destruct H1;subst...
  apply IHl... simpl in H0. split.
  apply IHl. intros. apply H0...
  apply H0...
 Qed.

 Lemma vars_membership:
  forall {A B} `{share_dec_base.varsable A B} (l : list A) a b,
  In a l -> In b (vars a) -> In b (vars l).
 Proof with try tauto.
  induction l;intros. inv H0.
  simpl. rewrite in_app_iff.
  destruct H0;subst...
  right. eapply IHl;eauto.
 Qed.

 Lemma var_eval_preserve: forall l l' (rho rho' : context) (v : var),
  (In v l -> In v l') ->
  sublist l' l ->
  ([l' => rho']rho) v = ([l => rho']rho) v.
 Proof with try tauto.
  intros.
  destruct (in_dec eq_dec v l).
  spec H i. repeat rewrite share_dec_base.override_in...
  repeat rewrite share_dec_base.override_not_in...
  intro. apply n. apply H0...
 Qed.

 Lemma obj_eval_preserve: forall l l' (rho rho' : context) (obj : object),
  (forall v, In v (vars obj) -> In v l -> In v l') ->
  sublist l' l ->
  get_obj_val ([l' => rho']rho) obj = get_obj_val ([l => rho']rho) obj.
 Proof with try tauto.
  intros.
  icase obj;simpl in *.
  apply var_eval_preserve...
  intro. apply H...
 Qed.

 Lemma eql_eval_preserve: forall l l' rho rho' (eql : equality),
  (forall v, In v (vars eql) -> In v l -> In v l') ->
  sublist l' l ->
  [l => rho']rho |= eql ->
  [l' => rho']rho |= eql.
 Proof with try tauto.
  intros.
  destruct eql as [obj1 obj2];simpl in *.
  generalize (obj_eval_preserve l l' rho rho' obj1);intro.
  spec H2. intros. apply H... rewrite in_app_iff... spec H2...
  generalize (obj_eval_preserve l l' rho rho' obj2);intro.
  spec H3. intros. apply H... rewrite in_app_iff... spec H3...
  congruence.
 Qed.

 Lemma eqn_eval_preserve: forall l l' rho rho' (eqn : equation),
  (forall v, In v (vars eqn) -> In v l -> In v l') ->
  sublist l' l ->
  [l => rho']rho |= eqn ->
  [l' => rho']rho |= eqn.
 Proof with try tauto.
  intros.
  destruct eqn as [[obj1 obj2] obj3];simpl in *.
  generalize (obj_eval_preserve l l' rho rho' obj1);intro.
  spec H2. intros. apply H... repeat rewrite in_app_iff... spec H2...
  generalize (obj_eval_preserve l l' rho rho' obj2);intro.
  spec H3. intros. apply H... repeat rewrite in_app_iff... spec H3...
  generalize (obj_eval_preserve l l' rho rho' obj3);intro.
  spec H4. intros. apply H... repeat rewrite in_app_iff... spec H4...
  congruence.
 Qed.

 Lemma nz_eval_preserve: forall l l' rho rho' (nz : var),
  (In nz l -> In nz l') ->
  sublist l' l ->
  [l => rho']rho |= nz ->
  [l' => rho']rho |= nz.
 Proof with try tauto.
  intros. simpl in *.
  erewrite var_eval_preserve;eauto.
 Qed.
  
 Lemma subsystem_eval: forall ies ies' rho,
  subsystem ies' ies -> ies_preserve_Cond ies ies' ->  
  rho |= ies -> rho |= ies'.
 Proof with try tauto.
  intros.
  destruct H1 as [rho' H1].
  exists rho'.
  destruct H1 as [H1 [H2 H3]].
  destruct ies as [lex lnz leql leqn].
  destruct ies' as [lex' lnz' leql' leqn'].
  simpl in *. destruct H as [? [? [? ?]]].
  split;simpl. 
  (*Equality*)
  apply list_eval_rewrite. intros. copy H7.
  apply H5 in H7.
  generalize (list_eval_rewrite ([lex => rho'] rho) leql);intro.
  rewrite H9 in H1. apply H1 in H7.
  apply eql_eval_preserve with (l:= lex)...
  intros. spec H0 v. simpl in H0.
  repeat rewrite in_app_iff in H0.
  apply H0... right. left. 
  generalize (vars_membership leql' b v H8 H10)...
  (*Equation*)
  split. apply list_eval_rewrite. intros. copy H7.
  apply H6 in H7.
  generalize (list_eval_rewrite ([lex => rho'] rho) leqn);intro.
  rewrite H9 in H2. apply H2 in H7.
  apply eqn_eval_preserve with (l:= lex)...
  intros. spec H0 v. simpl in H0.
  repeat rewrite in_app_iff in H0.
  apply H0... right. right. 
  generalize (vars_membership leqn' b v H8 H10)...
  (*Nonzero var*)
  apply list_eval_rewrite. intros. copy H7.
  apply H4 in H7.
  generalize (list_eval_rewrite ([lex => rho']rho) lnz);intro.
  rewrite H9 in H3. apply H3 in H7.
  apply nz_eval_preserve with (l:=lex)...
  intros. spec H0 b. simpl in H0.
  repeat rewrite in_app_iff in H0.
  apply H0... left. 
  rewrite<- vars_var_list in H8...
 Qed.

 Definition emp_ies : impl_equation_system :=
  Impl_equation_system nil nil nil nil.

 Lemma exist_nz_Cond_nil: forall ies,
  exist_nz_Cond nil ies -> impl_nzvars ies = nil.
 Proof with try tauto.
  intros. destruct ies as [l1 l2 l3 l4].
  unfold exist_nz_Cond in *;simpl in *.
  icase l2. spec H v. simpl in H. spec H...
  destruct H...
 Qed.

 Lemma exist_eql_Cond_nil: forall ies,
  exist_eql_Cond nil ies -> impl_equalities ies = nil.
 Proof with try tauto.
  intros. destruct ies as [l1 l2 l3 l4].
  unfold exist_eql_Cond in *;simpl in *.
  icase l3. spec H e. simpl in H. spec H...
  destruct H...
 Qed.

 Lemma exist_eqn_Cond_nil: forall ies,
  exist_eqn_Cond nil ies -> impl_equations ies = nil.
 Proof with try tauto.
  intros. destruct ies as [l1 l2 l3 l4].
  unfold exist_eqn_Cond in *;simpl in *.
  icase l4. spec H e. simpl in H. spec H...
  destruct H...
 Qed.

 Definition ies_combine (ies ies' : impl_equation_system) : impl_equation_system :=
  let (lex,lnz,leql,leqn) := ies in
   let (lex',lnz',leql',leqn') := ies' in
    Impl_equation_system (lex++lex') (lnz++lnz') (leql++leql') (leqn++leqn').

 Definition ies_aggregation (l : list impl_equation_system) : impl_equation_system :=
  fold_right ies_combine emp_ies l.

 Lemma list_eval_rewrite' : forall {A B} `{evalable A B} (a : A) (l : list B),
  eval_list a l <-> (forall b, In b l -> a |= b)%part_scope.
 Proof with try tauto.
  induction l;intros;
  simpl... rewrite IHl.
  split;intros. destruct H1;subst...
  destruct H0. apply H0...
  split. intros. apply H0...
  apply H0...
 Qed.

 Lemma override_app_iff: forall (ctx ctx' : context )l1 l2,
  [(l1++l2) => ctx'] ctx = [l2 => ctx'] ([l1 => ctx'] ctx).
 Proof with try tauto.
  intros.
  extensionality x.
  destruct (in_dec eq_dec x l2).
  rewrite override_in with (E:=l2)...
  rewrite override_in... rewrite in_app_iff...
  rewrite override_not_in with (E:=l2)...
  destruct (in_dec eq_dec x l1).
  rewrite override_in with (E:=l1)...
  rewrite override_in... rewrite in_app_iff...
  rewrite override_not_in with (E:=l1)...
  rewrite override_not_in... rewrite in_app_iff...
 Qed.

 Lemma override_app_swap: forall (ctx ctx' : context) l1 l2,
  [(l1++l2) => ctx'] ctx = [(l2++l1) => ctx'] ctx.
 Proof with try tauto.
  intros.
  extensionality x.
  destruct (in_dec eq_dec x (l1++l2)).
  repeat rewrite override_in...
  rewrite in_app_iff in *...
  repeat rewrite override_not_in...
  rewrite in_app_iff in *...
 Qed.

 Lemma override_disjoint1: forall (ctx1 ctx2 ctx : context) l1 l2,
  disjoint l1 l2 ->
  [l1 => ctx1] ([l2 => ctx2] ctx) = [l2 => ctx2] ([l1 => ctx1] ctx).
 Proof with try tauto.
  intros.
  extensionality x.
  destruct (in_dec eq_dec x l1).
  rewrite override_in with (E := l1)...
  destruct (in_dec eq_dec x l2).
  spec H x...
  rewrite override_not_in with (E:=l2)...
  rewrite override_in...
  rewrite override_not_in with (E:=l1)...
  destruct (in_dec eq_dec x l2).
  repeat rewrite override_in with (E:=l2)...
  repeat rewrite override_not_in...
 Qed.

 Lemma override_disjoint_reduce: forall (rho1 rho2 rho : context) l1 l2,
  disjoint l1 l2 ->
  [l1 => ([l2 => rho2] rho1)] rho = [l1 => rho1] rho.
 Proof with try tauto.
  intros.
  extensionality x.
  destruct (in_dec eq_dec x l1).
  repeat rewrite override_in with (E:=l1)...
  destruct (in_dec eq_dec x l2).
  spec H x...
  rewrite override_not_in...
  repeat rewrite override_not_in with (E:=l1)...
 Qed.

 Lemma override_sublist_reduce: forall (rho1 rho2 rho : context) l1 l2,
  sublist l2 l1 ->
  [l2 => rho2] ([l1 => rho1] rho) = [l1 => ([l2 => rho2] rho1)] rho.
 Proof with try tauto.
  intros.
  extensionality x.
  destruct (in_dec eq_dec x l1).
  rewrite override_in with (E:=l1)...
  destruct (in_dec eq_dec x l2).
  repeat rewrite override_in with (E:=l2)...
  repeat rewrite override_not_in with (E:=l2)...
  rewrite override_in...
  rewrite override_not_in with (E:=l1)...
  destruct (in_dec eq_dec x l2).
  spec H x...
  repeat rewrite override_not_in...
 Qed.

 Lemma override_reduce: forall (rho1 rho2 rho : context) l,
  [l => ([l => rho2] rho1)] rho = [l => rho2] rho.
 Proof with try tauto.
  intros.
  extensionality x.
  destruct (in_dec eq_dec x l).
  repeat rewrite override_in...
  repeat rewrite override_not_in...
 Qed.

 Lemma disjoint_app1: forall {A} (l l1 l2: list A),
  disjoint l (l1++l2) <-> disjoint l l1 /\ disjoint l l2.
 Proof with try tauto.
  intros.
  split;repeat intro.
  split;repeat intro. spec H x.
  rewrite in_app_iff in H...
  spec H x. rewrite in_app_iff in H...
  rewrite in_app_iff in H0.
  destruct H. spec H x. spec H1 x...
 Qed.

 Lemma disjoint_app2: forall {A} (l l1 l2: list A),
  disjoint (l1++l2) l <-> disjoint l1 l /\ disjoint l2 l.
 Proof with try tauto.
  intros.
  split;repeat intro.
  split;repeat intro;spec H x;
  rewrite in_app_iff in H...
  rewrite in_app_iff in H0.
  destruct H. spec H x. spec H1 x...
 Qed.

 Lemma transformS_vars1: forall (v : var),
  vars (transformS v) = v::nil.
 Proof with try tauto.
  repeat intro. simpl...
 Qed.
  
 Lemma transformS_vars2: forall (eql : equality),
  vars (transformS eql) = vars eql.
 Proof with try tauto.
  repeat intro. simpl...
 Qed.

 Lemma transformS_vars3: forall (eqn : equation),
  vars (transformS eqn) = vars eqn.
 Proof with try tauto.
  repeat intro. simpl...
 Qed.

 Lemma sublist_vars': forall (A B : Type) (H : varsable A B) (l : list A) (e : A),
  In e l -> sublist (vars e) (vars l).
 Proof with try tauto.
  induction l;intros. inv H0.
  destruct H0;subst. repeat intro.
  simpl. rewrite in_app_iff...
  apply IHl in H0. repeat intro.
  spec H0 e0 H1. simpl. rewrite in_app_iff...
 Qed.

 Lemma ies_combine_eval: forall ies ies' rho rho',
  rho |= ies ->
  rho' |= ies' ->
  disjointsystem ies ies' ->
  [(vars ies') => rho'] rho |= ies_combine ies ies'.
 Proof with try tauto.
  intros.
  destruct H as [rho1 H].
  destruct H0 as [rho2 H0].
  exists ([impl_exvars ies' => rho2] rho1).
  rewrite ses2eqnS_correct in *.
  unfold ses2eqnS in *.
  simpl in *. repeat rewrite eval_app.
  repeat rewrite eval_app in H.
  repeat rewrite eval_app in H0.

  split.
  (*Nonzero*)
  unfold ies_combine;simpl.
  destruct ies as [lex lnz leql leqn].
  destruct ies' as [lex' lnz' leql' leqn'].
  simpl. unfold disjointsystem in H1.
  rewrite list_eval_rewrite'. intros.
  unfold lmap in H2. 
  rewrite in_map_iff in H2. destruct H2 as [? [? ?]].
  rewrite in_app_iff in H3.
  destruct H0 as [H0 _]. destruct H as [H _].
  rewrite list_eval_rewrite' in H,H0.
  destruct H3. spec H b. spec H.
  unfold lmap. rewrite in_map_iff.
  exists x. split...

  rewrite override_app_iff.
  generalize pi1.eval_override_disjoint;intro. 
  unfold override in H4.
  unfold pi1.context_override in H4.
  apply H4. subst.
  apply disjoint_comm. 
  rewrite transformS_vars1...
  apply sublist_disjoint with (l2 := lnz).
  repeat intro. simpl in H2;destruct H2;subst...
  simpl in H1.
  repeat rewrite disjoint_app1 in H1.
  repeat rewrite disjoint_app2 in H1...
  clear H4.
  rewrite override_disjoint_reduce.
  rewrite override_disjoint1.
  generalize pi1.eval_override_disjoint;intro.
  unfold override in H4.
  unfold pi1.context_override in H4.
  apply H4...
  clear - H1 H2 H3. subst.
  rewrite transformS_vars1...
  apply disjoint_comm.
  apply sublist_disjoint with (l2:=lnz).
  repeat intro. simpl in H. destruct H;subst...
  simpl in H1. repeat rewrite disjoint_app2 in H1...
  simpl in H1. repeat rewrite disjoint_app2 in H1...
  simpl in H1. repeat rewrite disjoint_app1 in H1.
  repeat rewrite disjoint_app2 in H1...
  
  rewrite override_app_swap.
  rewrite override_app_iff.
  rewrite override_reduce.
  rewrite override_disjoint_reduce.
  generalize pi1.eval_override_disjoint;intro. 
  unfold override in H4.
  unfold pi1.context_override in H4.
  apply H4;clear H4.
  subst. rewrite transformS_vars1...
  apply disjoint_comm.
  apply sublist_disjoint with (l2 := lnz').
  repeat intro. simpl in H2;destruct H2;subst...
  apply disjoint_comm. simpl in H1.
  repeat rewrite disjoint_app1 in H1.
  repeat rewrite disjoint_app2 in H1...
  rewrite override_sublist_reduce.
  generalize pi1.eval_override_sublist;intro.
  unfold override in H4.
  unfold pi1.context_override in H4.
  apply H4;clear H4. apply H0...
  simpl. unfold lmap. rewrite in_map_iff. exists x...
  subst. repeat intro. repeat rewrite in_app_iff.
  simpl in H2;destruct H2;subst...
  repeat intro. repeat rewrite in_app_iff...
  simpl in H1. repeat rewrite disjoint_app1 in H1.
  repeat rewrite disjoint_app2 in H1...

  split.
  (*Equality*)
  unfold ies_combine;simpl.
  destruct ies as [lex lnz leql leqn].
  destruct ies' as [lex' lnz' leql' leqn'].
  simpl. unfold disjointsystem in H1.
  rewrite list_eval_rewrite'. intros.
  unfold lmap in H2. 
  rewrite in_map_iff in H2. destruct H2 as [? [? ?]].
  rewrite in_app_iff in H3.
  destruct H0 as [_ [H0 _]]. destruct H as [_ [H _]].
  rewrite list_eval_rewrite' in H,H0.
  destruct H3. spec H b. spec H.
  unfold lmap. rewrite in_map_iff.
  exists x. split...

  rewrite override_app_iff.
  generalize pi1.eval_override_disjoint;intro. 
  unfold override in H4.
  unfold pi1.context_override in H4.
  apply H4. subst.
  apply disjoint_comm. 
  rewrite transformS_vars2...
  apply sublist_disjoint with (l2 := (vars leql)).
  apply sublist_vars'...
  simpl in H1.
  repeat rewrite disjoint_app1 in H1.
  repeat rewrite disjoint_app2 in H1...
  clear H4.
  rewrite override_disjoint_reduce.
  rewrite override_disjoint1.
  generalize pi1.eval_override_disjoint;intro.
  unfold override in H4.
  unfold pi1.context_override in H4.
  apply H4...
  clear - H1 H2 H3. subst.
  rewrite transformS_vars2...
  apply disjoint_comm.
  apply sublist_disjoint with (l2:= (vars leql)).
  apply sublist_vars'...
  simpl in H1. repeat rewrite disjoint_app2 in H1...
  simpl in H1. repeat rewrite disjoint_app2 in H1...
  simpl in H1. repeat rewrite disjoint_app1 in H1.
  repeat rewrite disjoint_app2 in H1...
  
  rewrite override_app_swap.
  rewrite override_app_iff.
  rewrite override_reduce.
  rewrite override_disjoint_reduce.
  generalize pi1.eval_override_disjoint;intro. 
  unfold override in H4.
  unfold pi1.context_override in H4.
  apply H4;clear H4.
  subst. rewrite transformS_vars2...
  apply disjoint_comm.
  apply sublist_disjoint with (l2 := (vars leql')).
  apply sublist_vars'...
  apply disjoint_comm. simpl in H1.
  repeat rewrite disjoint_app1 in H1.
  repeat rewrite disjoint_app2 in H1...
  rewrite override_sublist_reduce.
  generalize pi1.eval_override_sublist;intro.
  unfold override in H4.
  unfold pi1.context_override in H4.
  apply H4;clear H4. apply H0...
  simpl. unfold lmap. rewrite in_map_iff. exists x...
  subst. repeat intro. repeat rewrite in_app_iff.
  rewrite transformS_vars2 in H2.
  eapply sublist_vars' in H3. spec H3 e H2...
  repeat intro. repeat rewrite in_app_iff...
  simpl in H1. repeat rewrite disjoint_app1 in H1.
  repeat rewrite disjoint_app2 in H1...

  (*Equation*)
  unfold ies_combine;simpl.
  destruct ies as [lex lnz leql leqn].
  destruct ies' as [lex' lnz' leql' leqn'].
  simpl. unfold disjointsystem in H1.
  rewrite list_eval_rewrite'. intros.
  unfold lmap in H2. 
  rewrite in_map_iff in H2. destruct H2 as [? [? ?]].
  rewrite in_app_iff in H3.
  destruct H0 as [_ [_ H0]]. destruct H as [_ [_ H]].
  rewrite list_eval_rewrite' in H,H0.
  destruct H3. spec H b. spec H.
  unfold lmap. rewrite in_map_iff.
  exists x. split...

  rewrite override_app_iff.
  generalize pi1.eval_override_disjoint;intro. 
  unfold override in H4.
  unfold pi1.context_override in H4.
  apply H4. subst.
  apply disjoint_comm. 
  rewrite transformS_vars3...
  apply sublist_disjoint with (l2 := (vars leqn)).
  apply sublist_vars'...
  simpl in H1.
  repeat rewrite disjoint_app1 in H1.
  repeat rewrite disjoint_app2 in H1...
  clear H4.
  rewrite override_disjoint_reduce.
  rewrite override_disjoint1.
  generalize pi1.eval_override_disjoint;intro.
  unfold override in H4.
  unfold pi1.context_override in H4.
  apply H4...
  clear - H1 H2 H3. subst.
  rewrite transformS_vars3...
  apply disjoint_comm.
  apply sublist_disjoint with (l2:= (vars leqn)).
  apply sublist_vars'...
  simpl in H1. repeat rewrite disjoint_app2 in H1...
  simpl in H1. repeat rewrite disjoint_app2 in H1...
  simpl in H1. repeat rewrite disjoint_app1 in H1.
  repeat rewrite disjoint_app2 in H1...
  
  rewrite override_app_swap.
  rewrite override_app_iff.
  rewrite override_reduce.
  rewrite override_disjoint_reduce.
  generalize pi1.eval_override_disjoint;intro. 
  unfold override in H4.
  unfold pi1.context_override in H4.
  apply H4;clear H4.
  subst. rewrite transformS_vars3...
  apply disjoint_comm.
  apply sublist_disjoint with (l2 := (vars leqn')).
  apply sublist_vars'...
  apply disjoint_comm. simpl in H1.
  repeat rewrite disjoint_app1 in H1.
  repeat rewrite disjoint_app2 in H1...
  rewrite override_sublist_reduce.
  generalize pi1.eval_override_sublist;intro.
  unfold override in H4.
  unfold pi1.context_override in H4.
  apply H4;clear H4. apply H0...
  simpl. unfold lmap. rewrite in_map_iff. exists x...
  subst. repeat intro. repeat rewrite in_app_iff.
  rewrite transformS_vars3 in H2.
  eapply sublist_vars' in H3. spec H3 e H2...
  repeat intro. repeat rewrite in_app_iff...
  simpl in H1. repeat rewrite disjoint_app1 in H1.
  repeat rewrite disjoint_app2 in H1...
 Qed.

 Lemma vars_app_rewrite': forall {A B} `{share_dec_base.varsable A B} (l1 l2 : list A),
  share_dec_base.vars_list (l1++l2) = (share_dec_base.vars_list l1) ++ (share_dec_base.vars_list l2).
 Proof with try tauto.
  induction l1;intros...
  simpl. rewrite IHl1.
  apply app_assoc.
 Qed.

 Lemma ies_combine_vars: forall v ies ies',
  (In v (vars ies) \/ In v (vars ies')) <-> In v (vars (ies_combine ies ies')).
 Proof with try tauto.
  intros. unfold ies_combine.
  destruct ies as [? ? ? ?].
  destruct ies' as [? ? ? ?].
  simpl.
  repeat rewrite vars_app_rewrite'.
  repeat rewrite in_app_iff...
 Qed.

 Lemma ies_combine_nz: forall nz ies ies',
  (In nz (impl_nzvars ies) \/ In nz (impl_nzvars ies')) <->
  (In nz (impl_nzvars (ies_combine ies ies'))).
 Proof with try tauto.
  intros. unfold ies_combine.
  destruct ies as [? ? ? ?].
  destruct ies' as [? ? ? ?].
  simpl.
  rewrite in_app_iff...
 Qed.

 Lemma ies_combine_ex: forall ex ies ies',
  (In ex (impl_exvars ies) \/ In ex (impl_exvars ies')) <->
  (In ex (impl_exvars (ies_combine ies ies'))).
 Proof with try tauto.
  intros. unfold ies_combine.
  destruct ies as [? ? ? ?].
  destruct ies' as [? ? ? ?].
  simpl.
  rewrite in_app_iff...
 Qed.

 Lemma ies_combine_eql: forall eql ies ies',
  (In eql (impl_equalities ies) \/ In eql (impl_equalities ies')) <->
  (In eql (impl_equalities (ies_combine ies ies'))).
 Proof with try tauto.
  intros. unfold ies_combine.
  destruct ies as [? ? ? ?].
  destruct ies' as [? ? ? ?].
  simpl.
  rewrite in_app_iff...
 Qed.

 Lemma ies_combine_eqn: forall eqn ies ies',
  (In eqn (impl_equations ies) \/ In eqn (impl_equations ies')) <->
  (In eqn (impl_equations (ies_combine ies ies'))).
 Proof with try tauto.
  intros. unfold ies_combine.
  destruct ies as [? ? ? ?].
  destruct ies' as [? ? ? ?].
  simpl.
  rewrite in_app_iff...
 Qed.
 
 Lemma ies_aggregation_vars: forall l v,
  In v (vars (ies_aggregation l)) <-> exists ies, In ies l /\ In v (vars ies).
 Proof with try tauto.
  induction l;intros.
  split;intros... destruct H... 
  replace (ies_aggregation (a :: l)) with (ies_combine a (ies_aggregation l))...
  rewrite<- ies_combine_vars.
  rewrite IHl. split;intros.
  destruct H. exists a. simpl...
  destruct H. exists x. simpl...
  destruct H. destruct H.
  destruct H;subst... right. exists x...
 Qed.
  
 Lemma ies_aggregation_nz: forall l nz,
  In nz (impl_nzvars (ies_aggregation l)) <-> exists ies, In ies l /\ In nz (impl_nzvars ies).
 Proof with try tauto.
  induction l;intros;simpl.
  split;intros... destruct H...
  rewrite<- ies_combine_nz.
  rewrite IHl. split;intros.
  destruct H. exists a...
  destruct H. exists x...
  destruct H. destruct H.
  destruct H;subst... right. exists x...
 Qed.

 Lemma ies_aggregation_ex: forall l ex,
  In ex (impl_exvars (ies_aggregation l)) <-> exists ies, In ies l /\ In ex (impl_exvars ies).
 Proof with try tauto.
  induction l;intros;simpl.
  split;intros... destruct H...
  rewrite<- ies_combine_ex.
  rewrite IHl. split;intros.
  destruct H. exists a...
  destruct H. exists x...
  destruct H. destruct H.
  destruct H;subst... right. exists x...
 Qed.

 Lemma ies_aggregation_eql: forall l eql,
  In eql (impl_equalities (ies_aggregation l)) <-> exists ies, In ies l /\ In eql (impl_equalities ies).
 Proof with try tauto.
  induction l;intros;simpl.
  split;intros... destruct H...
  rewrite<- ies_combine_eql.
  rewrite IHl. split;intros.
  destruct H. exists a...
  destruct H. exists x...
  destruct H. destruct H.
  destruct H;subst... right. exists x...
 Qed.

 Lemma ies_aggregation_eqn: forall l eqn,
  In eqn (impl_equations (ies_aggregation l)) <-> exists ies, In ies l /\ In eqn (impl_equations ies).
 Proof with try tauto.
  induction l;intros;simpl.
  split;intros... destruct H...
  rewrite<- ies_combine_eqn.
  rewrite IHl. split;intros.
  destruct H. exists a...
  destruct H. exists x...
  destruct H. destruct H.
  destruct H;subst... right. exists x...
 Qed.

 Lemma ies_aggregation_eval: forall l (rho : context),
  (forall ies, In ies l -> rho |= ies) ->
  disjoint_Cond l ->
  rho |= ies_aggregation l.
 Proof with try tauto.
  induction l;intros.
  simpl. exists rho. compute...
  simpl. generalize (H a);intro.
  spec H1;simpl...
  spec IHl rho. spec IHl. intros. apply H. simpl...
  spec IHl. repeat intro.
  spec H0 (S i) (S j) ies1 ies2.
  simpl in H0. spec H0... spec H0...
  spec H0. intro. inv H6...
  spec H0 x...
  generalize (ies_combine_eval a (ies_aggregation l) rho rho H1 IHl);intro.
  spec H2. repeat intro.
  rewrite ies_aggregation_vars in H3.
  destruct H3. destruct H4 as [? [? ?]].
  rewrite nth_op_In in H4. destruct H4.
  spec H0 0 (S x1) a x0. simpl in H0.
  spec H0... spec H0... spec H0. omega. spec H0 x...
  rewrite context_override_idem in H2...
 Qed.

 Lemma override_intersect_obj:forall (obj : object) l1 l2 (rho' rho : context),
  (forall v, In v (vars obj) -> (In v l1 <-> In v l2)) ->
  get_obj_val ([l1 => rho']rho) obj = get_obj_val ([l2 => rho']rho) obj.
 Proof with try tauto.
  intros.
  icase obj. simpl. spec H v. simpl in H. spec H...
  destruct (in_dec eq_dec v l1).
  repeat rewrite override_in...
  repeat rewrite override_not_in...
 Qed.

 Lemma override_intersect_eql: forall (eql : equality) l1 l2 rho' rho,
  (forall v, In v (vars eql) -> (In v l1 <-> In v l2)) ->
  ([l1 => rho']rho |= eql <->
   [l2 => rho']rho |= eql).
 Proof with try tauto.
  intros.
  destruct eql as [obj1 obj2].
  simpl in *.
  repeat rewrite override_intersect_obj with (l1:=l1) (l2:=l2)...
  intros. spec H v;rewrite in_app_iff in H...
  intros. spec H v;rewrite in_app_iff in H...
 Qed.

 Lemma override_intersect_eqn: forall (eqn : equation) l1 l2 rho' rho,
  (forall v, In v (vars eqn) -> (In v l1 <-> In v l2)) ->
  ([l1 => rho']rho |= eqn <->
   [l2 => rho']rho |= eqn).
 Proof with try tauto.
  intros.
  destruct eqn as [[obj1 obj2] obj3].
  simpl in *.
  repeat rewrite override_intersect_obj with (l1:=l1) (l2:=l2)...
  intros. spec H v;repeat rewrite in_app_iff in H...
  intros. spec H v;repeat rewrite in_app_iff in H...
  intros. spec H v;repeat rewrite in_app_iff in H...
 Qed.

 Lemma override_intersect_nz: forall (nz : var) l1 l2 rho' rho,
  (forall v, In v (vars nz) -> (In v l1 <-> In v l2)) ->
  ([l1 => rho']rho |= nz <->
   [l2 => rho']rho |= nz).
 Proof with try tauto.
  intros. simpl. spec H nz. simpl in H;spec H...
  destruct (in_dec eq_dec nz l1).
  repeat rewrite override_in...
  repeat rewrite override_not_in...
 Qed.
  
 Lemma subsystem_aggregate_eval: forall l rho (ies : impl_equation_system),
  sub_Cond l ies ->
  disjoint_Cond l ->
  exist_Cond l ies ->
  preserve_Cond l ies ->
  (forall ies', In ies' l -> rho |= ies') ->
  rho |= ies.
 Proof with try tauto.
  intros.
  destruct (ies_aggregation_eval _ _ H3 H0) as [rho' H4].
  exists rho'. destruct H4 as [? [? ?]].

  split.
  (*Equalities*)
  rewrite list_eval_rewrite.
  repeat intro. rewrite list_eval_rewrite in H4.
  spec H4 b. spec H4. 
  destruct H1 as [_ [H1 _]].
  spec H1 b. spec H1... destruct H1 as [ies' [? ?]].
  simpl. rewrite ies_aggregation_eql. exists ies'...
  rewrite override_intersect_eql with (l2:= impl_exvars (ies_aggregation l))...
  repeat intro. split;intros.
  destruct H1 as [_ [H1 _]]. spec H1 b. spec H1...
  destruct H1 as [ies' [? ?]].
  spec H2 ies' H1. spec H2 v. spec H2. 
  apply sublist_vars in H10. spec H10 v H8. repeat rewrite in_app_iff...
  spec H2... rewrite ies_aggregation_ex. exists ies'...
  apply ies_aggregation_ex in H9.
  destruct H9 as [ies' [? ?]].
  spec H ies' H9. 
  destruct ies as [? ? ? ?]. destruct ies' as [? ? ? ?].
  simpl in *. destruct H as [H _]. spec H v...

  split.
  (*Equations*)
  rewrite list_eval_rewrite.
  repeat intro. rewrite list_eval_rewrite in H5.
  spec H5 b. spec H5. 
  destruct H1 as [_ [_ H1]].
  spec H1 b. spec H1... destruct H1 as [ies' [? ?]].
  simpl. rewrite ies_aggregation_eqn. exists ies'...
  rewrite override_intersect_eqn with (l2:= impl_exvars (ies_aggregation l))...
  repeat intro. split;intros.
  destruct H1 as [_ [_ H1]]. spec H1 b. spec H1...
  destruct H1 as [ies' [? ?]].
  spec H2 ies' H1. spec H2 v. spec H2. 
  apply sublist_vars in H10. spec H10 v H8. repeat rewrite in_app_iff...
  spec H2... rewrite ies_aggregation_ex. exists ies'...
  apply ies_aggregation_ex in H9.
  destruct H9 as [ies' [? ?]].
  spec H ies' H9. 
  destruct ies as [? ? ? ?]. destruct ies' as [? ? ? ?].
  simpl in *. destruct H as [H _]. spec H v...

  (*nz*)
  rewrite list_eval_rewrite.
  intros. rewrite list_eval_rewrite in H6.
  spec H6 b. spec H6. 
  destruct H1 as [H1 _].
  spec H1 b. spec H1... destruct H1 as [ies' [? ?]].
  simpl. rewrite ies_aggregation_nz. exists ies'...
  rewrite override_intersect_nz with (l2:= impl_exvars (ies_aggregation l))...
  repeat intro. split;intros.
  destruct H1 as [H1 _]. spec H1 b. spec H1...
  destruct H1 as [ies' [? ?]].
  spec H2 ies' H1. spec H2 v. spec H2. 
  apply sublist_vars in H10. spec H10 v H8. repeat rewrite in_app_iff...
  spec H2... rewrite ies_aggregation_ex. exists ies'...
  apply ies_aggregation_ex in H9.
  destruct H9 as [ies' [? ?]].
  spec H ies' H9. 
  destruct ies as [? ? ? ?]. destruct ies' as [? ? ? ?].
  simpl in *. destruct H as [H _]. spec H v...
 Qed.
  
 Lemma ies_equiv_Cond : forall l ies rho,
  sub_Cond l ies ->
  disjoint_Cond l ->
  exist_Cond l ies ->
  preserve_Cond l ies ->
  (rho |= ies <-> (forall ies', In ies' l -> rho |= ies')).
 Proof with try tauto.
  intros.
  split;intros.
  (*=>*)
  apply subsystem_eval with ies...
  spec H ies'... spec H2 ies'...
  (*<=*)
  eapply subsystem_aggregate_eval;eauto.
 Qed.

 Lemma ies2eqnI_sublist_nzvars_In: forall ies b v l l' b',
  sublist l (ies2eqnI ies b) ->
  In (NZV v,l',b') l ->
  In v (impl_nzvars ies).
 Proof with try tauto.
  intros. generalize (H _ H0);clear H;intro. 
  unfold ies2eqnI in H.
  destruct ies as [lex lnz leql leqn]. simpl in *.
  repeat rewrite in_app_iff in H. icase H.
  unfold lnzvar2eqnI in H.
  rewrite in_map_iff in H.
  destruct H as [? [? ?]]. inv H...
  icase H. unfold leql2eqnI in H.
  rewrite in_map_iff in H.
  destruct H as [? [? ?]]. inv H.
  unfold leqn2eqnI in H.
  rewrite in_map_iff in H.
  destruct H as [? [? ?]]. inv H.
 Qed.
  
 Lemma ies2eqnI_sublist_equalities_In: forall ies b eql l l' b',
  sublist l (ies2eqnI ies b) ->
  In (EL eql,l',b') l ->
  In eql (impl_equalities ies).
 Proof with try tauto.
  intros.  generalize (H _ H0);clear H;intro.
  unfold ies2eqnI in H.
  destruct ies as [lex lnz leql leqn]. simpl in *.
  repeat rewrite in_app_iff in H. icase H.
  unfold lnzvar2eqnI in H.
  rewrite in_map_iff in H.
  destruct H as [? [? ?]]. inv H.
  icase H. unfold leql2eqnI in H.
  rewrite in_map_iff in H.
  destruct H as [? [? ?]]. inv H...
  unfold leqn2eqnI in H.
  rewrite in_map_iff in H.
  destruct H as [? [? ?]]. inv H.
 Qed.

 Lemma ies2eqnI_sublist_equations_In: forall ies b eqn l l' b',
  sublist l (ies2eqnI ies b) ->
  In (EQ eqn,l',b') l ->
  In eqn (impl_equations ies).
 Proof with try tauto.
  intros. generalize (H _ H0);clear H;intro.
  unfold ies2eqnI in H.
  destruct ies as [lex lnz leql leqn]. simpl in *.
  repeat rewrite in_app_iff in H. icase H.
  unfold lnzvar2eqnI in H.
  rewrite in_map_iff in H.
  destruct H as [? [? ?]]. inv H.
  icase H. unfold leql2eqnI in H.
  rewrite in_map_iff in H.
  destruct H as [? [? ?]]. inv H.
  unfold leqn2eqnI in H.
  rewrite in_map_iff in H.
  destruct H as [? [? ?]]. inv H...
 Qed.

 Lemma el_filter_In_iff: forall {A} `{EqDec A} (l l' : list A) a,
  In a (el_filter l l') <-> In a l /\ In a l'.
 Proof with try tauto.
  intros. unfold el_filter.
  rewrite filter_In.
  destruct (in_dec eq_dec a l')...
  split;intros... destruct H0. inv H1.
 Qed.

 Lemma ies2eqnI_sublist_exvars_In: forall ies b eqns l l' b',
  sublist l (ies2eqnI ies b) ->
  In (eqns,l',b') l ->
  sublist l' (impl_exvars ies).
 Proof with try tauto.
  repeat intro. generalize (H _ H0);clear H;intro.
  unfold ies2eqnI in H.
  destruct ies as [lex lnz leql leqn]. simpl in *.
  repeat rewrite in_app_iff in H. icase H.
  unfold lnzvar2eqnI in H.
  rewrite in_map_iff in H.
  destruct H as [? [? ?]].
  inv H. destruct (in_dec eq_dec x lex)...
  simpl in H1;destruct H1;subst... icase H.

  unfold leql2eqnI in H.
  rewrite in_map_iff in H.
  destruct H as [? [? ?]]. inv H.
  rewrite el_filter_In_iff in H1...

  unfold leqn2eqnI in H.
  rewrite in_map_iff in H.
  destruct H as [? [? ?]]. inv H.
  rewrite el_filter_In_iff in H1...
 Qed.

 Lemma removeDup_In: forall {A} `{EqDec A} (l : list A) v,
  In v (removeDup l) <-> In v l.
 Proof with try tauto.
  induction l;intros; simpl...
  destruct (in_dec eq_dec a l);split;intros.
  apply IHl in H0... destruct H0;subst.
  apply IHl... apply IHl...
  destruct H0;subst... apply IHl in H0...
  destruct H0;subst... left...
  right. apply IHl...
 Qed.

 Lemma tupleI2ies_nzvars_In: forall t v,
  In v (impl_nzvars (tupleI2ies t)) <->
  In v (snd (fst (fst t))).
 Proof with try tauto.
  intros.
  unfold tupleI2ies,tuple_simpl;simpl.
  destruct t as [[[[? ?] ?] ?] ?]. simpl.
  apply removeDup_In... 
 Qed.

 Lemma merge_tupleI_nzvars_In: forall t1 t2 v,
  In v (snd (fst (fst (merge_tupleI t1 t2)))) <->
  In v (snd (fst (fst t1))) \/ In v (snd (fst (fst t2))).
 Proof with try tauto.
  intros. unfold merge_tupleI.
  destruct t1 as [[[[? ?] ?] ?] ?].
  destruct t2 as [[[[? ?] ?] ?] ?].
  simpl. rewrite in_app_iff...
 Qed.

 Lemma merge_list_tupleI_nzvars_In: forall lt v ,
  In v (snd (fst (fst (merge_list_tupleI lt)))) <->
  exists t, In t lt /\ In v (snd (fst (fst t))).
 Proof with try tauto.
  induction lt;intros. simpl.
  split;intros... destruct H...
  simpl...
  rewrite merge_tupleI_nzvars_In.
  split;intros. destruct H. exists a...
  apply IHlt in H. destruct H. exists x...
  destruct H as [? [? ?]]. destruct H;subst...
  right. apply IHlt...
  exists x...
 Qed.

 Lemma tupleI2ies_nzvars_In_combine: forall l v,
  In v (impl_nzvars (tupleI2ies (merge_list_tupleI (leqnI2tupleI l)))) <->
  exists b l', In (NZV v,l',b) l.
 Proof with try tauto.
  induction l;intros.
  simpl. split;intros... destruct H as [? [? ?]]...
  simpl. rewrite tupleI2ies_nzvars_In.
  rewrite merge_tupleI_nzvars_In.
  split;intros. icase H.
  destruct a as [[? ?] ?].
  icase e... simpl in H. destruct H;subst...
  exists b,l0...
  spec IHl v. rewrite tupleI2ies_nzvars_In in IHl.
  rewrite IHl in H. destruct H as [? [? ?]].
  exists x,x0...
  destruct H as [? [? ?]]. icase H;subst;simpl...
  right. apply merge_list_tupleI_nzvars_In.
  spec IHl v. 
  destruct IHl as [_ ?]. detach H0.
  rewrite tupleI2ies_nzvars_In in H0.
  apply  merge_list_tupleI_nzvars_In in H0...
  exists x,x0...
 Qed.

 Lemma tupleI2ies_equalities_In: forall t eql,
  In eql (impl_equalities (tupleI2ies t)) <->
  In eql (snd (fst t)).
 Proof with try tauto.
  intros.
  unfold tupleI2ies,tuple_simpl;simpl.
  destruct t as [[[[? ?] ?] ?] ?]. simpl.
  apply removeDup_In... 
 Qed.

 Lemma merge_tupleI_equalities_In: forall t1 t2 eql,
  In eql (snd (fst (merge_tupleI t1 t2))) <->
  In eql (snd (fst t1)) \/ In eql (snd (fst t2)).
 Proof with try tauto.
  intros. unfold merge_tupleI.
  destruct t1 as [[[[? ?] ?] ?] ?].
  destruct t2 as [[[[? ?] ?] ?] ?].
  simpl. rewrite in_app_iff...
 Qed.

 Lemma merge_list_tupleI_equalities_In: forall lt eql,
  In eql (snd (fst (merge_list_tupleI lt))) <->
  exists t, In t lt /\ In eql (snd (fst t)).
 Proof with try tauto.
  induction lt;intros. simpl.
  split;intros... destruct H...
  simpl...
  rewrite merge_tupleI_equalities_In.
  split;intros. destruct H. exists a...
  apply IHlt in H. destruct H. exists x...
  destruct H as [? [? ?]]. destruct H;subst...
  right. apply IHlt...
  exists x...
 Qed.

 Lemma tupleI2ies_equalities_In_combine: forall l eql,
  In eql (impl_equalities (tupleI2ies (merge_list_tupleI (leqnI2tupleI l)))) <->
  exists b l', In (EL eql,l',b) l.
 Proof with try tauto.
  induction l;intros.
  simpl. split;intros... destruct H as [? [? ?]]...
  simpl. rewrite tupleI2ies_equalities_In.
  rewrite merge_tupleI_equalities_In.
  split;intros. icase H.
  destruct a as [[? ?] ?].
  icase e... simpl in H. destruct H;subst...
  exists b,l0...
  spec IHl eql. rewrite tupleI2ies_equalities_In in IHl.
  rewrite IHl in H. destruct H as [? [? ?]].
  exists x,x0...
  destruct H as [? [? ?]]. icase H;subst;simpl...
  right. apply merge_list_tupleI_equalities_In.
  spec IHl eql. 
  destruct IHl as [_ ?]. detach H0.
  rewrite tupleI2ies_equalities_In in H0.
  apply  merge_list_tupleI_equalities_In in H0...
  exists x,x0...
 Qed.

 Lemma tupleI2ies_equations_In: forall t eqn,
  In eqn (impl_equations (tupleI2ies t)) <->
  In eqn (snd t).
 Proof with try tauto.
  intros.
  unfold tupleI2ies,tuple_simpl;simpl.
  destruct t as [[[[? ?] ?] ?] ?]. simpl.
  apply removeDup_In... 
 Qed.

 Lemma merge_tupleI_equations_In: forall t1 t2 eqn,
  In eqn (snd (merge_tupleI t1 t2)) <->
  In eqn (snd t1) \/ In eqn (snd t2).
 Proof with try tauto.
  intros. unfold merge_tupleI.
  destruct t1 as [[[[? ?] ?] ?] ?].
  destruct t2 as [[[[? ?] ?] ?] ?].
  simpl. rewrite in_app_iff...
 Qed.

 Lemma merge_list_tupleI_equations_In: forall lt eqn,
  In eqn (snd (merge_list_tupleI lt)) <->
  exists t, In t lt /\ In eqn (snd t).
 Proof with try tauto.
  induction lt;intros. simpl.
  split;intros... destruct H...
  simpl...
  rewrite merge_tupleI_equations_In.
  split;intros. destruct H. exists a...
  apply IHlt in H. destruct H. exists x...
  destruct H as [? [? ?]]. destruct H;subst...
  right. apply IHlt...
  exists x...
 Qed.

 Lemma tupleI2ies_equations_In_combine: forall l eqn,
  In eqn (impl_equations (tupleI2ies (merge_list_tupleI (leqnI2tupleI l)))) <->
  exists b l', In (EQ eqn,l',b) l.
 Proof with try tauto.
  induction l;intros.
  simpl. split;intros... destruct H as [? [? ?]]...
  simpl. rewrite tupleI2ies_equations_In.
  rewrite merge_tupleI_equations_In.
  split;intros. icase H.
  destruct a as [[? ?] ?].
  icase e... simpl in H. destruct H;subst...
  exists b,l0...
  spec IHl eqn. rewrite tupleI2ies_equations_In in IHl.
  rewrite IHl in H. destruct H as [? [? ?]].
  exists x,x0...
  destruct H as [? [? ?]]. icase H;subst;simpl...
  right. apply merge_list_tupleI_equations_In.
  spec IHl eqn. 
  destruct IHl as [_ ?]. detach H0.
  rewrite tupleI2ies_equations_In in H0.
  apply  merge_list_tupleI_equations_In in H0...
  exists x,x0...
 Qed.

 Lemma tupleI2ies_exvars_In: forall t v,
  In v (impl_exvars (tupleI2ies t)) <->
  In v (fst (fst (fst (fst t)))).
 Proof with try tauto.
  intros.
  unfold tupleI2ies,tuple_simpl;simpl.
  destruct t as [[[[? ?] ?] ?] ?]. simpl.
  apply removeDup_In... 
 Qed.

 Lemma merge_tupleI_exvars_In: forall t1 t2 v,
  In v (fst (fst (fst (fst (merge_tupleI t1 t2))))) <-> 
  In v (fst (fst (fst (fst t1)))) \/ In v (fst (fst (fst (fst t2)))).
 Proof with try tauto.
  intros. unfold merge_tupleI.
  destruct t1 as [[[[? ?] ?] ?] ?].
  destruct t2 as [[[[? ?] ?] ?] ?].
  simpl. rewrite in_app_iff...
 Qed.

 Lemma merge_list_tupleI_exvars_In: forall lt v,
  In v (fst (fst (fst (fst (merge_list_tupleI lt))))) <->
  exists t, In t lt /\ In v (fst (fst (fst (fst t)))).
 Proof with try tauto.
  induction lt;intros. simpl.
  split;intros... destruct H...
  simpl...
  rewrite merge_tupleI_exvars_In.
  split;intros. destruct H. exists a...
  apply IHlt in H. destruct H. exists x...
  destruct H as [? [? ?]]. destruct H;subst...
  right. apply IHlt...
  exists x...
 Qed.

 Lemma tupleI2ies_exvars_In_combine: forall l v,
  In v (impl_exvars (tupleI2ies (merge_list_tupleI (leqnI2tupleI l)))) <->
  exists eqns b l', In (eqns,l',b) l /\ In v l'.
 Proof with try tauto.
  induction l;intros.
  simpl. split;intros... destruct H as [? [? [? ?]]]...
  simpl. rewrite tupleI2ies_exvars_In.
  rewrite merge_tupleI_exvars_In.
  split;intros. icase H.
  destruct a as [[? ?] ?].
  icase e;simpl in H.
  exists (NZV v0),b,l0...
  exists (EL e),b,l0...
  exists (EQ e),b,l0...
  spec IHl v. rewrite tupleI2ies_exvars_In in IHl.
  rewrite IHl in H. destruct H as [? [? [? ?]]].
  exists x,x0,x1...
  destruct H as [? [? [? [? ?]]]]. icase H;subst;simpl.
  left. icase x.
  right. apply merge_list_tupleI_exvars_In.
  spec IHl v. 
  destruct IHl as [_ ?]. detach H0.
  apply tupleI2ies_exvars_In in H1.
  apply merge_list_tupleI_exvars_In in H1...
  exists x,x0,x1...
 Qed.

 Lemma impl_partition_sub_Cond1: forall is,
  sub_Cond (map (@fst _ _) (impl_partition is)) (fst is).
 Proof with try tauto.
  intros. unfold sub_Cond. repeat intro.
  apply in_map_iff in H. destruct H as [? [? ?]].
  destruct x as [ies1 ies2];simpl in *.
  unfold impl_partition in H0.
  destruct is as [ies3 ies4].
  apply in_map_iff in H0.
  destruct H0 as [? [? ?]].
  destruct x as [l1 l2]. inv H0.
  apply ImplP.partition_IMPL_sublist1 in H1.
  unfold subsystem.
  unfold eqnI2ies in H3. subst.
  remember (tupleI2ies (merge_list_tupleI (leqnI2tupleI l1))).
  destruct i as [lex' lnz' leql' leqn']. simpl.
  destruct ies3 as [lex lnz leql leqn].
  split. 

  repeat intro.
  generalize (tupleI2ies_exvars_In_combine l1 e);intro.
  rewrite<- Heqi in H0. simpl in H0.
  rewrite H0 in H. destruct H as [? [? [? [? ?]]]].
  generalize (ies2eqnI_sublist_exvars_In _ _ _ _ _ _ H1 H e);intro...

  split. repeat intro.
  generalize (tupleI2ies_nzvars_In_combine l1 e);intro.
  rewrite<- Heqi in H0. simpl in H0.
  rewrite H0 in H. destruct H as [? [? ?]].
  assert (In e lnz').
   apply H0. exists x,x0...
  generalize (ies2eqnI_sublist_nzvars_In _ _ _ _ _ _ H1 H);intro...

  split. repeat intro.
  generalize (tupleI2ies_equalities_In_combine l1 e);intro.
  rewrite<- Heqi in H0. simpl in H0.
  rewrite H0 in H. destruct H as [? [? ?]].
  assert (In e leql').
   apply H0. exists x,x0...
  generalize (ies2eqnI_sublist_equalities_In _ _ _ _ _ _ H1 H);intro...

  repeat intro.
  generalize (tupleI2ies_equations_In_combine l1 e);intro.
  rewrite<- Heqi in H0. simpl in H0.
  rewrite H0 in H. destruct H as [? [? ?]].
  assert (In e leqn').
   apply H0. exists x,x0...
  generalize (ies2eqnI_sublist_equations_In _ _ _ _ _ _ H1 H);intro...
 Qed.

 Lemma impl_partition_sub_Cond2: forall is,
  sub_Cond (map (@snd _ _) (impl_partition is)) (snd is).
 Proof with try tauto.
  intros. unfold sub_Cond. repeat intro.
  apply in_map_iff in H. destruct H as [? [? ?]].
  destruct x as [ies1 ies2];simpl in *.
  unfold impl_partition in H0.
  destruct is as [ies3 ies4].
  apply in_map_iff in H0.
  destruct H0 as [? [? ?]].
  destruct x as [l1 l2]. inv H0.
  apply ImplP.partition_IMPL_sublist2 in H1.
  unfold subsystem.
  unfold eqnI2ies in H4. subst.
  remember (tupleI2ies (merge_list_tupleI (leqnI2tupleI l2))).
  destruct i as [lex' lnz' leql' leqn']. simpl.
  destruct ies4 as [lex lnz leql leqn].
  split. 

  repeat intro.
  generalize (tupleI2ies_exvars_In_combine l2 e);intro.
  rewrite<- Heqi in H0. simpl in H0.
  rewrite H0 in H. destruct H as [? [? [? [? ?]]]].
  generalize (ies2eqnI_sublist_exvars_In _ _ _ _ _ _ H1 H e);intro...

  split. repeat intro.
  generalize (tupleI2ies_nzvars_In_combine l2 e);intro.
  rewrite<- Heqi in H0. simpl in H0.
  rewrite H0 in H. destruct H as [? [? ?]].
  assert (In e lnz').
   apply H0. exists x,x0...
  generalize (ies2eqnI_sublist_nzvars_In _ _ _ _ _ _ H1 H);intro...

  split. repeat intro.
  generalize (tupleI2ies_equalities_In_combine l2 e);intro.
  rewrite<- Heqi in H0. simpl in H0.
  rewrite H0 in H. destruct H as [? [? ?]].
  assert (In e leql').
   apply H0. exists x,x0...
  generalize (ies2eqnI_sublist_equalities_In _ _ _ _ _ _ H1 H);intro...

  repeat intro.
  generalize (tupleI2ies_equations_In_combine l2 e);intro.
  rewrite<- Heqi in H0. simpl in H0.
  rewrite H0 in H. destruct H as [? [? ?]].
  assert (In e leqn').
   apply H0. exists x,x0...
  generalize (ies2eqnI_sublist_equations_In _ _ _ _ _ _ H1 H);intro...
 Qed.

 Lemma nth_op_map_Some_iff: forall {A B} (f : A -> B) n (l : list A) b,
  nth_op n (map f l) = Some b <-> exists a, nth_op n l = Some a /\ f a = b.
 Proof with try tauto.
  induction n;intros. simpl.
  case_eq (map f l);intros.
  icase l;inv H. split;intros.
  inv H. destruct H as [? [? ?]]. inv H.
  split;intros. inv H0.
  icase l;inv H. exists a...
  destruct H0. icase l. inv H.
  destruct H0. inv H...
  
  icase l;simpl.
  split;intros. inv H.
  destruct H as [? [? ?]]. inv H.
  apply IHn.
 Qed.

 Definition tupleI_varsable : varsable tupleI var.
 constructor. repeat intro.
 destruct X as [[[[? ?] ?] ?] ?].
 apply (l++l0++(vars l1)++(vars l2)).
 Defined.
 Instance tuple_vars : varsable tupleI var := tupleI_varsable.

 Lemma removeDup_var_In: forall {A B} `{EqDec A} `{varsable A B} (l : list A) v,
  In v (vars (removeDup l)) <-> In v (vars l).
 Proof with try tauto.
  induction l;intros. simpl...
  simpl. destruct (in_dec eq_dec a l).
  rewrite IHl. repeat rewrite in_app_iff.
  split;intros... icase H1...
  apply sublist_vars in i. spec i v...
  simpl. repeat rewrite in_app_iff.
  split;intro. icase H1. right. apply IHl...
  icase H1. right. apply IHl...
 Qed.
 
 Lemma tupleI2ies_var_In: forall v t,
  In v (vars (tupleI2ies t)) <-> In v (vars t).
 Proof with try tauto.
  intros.
  unfold tupleI2ies.
  destruct t as [[[[? ?] ?] ?] ?].
  simpl. repeat rewrite in_app_iff.
  repeat rewrite removeDup_In.
  generalize (removeDup_var_In l1 v);intro.
  generalize (removeDup_var_In l2 v);intro.
  rewrite H,H0...
 Qed.

 Lemma merge_tupleI_var_In: forall v t1 t2,
  In v (vars (merge_tupleI t1 t2)) <-> In v (vars t1) \/ In v (vars t2).
 Proof with try tauto.
  intros.
  unfold merge_tupleI. simpl.
  destruct t1 as [[[[? ?] ?] ?] ?].
  destruct t2 as [[[[? ?] ?] ?] ?].
  repeat rewrite in_app_iff.
  generalize (vars_app_rewrite _ l1 l5);intro.
  generalize (vars_app_rewrite _ l2 l6);intro.
  simpl in H,H0. unfold vars_list in H,H0.
  unfold share_dec_base.vars_list. simpl in *.
  rewrite H,H0. repeat rewrite in_app_iff...
 Qed.

 Lemma merge_list_tupleI_rewrite: forall t l,
  merge_list_tupleI (t::l) = merge_tupleI t (merge_list_tupleI l).
 Proof with try tauto.
  intro;simpl...
 Qed.

 Lemma merge_list_tupleI_var_In: forall lt v,
  In v (vars (merge_list_tupleI lt)) <-> exists t, In t lt /\ In v (vars t).
 Proof with try tauto.
  induction lt;intros.
  simpl... split;intro...
  destruct H...
  rewrite merge_list_tupleI_rewrite.
  rewrite merge_tupleI_var_In.
  split;intro. icase H.
  exists a;simpl...
  apply IHlt in H. destruct H.
  exists x;simpl...
  destruct H as [? [? ?]].
  icase H;subst... right.
  apply IHlt. exists x...
 Qed.

 Lemma eqnI2ies_var_exist: forall l v,
  In v (vars (eqnI2ies l)) <-> exists eqn b l', In (eqn,l',b) l /\ (In v (vars eqn) \/ In v l').
 Proof with try tauto.
  intros. unfold eqnI2ies.
  rewrite tupleI2ies_var_In.
  rewrite merge_list_tupleI_var_In.
  split;intros. destruct H as [? [? ?]].
  unfold leqnI2tupleI in H.
  rewrite in_map_iff in H.
  destruct H as [? [? ?]];subst.
  destruct x0 as [[? ?] ?].
  exists e,b,l0. split...
  simpl in H0. icase e.
  repeat rewrite in_app_iff in H0;simpl in *...
  repeat rewrite in_app_iff in *;simpl in *.
  repeat rewrite in_app_iff in *;simpl in *...
  repeat rewrite in_app_iff in *;simpl in *.
  repeat rewrite in_app_iff in *;simpl in *...

  destruct H as [? [? [? [? ?]]]].
  icase H0. apply in_map with (f:=eqnI2tupleI) in H.
  exists (eqnI2tupleI (x,x1,x0)). split...
  simpl. icase x;simpl in *. destruct H0;subst...
  rewrite in_app_iff;simpl...
  repeat rewrite in_app_iff;simpl...
  repeat rewrite in_app_iff;simpl...
  apply in_map with (f:=eqnI2tupleI) in H.
  exists (eqnI2tupleI (x,x1,x0)). split...
  simpl. icase x;simpl in *. repeat rewrite in_app_iff...
  repeat rewrite in_app_iff;simpl...
  repeat rewrite in_app_iff;simpl...
 Qed.

 Lemma ies2eqnI_exist: forall ies b eqn,
  In eqn (ies2eqnI ies b) -> 
  forall v, In v (snd (fst eqn)) -> In v (vars (fst (fst eqn))).
 Proof with try tauto.
  intros. unfold ies2eqnI in H.
  destruct ies as [lex lnz leql leqn];simpl in H.
  repeat rewrite in_app_iff in H.
  icase H.
  unfold lnzvar2eqnI in H.
  rewrite in_map_iff in H.
  destruct H as [? [? ?]];subst.
  simpl in *. destruct (in_dec eq_dec x lex)...
  icase H.
  unfold leql2eqnI in H.
  rewrite in_map_iff in H.
  destruct H as [? [? ?]];subst.
  simpl in *. repeat rewrite el_filter_In_iff in H0.
  destruct H0. repeat rewrite in_app_iff in H...

  unfold leqn2eqnI in H.
  rewrite in_map_iff in H.
  destruct H as [? [? ?]];subst.
  simpl in *. repeat rewrite el_filter_In_iff in H0.
  destruct H0. repeat rewrite in_app_iff in H...
 Qed.

 Lemma var_list_exist_iff: forall {A B} `{varsable A B} (l : list A) (b : B),
  In b (vars l) <-> exists a, In a l /\ In b (vars a).
 Proof with try tauto.
  induction l;intros.
  simpl. split;intro...
  destruct H0...
  simpl. repeat rewrite in_app_iff.
  split;intros.
  icase H0. exists a...
  apply IHl in H0. destruct H0. exists x...
  destruct H0 as [? [? ?]].
  destruct H0;subst... right. apply IHl.
  exists x...
 Qed.

 Lemma impl_partition_exist1: forall is ies1 ies2 v,
  In (ies1,ies2) (impl_partition is) ->
  In v (impl_exvars ies1) ->
  In v (impl_nzvars ies1) \/ In v (vars (impl_equalities ies1)) \/ 
  In v (vars (impl_equations ies1)).
 Proof with try tauto.
  intros.
  unfold impl_partition in H.
  destruct is as [ies3 ies4];simpl in H.
  rewrite in_map_iff in H. destruct H as [? [? ?]].
  destruct x as [l1 l2].
  apply ImplP.partition_IMPL_sublist1 in H1.
  inv H. unfold eqnI2ies in H0.
  rewrite tupleI2ies_exvars_In_combine in H0.
  destruct H0 as [? [? [? [? ?]]]].
  spec H1 (x,x1,x0) H.
  apply ies2eqnI_exist with (v:=v) in H1...
  icase x.
  left. unfold eqnI2ies.
  rewrite tupleI2ies_nzvars_In_combine.
  exists x0,x1. simpl in H1. destruct H1;subst...
  right;left. 
  generalize (var_list_exist_iff (impl_equalities (eqnI2ies l1)) v);intro.
  rewrite H2. exists e. split...
  unfold eqnI2ies. rewrite tupleI2ies_equalities_In_combine.
  exists x0,x1...
  right;right.
  generalize (var_list_exist_iff (impl_equations (eqnI2ies l1)) v);intro.
  rewrite H2. exists e. split...
  unfold eqnI2ies. rewrite tupleI2ies_equations_In_combine.
  exists x0,x1...  
 Qed.

 Lemma implP_partition_var_exist1: forall ies1 ies2 l1 l2 eqn v,
  In (l1,l2) (ImplP.partition_IMPL (ies2eqnI ies1 false) (ies2eqnI ies2 true)) ->
  In eqn l1 -> In v (snd (fst eqn)) ->
  In v (vars (fst (fst eqn))).
 Proof with try tauto.
  intros. apply ImplP.partition_IMPL_sublist1 in H.
  spec H eqn H0. apply ies2eqnI_exist with (v:=v) in H...
 Qed.

 Lemma Univ_exclude: forall ies v b,
  In (Univ v) (vars (ies2eqnI ies b)) ->
  ~In v (impl_exvars ies).
 Proof with try tauto.
  repeat intro.
  destruct ies as [lex lnz leql leqn].
  unfold ies2eqnI in H.
  repeat rewrite vars_app_rewrite in H.
  repeat rewrite in_app_iff in H.
  simpl in H0. icase H.

  apply var_list_exist in H.
  destruct H as [? [? ?]];subst.
  unfold lnzvar2eqnI in H.
  rewrite in_map_iff in H.
  destruct H as [? [? ?]]. subst.
  simpl in H1. destruct (in_dec eq_dec x0 lex).
  destruct (in_dec eq_dec x0 (x0::nil)).
  simpl in H1. destruct H1... inv H...
  simpl in n...
  destruct (in_dec eq_dec x0 nil)...
  simpl in H1. destruct H1... inv H...

  icase H. apply var_list_exist in H.
  destruct H as [? [? ?]];subst.
  unfold leql2eqnI in H.
  rewrite in_map_iff in H.
  destruct H as [? [? ?]]. subst.
  unfold eql2eqnI in H1.
  unfold vars,pi2.varsable_equation,varsable_eqnS' in H1.
  rewrite in_map_iff in H1.
  destruct H1 as [? [? ?]].
  destruct (in_dec eq_dec x (el_filter
             ((let (vars) := vars_transform equality_vars in vars) x0) lex)).
  inv H. inv H. apply n. rewrite el_filter_In_iff...

  apply var_list_exist in H.
  destruct H as [? [? ?]];subst.
  unfold leqn2eqnI in H.
  rewrite in_map_iff in H.
  destruct H as [? [? ?]]. subst.
  unfold eqn2eqnI in H1.
  unfold vars,pi2.varsable_equation,varsable_eqnS' in H1.
  rewrite in_map_iff in H1.
  destruct H1 as [? [? ?]].
  destruct (in_dec eq_dec x (el_filter
             ((let (vars) := vars_transform equation_vars in vars) x0) lex)).
  inv H. inv H. apply n. rewrite el_filter_In_iff...
 Qed.  

 Lemma Ex_include: forall ies v b,
  In (Ex v b) (vars (ies2eqnI ies b)) ->
  In v (impl_exvars ies).
 Proof with try tauto.
  intros.
  unfold ies2eqnI in H.
  destruct ies as [lex lnz leql leqn].
  repeat rewrite vars_app_rewrite in H.
  repeat rewrite in_app_iff in H.
  simpl. icase H.

  apply var_list_exist in H.
  destruct H as [? [? ?]].
  unfold lnzvar2eqnI in H.
  rewrite in_map_iff in H.
  destruct H as [? [? ?]];subst.
  simpl in H0.
  destruct (in_dec eq_dec x0 lex).
  destruct (in_dec eq_dec x0 (x0::nil))...
  simpl in H0. destruct H0... inv H...
  simpl in n...
  destruct (in_dec eq_dec x0 nil)...
  simpl in H0. destruct H0... inv H...

  icase H. apply var_list_exist in H.
  destruct H as [? [? ?]];subst.
  unfold leql2eqnI in H.
  rewrite in_map_iff in H.
  destruct H as [? [? ?]]. subst.
  unfold eql2eqnI in H0.
  unfold vars,pi2.varsable_equation,varsable_eqnS' in H0.
  rewrite in_map_iff in H0.
  destruct H0 as [? [? ?]].
  destruct (in_dec eq_dec x (el_filter
             ((let (vars) := vars_transform equality_vars in vars) x0) lex)).
  inv H. rewrite el_filter_In_iff in i... inv H...

  apply var_list_exist in H.
  destruct H as [? [? ?]];subst.
  unfold leqn2eqnI in H.
  rewrite in_map_iff in H.
  destruct H as [? [? ?]]. subst.
  unfold eqn2eqnI in H0.
  unfold vars,pi2.varsable_equation,varsable_eqnS' in H0.
  rewrite in_map_iff in H0.
  destruct H0 as [? [? ?]].
  destruct (in_dec eq_dec x (el_filter
             ((let (vars) := vars_transform equation_vars in vars) x0) lex)).
  inv H. rewrite el_filter_In_iff in i... inv H...
 Qed.
 
 Lemma Ex_Univ_False: forall ies v b,
  In (Univ v) (vars (ies2eqnI ies b)) ->
  In (Ex v b) (vars (ies2eqnI ies b)) ->
  False.
 Proof with try tauto.
  intros. apply Univ_exclude in H.
  apply Ex_include in H0...
 Qed.

 Lemma ies2eqnI_bool: forall ies eqn l b b',
  In (eqn,l,b) (ies2eqnI ies b') ->
  b = b'.
 Proof with try tauto.
  intros.
  unfold ies2eqnI in H.
  destruct ies as [lex lnz leql leqn].
  repeat rewrite in_app_iff in H.
  icase H. unfold lnzvar2eqnI in H.
  rewrite in_map_iff in H.
  destruct H as [? [? ?]]. inv H...
  icase H. unfold leql2eqnI in H.
  rewrite in_map_iff in H.
  destruct H as [? [? ?]]. inv H...
  unfold leqn2eqnI in H.
  rewrite in_map_iff in H.
  destruct H as [? [? ?]]. inv H...
 Qed.

 Lemma eqnI_Ex_var: forall eqn l b v,
  In v (vars eqn) -> In v l -> 
  In (Ex v b) (vars (eqn,l,b)).
 Proof with try tauto.
  intros.
  simpl. icase eqn.
  simpl in H. destruct H;subst...
  destruct (@in_dec var (@eq_dec var (@EqDec_transform var var_eq_dec)) v l)...
  simpl...
  rewrite in_map_iff. exists v.
  destruct (@in_dec var (@eq_dec var (@EqDec_transform var var_eq_dec)))...
  rewrite in_map_iff. exists v.
  destruct (@in_dec var (@eq_dec var (@EqDec_transform var var_eq_dec)))...
 Qed.

 Lemma eqnI_Univ_var: forall eqn l b v,
  In v (vars eqn) -> ~In v l -> 
  In (Univ v) (vars (eqn,l,b)).
 Proof with try tauto.
  intros.
  simpl. icase eqn.
  simpl in H. destruct H;subst...
  destruct (@in_dec var (@eq_dec var (@EqDec_transform var var_eq_dec)) v l)...
  simpl...
  rewrite in_map_iff. exists v.
  destruct (@in_dec var (@eq_dec var (@EqDec_transform var var_eq_dec)))...
  rewrite in_map_iff. exists v.
  destruct (@in_dec var (@eq_dec var (@EqDec_transform var var_eq_dec)))...
 Qed.

 Lemma impl_partition_disjoint_Cond1: forall is,
  disjoint_Cond (map (@fst _ _) (impl_partition is)).
 Proof with try tauto.
  intros. unfold disjoint_Cond. repeat intro.
  destruct H2. unfold impl_partition in *.
  destruct is as [ies3 ies4];simpl in H,H0.
  apply nth_op_map_Some_iff in H.
  apply nth_op_map_Some_iff in H0.
  destruct H as [? [? ?]];subst.
  destruct H0 as [? [? ?]];subst.
  apply nth_op_map_Some_iff in H.
  apply nth_op_map_Some_iff in H0.
  destruct H as [? [? ?]];subst.
  destruct H0 as [? [? ?]];subst.
  destruct x2. destruct x0.
  generalize (ImplP.partition_IMPL_disjoint _ _ _ _ _ _ _ _ H H0 H1);intro.
  unfold eqnI2is,fst in H2,H3.
  rewrite eqnI2ies_var_exist in H2,H3.
  destruct H2 as [? [? [? [? ?]]]].
  destruct H3 as [? [? [? [? ?]]]].
  assert (In (l1,l2) (ImplP.partition_IMPL (ies2eqnI ies3 false) (ies2eqnI ies4 true))).
   apply nth_op_In;eauto.
  assert (In (l,l0) (ImplP.partition_IMPL (ies2eqnI ies3 false) (ies2eqnI ies4 true))).
   apply nth_op_In;eauto.
  assert (x4 = false).
   apply ImplP.partition_IMPL_sublist1 in H7.
   spec H7 (x3,x5,x4) H3.
   apply ies2eqnI_bool in H7...
  subst.
  assert (x1 = false).
   apply ImplP.partition_IMPL_sublist1 in H8.
   spec H8 (x0,x2,x1) H2.
   apply ies2eqnI_bool in H8...
  subst.

  destruct (in_dec eq_dec x x5).

  generalize (implP_partition_var_exist1 _ _ _ _ _ _ H7 H3 i0);intro.
  unfold fst in H9.
  generalize (eqnI_Ex_var _ _ false _ H9 i0);intro.
  generalize (sublist_vars _ _ H3 _ H10);intro.
  destruct (in_dec eq_dec x x2).
   generalize (implP_partition_var_exist1 _ _ _ _ _ _ H8 H2 i1);intro.
   unfold fst in H12.
   generalize (eqnI_Ex_var _ _ false _ H12 i1);intro.
   generalize (sublist_vars _ _ H2 _ H13);intro.
   generalize (H4 (Ex x false));intro.
   apply H15.
   repeat rewrite vars_app_rewrite.
   repeat rewrite in_app_iff...

   assert (In x (vars x0)) by tauto.
   generalize (eqnI_Univ_var _ _ false _ H12 n);intro.
   generalize (sublist_vars _ _ H2 _ H13);intro.
   generalize (ImplP.partition_IMPL_sublist1 _ _ _ _ H7);intro.
   generalize (ImplP.partition_IMPL_sublist1 _ _ _ _ H8);intro.
   generalize (sublist_listvars _ _ H15 _ H11);intro.
   generalize (sublist_listvars _ _ H16 _ H14);intro.
   eapply Ex_Univ_False;eauto.

  assert (In x (vars x3)) by tauto.
  generalize (eqnI_Univ_var _ _ false _ H9 n);intro.
  generalize (sublist_vars _ _ H3 _ H10);intro.
  destruct (in_dec eq_dec x x2).
   generalize (implP_partition_var_exist1 _ _ _ _ _ _ H8 H2 i0);intro.
   unfold fst in H12.
   generalize (eqnI_Ex_var _ _ false _ H12 i0);intro.
   generalize (sublist_vars _ _ H2 _ H13);intro.
   generalize (sublist_vars _ _ H3 _ H10);intro.
   generalize (ImplP.partition_IMPL_sublist1 _ _ _ _ H7);intro.
   generalize (ImplP.partition_IMPL_sublist1 _ _ _ _ H8);intro.
   generalize (sublist_listvars _ _ H16 _ H15);intro.
   generalize (sublist_listvars _ _ H17 _ H14);intro.
   eapply Ex_Univ_False;eauto.
  
   assert (In x (vars x0)) by tauto.
   generalize (eqnI_Univ_var _ _ false _ H12 n0);intro.
   generalize (sublist_vars _ _ H2 _ H13);intro.
   generalize (H4 (Univ x));intro.
   apply H15.
   repeat rewrite vars_app_rewrite.
   repeat rewrite in_app_iff...
 Qed.

 Lemma implP_partition_var_exist2: forall ies1 ies2 l1 l2 eqn v,
  In (l1,l2) (ImplP.partition_IMPL (ies2eqnI ies1 false) (ies2eqnI ies2 true)) ->
  In eqn l2 -> In v (snd (fst eqn)) ->
  In v (vars (fst (fst eqn))).
 Proof with try tauto.
  intros. apply ImplP.partition_IMPL_sublist2 in H.
  spec H eqn H0. apply ies2eqnI_exist with (v:=v) in H...
 Qed.

 Lemma impl_partition_disjoint_Cond2: forall is,
  disjoint_Cond (map (@snd _ _) (impl_partition is)).
 Proof with try tauto.
  intros. unfold disjoint_Cond. repeat intro.
  destruct H2. unfold impl_partition in *.
  destruct is as [ies3 ies4];simpl in H,H0.
  apply nth_op_map_Some_iff in H.
  apply nth_op_map_Some_iff in H0.
  destruct H as [? [? ?]];subst.
  destruct H0 as [? [? ?]];subst.
  apply nth_op_map_Some_iff in H.
  apply nth_op_map_Some_iff in H0.
  destruct H as [? [? ?]];subst.
  destruct H0 as [? [? ?]];subst.
  destruct x2. destruct x0.
  generalize (ImplP.partition_IMPL_disjoint _ _ _ _ _ _ _ _ H H0 H1);intro.
  unfold eqnI2is,snd in H2,H3.
  rewrite eqnI2ies_var_exist in H2,H3.
  destruct H2 as [? [? [? [? ?]]]].
  destruct H3 as [? [? [? [? ?]]]].
  assert (In (l1,l2) (ImplP.partition_IMPL (ies2eqnI ies3 false) (ies2eqnI ies4 true))).
   apply nth_op_In;eauto.
  assert (In (l,l0) (ImplP.partition_IMPL (ies2eqnI ies3 false) (ies2eqnI ies4 true))).
   apply nth_op_In;eauto.
  assert (x4 = true).
   apply ImplP.partition_IMPL_sublist2 in H7.
   spec H7 (x3,x5,x4) H3.
   apply ies2eqnI_bool in H7...
  subst.
  assert (x1 = true).
   apply ImplP.partition_IMPL_sublist2 in H8.
   spec H8 (x0,x2,x1) H2.
   apply ies2eqnI_bool in H8...
  subst.

  destruct (in_dec eq_dec x x5).

  generalize (implP_partition_var_exist2 _ _ _ _ _ _ H7 H3 i0);intro.
  unfold fst in H9.
  generalize (eqnI_Ex_var _ _ true _ H9 i0);intro.
  generalize (sublist_vars _ _ H3 _ H10);intro.
  destruct (in_dec eq_dec x x2).
   generalize (implP_partition_var_exist2 _ _ _ _ _ _ H8 H2 i1);intro.
   unfold fst in H12.
   generalize (eqnI_Ex_var _ _ true _ H12 i1);intro.
   generalize (sublist_vars _ _ H2 _ H13);intro.
   generalize (H4 (Ex x true));intro.
   apply H15.
   repeat rewrite vars_app_rewrite.
   repeat rewrite in_app_iff...

   assert (In x (vars x0)) by tauto.
   generalize (eqnI_Univ_var _ _ true _ H12 n);intro.
   generalize (sublist_vars _ _ H2 _ H13);intro.
   generalize (ImplP.partition_IMPL_sublist2 _ _ _ _ H7);intro.
   generalize (ImplP.partition_IMPL_sublist2 _ _ _ _ H8);intro.
   generalize (sublist_listvars _ _ H15 _ H11);intro.
   generalize (sublist_listvars _ _ H16 _ H14);intro.
   eapply Ex_Univ_False;eauto.

  assert (In x (vars x3)) by tauto.
  generalize (eqnI_Univ_var _ _ true _ H9 n);intro.
  generalize (sublist_vars _ _ H3 _ H10);intro.
  destruct (in_dec eq_dec x x2).
   generalize (implP_partition_var_exist2 _ _ _ _ _ _ H8 H2 i0);intro.
   unfold fst in H12.
   generalize (eqnI_Ex_var _ _ true _ H12 i0);intro.
   generalize (sublist_vars _ _ H2 _ H13);intro.
   generalize (sublist_vars _ _ H3 _ H10);intro.
   generalize (ImplP.partition_IMPL_sublist2 _ _ _ _ H7);intro.
   generalize (ImplP.partition_IMPL_sublist2 _ _ _ _ H8);intro.
   generalize (sublist_listvars _ _ H16 _ H15);intro.
   generalize (sublist_listvars _ _ H17 _ H14);intro.
   eapply Ex_Univ_False;eauto.
  
   assert (In x (vars x0)) by tauto.
   generalize (eqnI_Univ_var _ _ true _ H12 n0);intro.
   generalize (sublist_vars _ _ H2 _ H13);intro.
   generalize (H4 (Univ x));intro.
   apply H15.
   repeat rewrite vars_app_rewrite.
   repeat rewrite in_app_iff...
 Qed.

 Lemma ies2eqnI_nzvar_In: forall v b ies,
  In v (impl_nzvars ies) ->
  In (NZV v, el_filter (vars v) (impl_exvars ies), b) (ies2eqnI ies b).
 Proof with try tauto.
  intros. unfold ies2eqnI.
  destruct ies as [? ? ? ?]. simpl in *.
  repeat rewrite in_app_iff.
  left. unfold lnzvar2eqnI.
  rewrite in_map_iff. unfold nzvar2eqnI.
  exists v...
 Qed.

 Lemma ies2eqnI_eql_In: forall eql b ies,
  In eql (impl_equalities ies) ->
  In (EL eql, el_filter (vars eql) (impl_exvars ies), b) (ies2eqnI ies b).
 Proof with try tauto.
  intros. unfold ies2eqnI.
  destruct ies as [? ? ? ?]. simpl in *.
  repeat rewrite in_app_iff. right. left.
  unfold leql2eqnI.
  rewrite in_map_iff. unfold eql2eqnI.
  exists eql...
 Qed.

 Lemma ies2eqnI_eqn_In: forall eqn b ies,
  In eqn (impl_equations ies) ->
  In (EQ eqn, el_filter (vars eqn) (impl_exvars ies), b) (ies2eqnI ies b).
 Proof with try tauto.
  intros. unfold ies2eqnI.
  destruct ies as [? ? ? ?]. simpl in *.
  repeat rewrite in_app_iff. right. right.
  unfold leqn2eqnI.
  rewrite in_map_iff. unfold eqn2eqnI.
  exists eqn...
 Qed.

 Lemma impl_partition_exist_Cond1: forall is,
  exist_Cond (map (@fst _ _) (impl_partition is)) (fst is).
 Proof with try tauto.
  repeat intro.
  unfold exist_Cond.
  destruct is as [ies1 ies2]. split.

  repeat intro.
  generalize (ies2eqnI_nzvar_In _ false _ H);intro.
  generalize (ImplP.partition_IMPL_In1 _ (ies2eqnI ies2 true) _ H0);intro.
  destruct H1 as [? [? [? ?]]].
  exists (eqnI2ies x).
  rewrite in_map_iff. split.
  exists (eqnI2ies x,eqnI2ies x0).
  split... unfold impl_partition.
  rewrite in_map_iff. exists (x,x0)...
  unfold eqnI2ies.
  apply tupleI2ies_nzvars_In_combine.
  exists false,(el_filter (vars v) (impl_exvars ies1))...

  split. repeat intro.
  generalize (ies2eqnI_eql_In _ false _ H);intro.
  generalize (ImplP.partition_IMPL_In1 _ (ies2eqnI ies2 true) _ H0);intro.
  destruct H1 as [? [? [? ?]]].
  exists (eqnI2ies x).
  rewrite in_map_iff. split.
  exists (eqnI2ies x,eqnI2ies x0).
  split... unfold impl_partition.
  rewrite in_map_iff. exists (x,x0)...
  unfold eqnI2ies.
  apply tupleI2ies_equalities_In_combine.
  exists false,(el_filter (vars eql) (impl_exvars ies1))...

  repeat intro.
  generalize (ies2eqnI_eqn_In _ false _ H);intro.
  generalize (ImplP.partition_IMPL_In1 _ (ies2eqnI ies2 true) _ H0);intro.
  destruct H1 as [? [? [? ?]]].
  exists (eqnI2ies x).
  rewrite in_map_iff. split.
  exists (eqnI2ies x,eqnI2ies x0).
  split... unfold impl_partition.
  rewrite in_map_iff. exists (x,x0)...
  unfold eqnI2ies.
  apply tupleI2ies_equations_In_combine.
  exists false,(el_filter (vars eqn) (impl_exvars ies1))...
 Qed.

 Lemma impl_partition_exist_Cond2: forall is,
  exist_Cond (map (@snd _ _) (impl_partition is)) (snd is).
 Proof with try tauto.
  repeat intro.
  unfold exist_Cond.
  destruct is as [ies1 ies2]. split.

  repeat intro.
  generalize (ies2eqnI_nzvar_In _ true _ H);intro.
  generalize (ImplP.partition_IMPL_In2 (ies2eqnI ies1 false) _ _ H0);intro.
  destruct H1 as [? [? [? ?]]].
  exists (eqnI2ies x0).
  rewrite in_map_iff. split.
  exists (eqnI2ies x,eqnI2ies x0).
  split... unfold impl_partition.
  rewrite in_map_iff. exists (x,x0)...
  unfold eqnI2ies.
  apply tupleI2ies_nzvars_In_combine.
  exists true,(el_filter (vars v) (impl_exvars ies2))...

  split. repeat intro.
  generalize (ies2eqnI_eql_In _ true _ H);intro.
  generalize (ImplP.partition_IMPL_In2 (ies2eqnI ies1 false) _ _ H0);intro.
  destruct H1 as [? [? [? ?]]].
  exists (eqnI2ies x0).
  rewrite in_map_iff. split.
  exists (eqnI2ies x,eqnI2ies x0).
  split... unfold impl_partition.
  rewrite in_map_iff. exists (x,x0)...
  unfold eqnI2ies.
  apply tupleI2ies_equalities_In_combine.
  exists true,(el_filter (vars eql) (impl_exvars ies2))...

  repeat intro.
  generalize (ies2eqnI_eqn_In _ true _ H);intro.
  generalize (ImplP.partition_IMPL_In2 (ies2eqnI ies1 false) _ _ H0);intro.
  destruct H1 as [? [? [? ?]]].
  exists (eqnI2ies x0).
  rewrite in_map_iff. split.
  exists (eqnI2ies x,eqnI2ies x0).
  split... unfold impl_partition.
  rewrite in_map_iff. exists (x,x0)...
  unfold eqnI2ies.
  apply tupleI2ies_equations_In_combine.
  exists true,(el_filter (vars eqn) (impl_exvars ies2))...
 Qed.

 Lemma vars_var_id: forall l,
  vars l = l.
 Proof with try tauto.
  induction l; simpl in *...
  rewrite IHl...
 Qed.

 Lemma impl_partition_preserve_Cond1: forall is,
  preserve_Cond (map (@fst _ _) (impl_partition is)) (fst is).
 Proof with try tauto.
  repeat intro.
  repeat rewrite in_app_iff in H0.
  unfold impl_partition in H.
  rewrite in_map_iff in H.
  destruct H as [? [? ?]]. subst.
  destruct is as [ies1 ies2].
  repeat rewrite in_map_iff in H2.
  destruct H2 as [? [? ?]]. subst.
  destruct x0 as [l1 l2].
  unfold eqnI2is in *. unfold fst,snd in *.
  assert (In v (vars (eqnI2ies l1))). 
   destruct (eqnI2ies l1) as [? ? ? ?].
   simpl in *. repeat rewrite in_app_iff.
   generalize (vars_var_id impl_nzvars0);intro.
   simpl in H;rewrite H in H0...
  apply eqnI2ies_var_exist in H.
  destruct H as [? [? [? [? ?]]]].
  unfold eqnI2ies.
  apply tupleI2ies_exvars_In_combine.
  destruct H3. Focus 2. exists x,x0,x1...
  assert (x0 = false).
   apply ImplP.partition_IMPL_sublist1 in H2.
   spec H2 (x,x1,x0) H.
   apply ies2eqnI_bool in H2...
  subst.
  destruct (in_dec eq_dec v x1).

  generalize (eqnI_Ex_var _ _ false _ H3 i);intro.
  generalize (sublist_vars _ _ H _ H4);intro.
  apply var_list_exist in H5. destruct H5 as [? [? ?]].
  exists x,false,x1. split...

  generalize (eqnI_Univ_var _ _ false _ H3 n);intro.
  generalize (sublist_vars _ _ H _ H4);intro.
  apply var_list_exist in H5. destruct H5 as [? [? ?]].
  generalize (ImplP.partition_IMPL_sublist1 _ _ _ _ H2 _ H5);intro.
  generalize (sublist_vars _ _ H7 _ H6);intro.
  apply Univ_exclude in H8...
 Qed.

 Lemma impl_partition_preserve_Cond2: forall is,
  preserve_Cond (map (@snd _ _) (impl_partition is)) (snd is).
 Proof with try tauto.
  repeat intro.
  repeat rewrite in_app_iff in H0.
  unfold impl_partition in H.
  rewrite in_map_iff in H.
  destruct H as [? [? ?]]. subst.
  destruct is as [ies1 ies2].
  repeat rewrite in_map_iff in H2.
  destruct H2 as [? [? ?]]. subst.
  destruct x0 as [l1 l2].
  unfold eqnI2is in *. unfold fst,snd in *.
  assert (In v (vars (eqnI2ies l2))). 
   destruct (eqnI2ies l2) as [? ? ? ?].
   simpl in *. repeat rewrite in_app_iff.
   generalize (vars_var_id impl_nzvars0);intro.
   simpl in H;rewrite H in H0...
  apply eqnI2ies_var_exist in H.
  destruct H as [? [? [? [? ?]]]].
  unfold eqnI2ies.
  apply tupleI2ies_exvars_In_combine.
  destruct H3. Focus 2. exists x,x0,x1...
  assert (x0 = true).
   apply ImplP.partition_IMPL_sublist2 in H2.
   spec H2 (x,x1,x0) H.
   apply ies2eqnI_bool in H2...
  subst.
  destruct (in_dec eq_dec v x1).

  generalize (eqnI_Ex_var _ _ true _ H3 i);intro.
  generalize (sublist_vars _ _ H _ H4);intro.
  apply var_list_exist in H5. destruct H5 as [? [? ?]].
  exists x,true,x1. split...

  generalize (eqnI_Univ_var _ _ true _ H3 n);intro.
  generalize (sublist_vars _ _ H _ H4);intro.
  apply var_list_exist in H5. destruct H5 as [? [? ?]].
  generalize (ImplP.partition_IMPL_sublist2 _ _ _ _ H2 _ H5);intro.
  generalize (sublist_vars _ _ H7 _ H6);intro.
  apply Univ_exclude in H8...
 Qed.

 Lemma is_partition_correct1: forall is,
  (forall is', In is' (impl_partition is) -> IMPL is') ->
  IMPL is.
 Proof with try tauto.
  repeat intro.
  generalize (impl_partition_sub_Cond1 is);intro.
  generalize (impl_partition_disjoint_Cond1 is);intro.
  generalize (impl_partition_exist_Cond1 is);intro.
  generalize (impl_partition_preserve_Cond1 is);intro.
  generalize (ies_equiv_Cond (map (@fst _ _) (impl_partition is)) (fst is) rho H1 H2 H3 H4);intro.
  rewrite H5 in H0.
  generalize (impl_partition_sub_Cond2 is);intro.
  generalize (impl_partition_disjoint_Cond2 is);intro.
  generalize (impl_partition_exist_Cond2 is);intro.
  generalize (impl_partition_preserve_Cond2 is);intro.
  generalize (ies_equiv_Cond (map (@snd _ _) (impl_partition is)) (snd is) rho H6 H7 H8 H9);intro.
  rewrite H10. clear - H H0. intros.
  apply in_map_iff in H1.
  destruct H1 as [is' [H1 H2]]. subst.
  spec H is' H2. spec H0 (fst is').
  apply H. apply H0. apply in_map...
 Qed.

  (*Retrieve all elements in l but not in l'*)
  Fixpoint exclude {A : Type} `{eqd : EqDec A} (l lex : list A) : list A :=
  match l with
  | nil => nil
  | a::l' => match in_dec eqd a lex with
             |left _ => exclude l' lex
             |right _ => a::(exclude l' lex)
             end
  end.
  
  Lemma exclude_correct: forall {A : Type}  `{eqd : EqDec A} l lex (e : A),
   In e (exclude l lex) <-> In e l /\ ~In e lex.
  Proof.
   induction l;intros.
   simpl. tauto.
   split;intros. simpl in H.
   icase (in_dec eqd a lex).
   apply IHl in H. destruct H. split;trivial. right;trivial.
   destruct H. subst. split;trivial. left;trivial.
   apply IHl in H. destruct H. split;trivial. right;trivial.
   destruct H. simpl. icase (in_dec eqd a lex).
   apply IHl. split;trivial. destruct H;auto. subst a. contradiction.
   destruct H. subst. left. trivial.
   right. apply IHl. tauto.
  Qed.

 Lemma disjoint_obj_eval: forall l1 l2 (obj : object) rho rho1 rho2,
  disjoint l1 (vars obj) ->
  get_obj_val ([l2 => rho2] ([l1 => rho1] rho)) obj = get_obj_val ([l2 => rho2]rho) obj.
 Proof with try tauto.
  intros.
  icase obj.
  simpl. destruct (in_dec eq_dec v l2).
  repeat rewrite override_in with (E:=l2)...
  repeat rewrite override_not_in with (E:=l2)...
  rewrite override_not_in... spec H v. simpl in H...
 Qed.

 Lemma disjoint_eql_eval: forall l1 l2 (eql : equality) rho rho1 rho2,
  [l2 => rho2] ([l1 => rho1] rho) |= eql ->
  disjoint l1 (vars eql) ->
  [l2 => rho2] rho |= eql.
 Proof with try tauto.
  intros.
  destruct eql as [obj1 obj2]. simpl in *.
  rewrite disjoint_app1 in H0. 
  rewrite disjoint_obj_eval with (l1:=l1) (l2:=l2) in H...
  rewrite disjoint_obj_eval with (l1:=l1) (l2:=l2) in H...
 Qed.

 Lemma disjoint_eqn_eval: forall l1 l2 (eqn : equation) rho rho1 rho2,
  [l2 => rho2] ([l1 => rho1] rho) |= eqn ->
  disjoint l1 (vars eqn) ->
  [l2 => rho2] rho |= eqn.
 Proof with try tauto.
  intros.
  destruct eqn as [[obj1 obj2] obj3]. simpl in *.
  repeat rewrite disjoint_app1 in H0. 
  rewrite disjoint_obj_eval with (l1:=l1) (l2:=l2) in H...
  rewrite disjoint_obj_eval with (l1:=l1) (l2:=l2) in H...
  rewrite disjoint_obj_eval with (l1:=l1) (l2:=l2) in H...
 Qed.

 Lemma disjoint_nz_eval: forall l1 l2 (nz : var) rho rho1 rho2,
  [l2 => rho2] ([l1 => rho1] rho) |= nz ->
  disjoint l1 (vars nz) ->
  [l2 => rho2] rho |= nz.
 Proof with try tauto.
  intros. simpl in *.
  destruct (in_dec eq_dec nz l2).
  rewrite override_in... rewrite override_in in H...
  rewrite override_not_in... rewrite override_not_in in H...
  rewrite override_not_in in H... spec H0 nz;simpl in H0...
 Qed.
  
 Lemma disjoint_ies_eval: forall l (ies : impl_equation_system) rho rho',
  [l => rho'] rho |= ies ->
  disjoint l (vars ies) ->
  rho |= ies.
 Proof with try tauto.
  intros.
  destruct H as [rho'' H].
  exists rho''.
  destruct H as [? [? ?]].
  split.

  rewrite list_eval_rewrite. intros.
  rewrite list_eval_rewrite in H. spec H b H3.
  apply disjoint_eql_eval with (l1:=l) (rho1:=rho')...
  apply disjoint_comm.
  apply sublist_disjoint with (l2:= vars ies).
  apply sublist_vars in H3. repeat intro. spec H3 e H4.
  destruct ies. simpl. repeat rewrite in_app_iff...
  apply disjoint_comm...

  split.

  rewrite list_eval_rewrite. intros.
  rewrite list_eval_rewrite in H1. spec H1 b H3.
  apply disjoint_eqn_eval with (l1:=l) (rho1:=rho')...
  apply disjoint_comm.
  apply sublist_disjoint with (l2:= vars ies).
  apply sublist_vars in H3. repeat intro. spec H3 e H4.
  destruct ies. simpl. repeat rewrite in_app_iff...
  apply disjoint_comm...
  
  rewrite list_eval_rewrite. intros.
  rewrite list_eval_rewrite in H2. spec H2 b H3.
  apply disjoint_nz_eval with (l1:=l) (rho1:=rho')...
  apply disjoint_comm. repeat intro. simpl in H4.
  destruct H4. destruct H4;subst...
  spec H0 x. apply H0. split...
  destruct ies. simpl in *. repeat rewrite in_app_iff...
 Qed.
 
 Lemma disjoint_exclude_app: forall {A} `{EqDec A} (l l' l1 l2 : list A),
  disjoint l (exclude (l1++l2) l') <->
  disjoint l (exclude l1 l') /\ disjoint l (exclude l2 l').
 Proof with try tauto.
  intros.
  repeat split;repeat intro.
  spec H0 x. apply H0.
  rewrite exclude_correct. rewrite exclude_correct in H1.
  rewrite in_app_iff...
  spec H0 x. apply H0.
  rewrite exclude_correct. rewrite exclude_correct in H1.
  rewrite in_app_iff...
  destruct H0. spec H0 x. spec H2 x.
  rewrite exclude_correct in H0,H1,H2.
  rewrite in_app_iff in H1...
 Qed.

 Lemma disjoint_obj_eval_stronger:
  forall l1 l2 obj (rho rho1 rho2 : context),
  disjoint l1 (exclude (vars obj) l2) ->
  get_obj_val ([l2 => rho2]([l1 => rho1]rho)) obj =
  get_obj_val ([l2 => rho2]rho) obj.
 Proof with try tauto.
  intros. icase obj.
  simpl in *.
  destruct (@in_dec var pi1.var_eq_dec v l2).
  repeat rewrite override_in...
  repeat rewrite override_not_in...
  spec H v;simpl in H...
 Qed.

 Lemma disjoint_eql_eval_stronger: 
  forall (l1 l2 : list var) (eql : equality) (rho rho1 rho2 : context),
  [l2 => rho2]([l1 => rho1]rho) |= eql ->
  disjoint l1 (exclude (vars eql) l2) -> 
  [l2 => rho2]rho |= eql.
 Proof with try tauto.
  intros.
  destruct eql as [obj1 obj2];simpl in *.
  rewrite disjoint_exclude_app in H0.
  destruct H0.
  do 2 rewrite disjoint_obj_eval_stronger in H...
 Qed.

 Lemma disjoint_eqn_eval_stronger: 
  forall (l1 l2 : list var) (eqn : equation) (rho rho1 rho2 : context),
  [l2 => rho2]([l1 => rho1]rho) |= eqn ->
  disjoint l1 (exclude (vars eqn) l2) -> 
  [l2 => rho2]rho |= eqn.
 Proof with try tauto.
  intros.
  destruct eqn as [[obj1 obj2] obj3];simpl in *.
  repeat rewrite disjoint_exclude_app in H0.
  destruct H0.
  do 3 rewrite disjoint_obj_eval_stronger in H...
 Qed.

 Lemma disjoint_nzvar_eval_stronger: 
  forall (l1 l2 : list var) (nzv : var) (rho rho1 rho2 : context),
  [l2 => rho2]([l1 => rho1]rho) |= nzv ->
  disjoint l1 (exclude (vars nzv) l2) -> 
  [l2 => rho2]rho |= nzv.
 Proof with try tauto.
  intros. simpl in *.
  intro. apply H.
  destruct (@in_dec var pi1.var_eq_dec nzv l2).
  rewrite override_in with (E:=l2)...
  rewrite override_in with (E:=l2) in H1...
  rewrite override_not_in with (E:=l2)...
  rewrite override_not_in with (E:=l2) in H1...
  spec H0 nzv. simpl in H0.
  assert (~In nzv l1) by tauto.
  rewrite override_not_in...
 Qed.
  
 Lemma disjoint_ies_eval_stronger: forall l (ies : impl_equation_system) rho rho',
  [l => rho'] rho |= ies ->
  disjoint l (exclude (vars ies) (impl_exvars ies)) ->
  rho |= ies.
 Proof with try tauto.
  intros.
  destruct H as [rho'' H].
  exists rho''.
  destruct H as [? [? ?]].
  split.

  rewrite list_eval_rewrite. intros.
  rewrite list_eval_rewrite in H. spec H b H3.
  apply disjoint_eql_eval_stronger with (l1:=l) (rho1:=rho')...
  apply disjoint_comm.
  apply sublist_disjoint with (l2:= exclude (vars ies) (impl_exvars ies)).
  apply sublist_vars in H3. intro.
  repeat rewrite exclude_correct. intro.
  destruct H4;split...
  spec H3 e H4.
  destruct ies. simpl. repeat rewrite in_app_iff...
  apply disjoint_comm...

  split.

  rewrite list_eval_rewrite. intros.
  rewrite list_eval_rewrite in H1. spec H1 b H3.
  apply disjoint_eqn_eval_stronger with (l1:=l) (rho1:=rho')...
  apply disjoint_comm.
  apply sublist_disjoint with (l2:= exclude (vars ies) (impl_exvars ies)).
  apply sublist_vars in H3. intro.
  repeat rewrite exclude_correct. intro.
  destruct H4;split...
  spec H3 e H4.
  destruct ies. simpl. repeat rewrite in_app_iff...
  apply disjoint_comm...

  rewrite list_eval_rewrite. intros.
  rewrite list_eval_rewrite in H2. spec H2 b H3.
  apply disjoint_nzvar_eval_stronger with (l1:=l) (rho1:=rho')...
  apply disjoint_comm.
  apply sublist_disjoint with (l2:= exclude (vars ies) (impl_exvars ies)).
  apply sublist_vars in H3. intro.
  repeat rewrite exclude_correct. intro.
  destruct H4;split...
  spec H3 e H4. 
  rewrite vars_var_id in H3.
  destruct ies. simpl. repeat rewrite in_app_iff...
  apply disjoint_comm...
 Qed.

 Lemma eval_obj_override_disjoint: forall (obj: object) rho rho1 rho2 l1 l2,
  disjoint l1 (vars obj) ->
  get_obj_val ([l2 => rho2]([l1 => rho1]rho)) obj =
  get_obj_val ([l2 => rho2]rho) obj.
 Proof with try tauto.
  intros.
  icase obj.
  simpl. destruct (in_dec eq_dec v l2).
  repeat rewrite override_in...
  repeat rewrite override_not_in...
  spec H v. simpl in H...
 Qed.

 Lemma eval_eql_override_disjoint: forall (eql: equality) (rho rho1 rho2: context) l1 l2,
  disjoint l1 (vars eql) ->
  ([l2 => rho2]([l1 => rho1]rho) |= eql <->
   [l2 => rho2]rho |= eql).
 Proof with try tauto.
  intros.
  destruct eql as [obj1 obj2];simpl.
  simpl in H. rewrite disjoint_app_iff in H.
  repeat rewrite eval_obj_override_disjoint...
 Qed.

 Lemma eval_eqn_override_disjoint: forall (eqn: equation) (rho rho1 rho2: context) l1 l2,
  disjoint l1 (vars eqn) ->
  ([l2 => rho2]([l1 => rho1]rho) |= eqn <->
   [l2 => rho2]rho |= eqn).
 Proof with try tauto.
  intros.
  destruct eqn as [[obj1 obj2] obj3];simpl.
  simpl in H. repeat rewrite disjoint_app_iff in H.
  repeat rewrite eval_obj_override_disjoint...
 Qed.

 Lemma eval_nzvar_override_disjoint: forall (nzvar: var) (rho rho1 rho2: context) l1 l2,
  disjoint l1 (vars nzvar) ->
  ([l2 => rho2]([l1 => rho1]rho) |= nzvar <->
   [l2 => rho2]rho |= nzvar).
 Proof with try tauto.
  intros. simpl.
  destruct (in_dec eq_dec nzvar l2).
  repeat rewrite override_in with (E:=l2)...
  repeat rewrite override_not_in with (E:=l2)...
  spec H nzvar. simpl in H.
  assert (~In nzvar l1) by tauto.
  repeat rewrite override_not_in...
 Qed.

 Lemma eval_obj_override_reduce: forall (obj : object) rho rho1 rho2 l1 l2,
  sublist l1 l2 ->
  (forall v, In v (vars obj) -> In v l2 -> In v l1) ->
  get_obj_val ([l2 => ([l1 => rho1]rho2)]rho) obj =
  get_obj_val ([l1 => rho1]rho) obj.
 Proof with try tauto. 
  intros.
  icase obj.
  simpl in H0. spec H0 v.
  spec H0... simpl.
  destruct (in_dec eq_dec v l2).
  repeat rewrite override_in...
  repeat rewrite override_not_in...
  intro. apply n. apply H...
 Qed.
  
 Lemma eval_eql_override_reduce: forall (eql : equality) rho rho1 rho2 l1 l2,
  sublist l1 l2 ->
  (forall v, In v (vars eql) -> In v l2 -> In v l1) ->
  ([l2 => ([l1 => rho1]rho2)]rho |= eql <->
  [l1 => rho1]rho |= eql).
 Proof with try tauto.
  intros.
  destruct eql as [obj1 obj2]. simpl.
  repeat rewrite eval_obj_override_reduce...
  intros. spec H0 v;simpl in H0;apply H0... rewrite in_app_iff...
  intros. spec H0 v;simpl in H0;apply H0... rewrite in_app_iff...
 Qed.

 Lemma eval_eqn_override_reduce: forall (eqn : equation) rho rho1 rho2 l1 l2,
  sublist l1 l2 ->
  (forall v, In v (vars eqn) -> In v l2 -> In v l1) ->
  ([l2 => ([l1 => rho1]rho2)]rho |= eqn <->
  [l1 => rho1]rho |= eqn).
 Proof with try tauto.
  intros.
  destruct eqn as [[obj1 obj2] oj3]. simpl.
  repeat rewrite eval_obj_override_reduce...
  intros. spec H0 v;simpl in H0;apply H0... repeat rewrite in_app_iff...
  intros. spec H0 v;simpl in H0;apply H0... repeat rewrite in_app_iff...
  intros. spec H0 v;simpl in H0;apply H0... repeat rewrite in_app_iff...
 Qed.

 Lemma eval_nzvar_override_reduce: forall (nzv : var) rho rho1 rho2 l1 l2,
  sublist l1 l2 ->
  (forall v, In v (vars nzv) -> In v l2 -> In v l1) ->
  ([l2 => ([l1 => rho1]rho2)]rho |= nzv <->
  [l1 => rho1]rho |= nzv).
 Proof with try tauto.
  intros. spec H0 nzv.
  simpl in H0. spec H0... simpl.
  destruct (in_dec eq_dec nzv l2). 
  repeat rewrite override_in with (E:=l2)...
  repeat rewrite override_in...
  repeat rewrite override_not_in with (E:=l2)...
  spec H nzv. assert (~In nzv l1) by tauto.
  repeat rewrite override_not_in...
 Qed.

 Lemma eval_obj_override_reduce2: forall (obj:object) rho rho1 rho2 l1 l2,
  sublist (vars obj) (l1++l2) ->
  get_obj_val ([l2 => rho2]([l1 => rho1]rho)) obj = 
  get_obj_val ([l2 => rho2]rho1) obj.
 Proof with try tauto.
  intros. icase obj.
  spec H v;simpl in H.
  spec H... simpl.
  destruct (in_dec eq_dec v l2).
  repeat rewrite override_in...
  repeat rewrite override_not_in with (E:=l2)...
  rewrite override_in... rewrite in_app_iff in H...
 Qed.
  
 Lemma eval_eql_override_reduce2: forall (eql : equality) rho rho1 rho2 l1 l2,
  sublist (vars eql) (l1++l2) ->
 ([l2 => rho2]([l1 => rho1] rho) |= eql <->
  [l2 => rho2] rho1 |= eql). 
 Proof with try tauto.
  intros.
  destruct eql as [obj1 obj2].
  simpl. repeat rewrite eval_obj_override_reduce2...
  repeat intro. apply H. simpl.
  rewrite in_app_iff...
  repeat intro. apply H. simpl.
  rewrite in_app_iff...
 Qed.

 Lemma eval_eqn_override_reduce2: forall (eqn : equation) rho rho1 rho2 l1 l2,
  sublist (vars eqn) (l1++l2) ->
 ([l2 => rho2]([l1 => rho1] rho) |= eqn <->
  [l2 => rho2] rho1 |= eqn). 
 Proof with try tauto.
  intros.
  destruct eqn as [[obj1 obj2] obj3].
  simpl. repeat rewrite eval_obj_override_reduce2...
  repeat intro. apply H. simpl.
  repeat rewrite in_app_iff...
  repeat intro. apply H. simpl.
  repeat rewrite in_app_iff...
  repeat intro. apply H. simpl.
  repeat rewrite in_app_iff...
 Qed.

 Lemma eval_nzvar_override_reduce2: forall (nzv : var) rho rho1 rho2 l1 l2,
  sublist (vars nzv) (l1++l2) ->
 ([l2 => rho2]([l1 => rho1] rho) |= nzv <->
  [l2 => rho2] rho1 |= nzv). 
 Proof with try tauto.
  intros. simpl.
  destruct (in_dec eq_dec nzv l2).
  repeat rewrite override_in with (E:=l2)...
  repeat rewrite override_not_in with (E:=l2)...
  spec H nzv. simpl in H. spec H...
  rewrite in_app_iff in H. icase H...
  repeat rewrite override_in...
 Qed.

 Lemma eval_obj_override_reduce3: forall (obj : object) rho rho1 rho2 l1 l2,
  disjoint (vars obj) l1 ->
  get_obj_val (([l2 => ([l1 => rho1]rho2)]rho)) obj =
  get_obj_val ([l2 => rho2]rho) obj.
 Proof with try tauto. 
  intros. icase obj. simpl.
  simpl in H. spec H v.
  destruct (in_dec eq_dec v l2).
  repeat rewrite override_in with (E:=l2)...
  rewrite override_not_in...
  intro. apply H. simpl in H...
  repeat rewrite override_not_in...
 Qed.

 Lemma eval_eql_override_reduce3: forall (eql : equality) rho rho1 rho2 l1 l2,
  disjoint (vars eql) l1 ->
  ([l2 => ([l1 => rho1]rho2)]rho |= eql <->
   [l2 => rho2]rho |= eql).
 Proof with try tauto.
  intros. destruct eql as [obj1 obj2];simpl.
  repeat rewrite eval_obj_override_reduce3...
  repeat intro. spec H x. apply H. simpl. rewrite in_app_iff...
  repeat intro. spec H x. apply H. simpl. rewrite in_app_iff...
 Qed.

 Lemma eval_eqn_override_reduce3: forall (eqn : equation) rho rho1 rho2 l1 l2,
  disjoint (vars eqn) l1 ->
  ([l2 => ([l1 => rho1]rho2)]rho |= eqn <->
   [l2 => rho2]rho |= eqn).
 Proof with try tauto.
  intros. destruct eqn as [[obj1 obj2] obj3];simpl.
  repeat rewrite eval_obj_override_reduce3...
  repeat intro. spec H x. apply H. simpl. repeat  rewrite in_app_iff...
  repeat intro. spec H x. apply H. simpl. repeat  rewrite in_app_iff...
  repeat intro. spec H x. apply H. simpl. repeat  rewrite in_app_iff...
 Qed.

 Lemma eval_nzvar_override_reduce3: forall (nzv : var) rho rho1 rho2 l1 l2,
  disjoint (vars nzv) l1 ->
  ([l2 => ([l1 => rho1]rho2)]rho |= nzv <->
   [l2 => rho2]rho |= nzv).
 Proof with try tauto.
  intros. simpl.
  destruct (in_dec eq_dec nzv l2).
  spec H nzv. simpl in H. assert (~In nzv l1) by tauto.
  repeat rewrite override_in with (E:=l2)...
  repeat rewrite override_not_in...
  repeat rewrite override_not_in...
 Qed.

 Lemma is_partition_var_eql: forall is is' eql v,
  In is' (impl_partition is) ->
  In eql (impl_equalities (fst is)) ->
  In v (vars eql) -> 
  ~In v (vars (fst is')) ->
  ~In v (impl_exvars (fst is)) ->
  In v (vars (snd is')) ->
  In v (impl_exvars (snd is')).
 Proof with try tauto.
  intros.
  destruct is as [ies1 ies2].
  destruct is' as [ies1' ies2'].
  unfold impl_partition in H.
  rewrite in_map_iff in H.
  destruct H as [? [? ?]];subst.
  unfold fst,snd in *.
  destruct x as [l1 l2]. inv H.
  generalize (ies2eqnI_eql_In _ false _ H0);intro.
  generalize (ImplP.partition_IMPL_In1 _ (ies2eqnI ies2 true) _ H);intro.
  destruct H6 as [l1' [l2' [? ?]]].
  apply eqnI2ies_var_exist in H4.
  destruct H4 as [eqns [b [l' [? ?]]]].
  unfold eqnI2ies.
  apply tupleI2ies_exvars_In_combine.
  destruct (in_dec eq_dec v l').
  exists eqns,b,l'...
  
  assert (In v (vars eqns)) by tauto.
  generalize (eqnI_Univ_var _ _ b _ H9 n);intro.
  assert (In (Univ v) (vars (EL eql, el_filter (vars eql) (impl_exvars ies1), false))).
   apply eqnI_Univ_var...
   intro. rewrite el_filter_In_iff in H11...
  apply nth_op_In in H5.
  apply nth_op_In in H7.
  destruct H5 as [i H5].
  destruct H7 as [j H7].
  generalize (ImplP.partition_IMPL_disjoint _ _ _ _ _ _ _ _ H5 H7);intro.
  spec H12. intro;subst.
  unfold pi2.equation in H7.
  unfold equationI in H5.
  rewrite H5 in H7. inv H7. 
  apply H2. apply eqnI2ies_var_exist.
  exists (EL eql),false,(el_filter (vars eql) (impl_exvars ies1))...
  spec H12 (@Univ var bool v).
  elimtype False. apply H12.
  split. rewrite vars_app_rewrite.
  rewrite in_app_iff. right.
  eapply sublist_vars;eauto.
  rewrite vars_app_rewrite.
  rewrite in_app_iff. left.
  eapply sublist_vars;eauto.
 Qed.

 Lemma is_partition_var_eqn: forall is is' eqn v,
  In is' (impl_partition is) ->
  In eqn (impl_equations (fst is)) ->
  In v (vars eqn) -> 
  ~In v (vars (fst is')) ->
  ~In v (impl_exvars (fst is)) ->
  In v (vars (snd is')) ->
  In v (impl_exvars (snd is')).
 Proof with try tauto.
  intros.
  destruct is as [ies1 ies2].
  destruct is' as [ies1' ies2'].
  unfold impl_partition in H.
  rewrite in_map_iff in H.
  destruct H as [? [? ?]];subst.
  unfold fst,snd in *.
  destruct x as [l1 l2]. inv H.
  generalize (ies2eqnI_eqn_In _ false _ H0);intro.
  generalize (ImplP.partition_IMPL_In1 _ (ies2eqnI ies2 true) _ H);intro.
  destruct H6 as [l1' [l2' [? ?]]].
  apply eqnI2ies_var_exist in H4.
  destruct H4 as [eqns [b [l' [? ?]]]].
  unfold eqnI2ies.
  apply tupleI2ies_exvars_In_combine.
  destruct (in_dec eq_dec v l').
  exists eqns,b,l'...
  
  assert (In v (vars eqns)) by tauto.
  generalize (eqnI_Univ_var _ _ b _ H9 n);intro.
  assert (In (Univ v) (vars (EQ eqn, el_filter (vars eqn) (impl_exvars ies1), false))).
   apply eqnI_Univ_var...
   intro. rewrite el_filter_In_iff in H11...
  apply nth_op_In in H5.
  apply nth_op_In in H7.
  destruct H5 as [i H5].
  destruct H7 as [j H7].
  generalize (ImplP.partition_IMPL_disjoint _ _ _ _ _ _ _ _ H5 H7);intro.
  spec H12. intro;subst.
  unfold pi2.equation in H7.
  unfold equationI in H5.
  rewrite H5 in H7. inv H7. 
  apply H2. apply eqnI2ies_var_exist.
  exists (EQ eqn),false,(el_filter (vars eqn) (impl_exvars ies1))...
  spec H12 (@Univ var bool v).
  elimtype False. apply H12.
  split. rewrite vars_app_rewrite.
  rewrite in_app_iff. right.
  eapply sublist_vars;eauto.
  rewrite vars_app_rewrite.
  rewrite in_app_iff. left.
  eapply sublist_vars;eauto.
 Qed.

 Lemma is_partition_var_nzvar: forall is is' nzv v,
  In is' (impl_partition is) ->
  In nzv (impl_nzvars (fst is)) ->
  In v (vars nzv) -> 
  ~In v (vars (fst is')) ->
  ~In v (impl_exvars (fst is)) ->
  In v (vars (snd is')) ->
  In v (impl_exvars (snd is')).
 Proof with try tauto.
  intros.
  destruct is as [ies1 ies2].
  destruct is' as [ies1' ies2'].
  unfold impl_partition in H.
  rewrite in_map_iff in H.
  destruct H as [? [? ?]];subst.
  unfold fst,snd in *.
  destruct x as [l1 l2]. inv H.
  generalize (ies2eqnI_nzvar_In _ false _ H0);intro.
  generalize (ImplP.partition_IMPL_In1 _ (ies2eqnI ies2 true) _ H);intro.
  destruct H6 as [l1' [l2' [? ?]]].
  apply eqnI2ies_var_exist in H4.
  destruct H4 as [eqns [b [l' [? ?]]]].
  unfold eqnI2ies.
  apply tupleI2ies_exvars_In_combine.
  destruct (in_dec eq_dec v l').
  exists eqns,b,l'...
  
  assert (In v (vars eqns)) by tauto.
  generalize (eqnI_Univ_var _ _ b _ H9 n);intro.
  assert (In (Univ v) (vars (NZV nzv, el_filter (vars nzv) (impl_exvars ies1), false))).
   apply eqnI_Univ_var...
   intro. rewrite el_filter_In_iff in H11...
  apply nth_op_In in H5.
  apply nth_op_In in H7.
  destruct H5 as [i H5].
  destruct H7 as [j H7].
  generalize (ImplP.partition_IMPL_disjoint _ _ _ _ _ _ _ _ H5 H7);intro.
  spec H12. intro;subst.
  unfold pi2.equation in H7.
  unfold equationI in H5.
  rewrite H5 in H7. inv H7. 
  apply H2. apply eqnI2ies_var_exist.
  exists (NZV nzv),false,(el_filter (vars nzv) (impl_exvars ies1))...
  spec H12 (@Univ var bool v).
  elimtype False. apply H12.
  split. rewrite vars_app_rewrite.
  rewrite in_app_iff. right.
  eapply sublist_vars;eauto.
  rewrite vars_app_rewrite.
  rewrite in_app_iff. left.
  eapply sublist_vars;eauto.
 Qed.

 Lemma is_partition_correct2 : forall is,
  IMPL is -> SAT (ies2ses (fst is)) ->
  forall is', In is' (impl_partition is) -> IMPL is'.
 Proof with try tauto.
  repeat intro.
  destruct H0 as [rho' H0].
  assert ([(exclude (vars (fst is)) (exclude (vars is') (exclude (impl_exvars (snd is')) (vars (fst is')) ))) => rho'] rho |= (fst is)).
   destruct H2 as [rho'' H2].
   exists ([(impl_exvars (fst is')) => rho'']rho').
   destruct H2 as [H21 [H22 H23]].
   destruct H0 as [H01 [H02 H03]].
   split.
   (*C1: Equality*)
   rewrite list_eval_rewrite. intros.
   destruct (in_dec eq_dec b (impl_equalities (fst is'))).
   (*In*)
   rewrite list_eval_rewrite in H21. spec H21 b. spec H21...
   rewrite eval_eql_override_disjoint.
   
    Focus 2.
    repeat intro.
    repeat rewrite exclude_correct in H2.
    destruct H2. destruct H2.
    apply H4. split.
    generalize (sublist_vars _ _ i x H3);intro.
    destruct is'. destruct i0. simpl in *;repeat rewrite in_app_iff...
    intro. destruct H5. apply H6.
    generalize (sublist_vars _ _ i x H3);intro.
    destruct is'. destruct i0. simpl in *;repeat rewrite in_app_iff...
    
   apply eval_eql_override_reduce...
   generalize (impl_partition_sub_Cond1 is (fst is'));intro.
   spec H2. rewrite in_map_iff. exists is'...
   unfold subsystem in H2.
   destruct (fst is');destruct (fst is)...
   intros. generalize (impl_partition_preserve_Cond1 is (fst is'));intro.
   spec H4. rewrite in_map_iff. exists is'...
   spec H4 v. apply H4...
   repeat rewrite in_app_iff.
   generalize (sublist_vars _ _ i _ H2);intro...
   (*Not In*)
   rewrite list_eval_rewrite in H01. spec H01 b. spec H01...
   assert (disjoint (vars b) (vars (fst is'))).
    repeat intro.
    destruct H2.
    generalize (impl_partition_exist_Cond1 is);intro.
    destruct H4 as [_ [H4 _]]. spec H4 b H0.
    destruct H4 as [? [? ?]]. rewrite in_map_iff in H4.
    destruct H4 as [? [? ?]]. subst.
    apply nth_op_In in H6. apply nth_op_In in H1.
    destruct H1 as [i H1]. destruct H6 as [j H6].
    destruct (eq_dec i j). subst. 
    unfold impl_system in H1;congruence.
    generalize (impl_partition_disjoint_Cond1 is i j (fst is') (fst x1));intro.
    spec H4. apply nth_op_map_Some_iff.
    exists is'...
    spec H4. apply nth_op_map_Some_iff.
    exists x1...
    spec H4... spec H4 x.
    apply H4. split...
    generalize (sublist_vars _ _ H5 _ H2);intro.
    destruct (fst x1). simpl. repeat rewrite in_app_iff...
   assert (sublist (vars b) ((exclude (vars (fst is))
    (exclude (vars is') (exclude (impl_exvars (snd is')) (vars (fst is')))))++(impl_exvars (fst is)))).
    repeat intro. rewrite in_app_iff.
    destruct (in_dec eq_dec e (impl_exvars (fst is)))...
    left.
    repeat rewrite exclude_correct. split.
    generalize (impl_partition_exist_Cond1 is);intro.
    destruct H4 as [_ [H4 _]]. spec H4 b H0.
    destruct H4 as [? [? ?]].
    rewrite in_map_iff in H4.
    destruct H4 as [? [? ?]];subst.
    generalize (sublist_vars _ _ H0 _ H3);intro.
    destruct (fst is). simpl. repeat rewrite in_app_iff...
    intro. destruct H4. apply H5.
    split.
    destruct (in_dec eq_dec e (impl_exvars (snd is')))... 
    eapply is_partition_var_eql;eauto.
    spec H2 e... destruct is'. simpl in H4.
    rewrite in_app_iff in H4. spec H2 e...
    intro. spec H2 e...
   apply eval_eql_override_reduce2...
   apply eval_eql_override_reduce3.
   destruct (fst is'). simpl in H2.
   repeat rewrite disjoint_app_iff in H2...
   rewrite context_override_idem...

   split.
   (*C2 : equations*)
   rewrite list_eval_rewrite. intros.
   destruct (in_dec eq_dec b (impl_equations (fst is'))).
   (*In*)
   rewrite list_eval_rewrite in H22. spec H22 b. spec H22...
   rewrite eval_eqn_override_disjoint.
   
    Focus 2.
    repeat intro.
    repeat rewrite exclude_correct in H2.
    destruct H2. destruct H2.
    apply H4. split.
    generalize (sublist_vars _ _ i x H3);intro.
    destruct is'. destruct i0. simpl in *;repeat rewrite in_app_iff...
    intro. destruct H5. apply H6.
    generalize (sublist_vars _ _ i x H3);intro.
    destruct is'. destruct i0. simpl in *;repeat rewrite in_app_iff...
    
   apply eval_eqn_override_reduce...
   generalize (impl_partition_sub_Cond1 is (fst is'));intro.
   spec H2. rewrite in_map_iff. exists is'...
   unfold subsystem in H2.
   destruct (fst is');destruct (fst is)...
   intros. generalize (impl_partition_preserve_Cond1 is (fst is'));intro.
   spec H4. rewrite in_map_iff. exists is'...
   spec H4 v. apply H4...
   repeat rewrite in_app_iff.
   generalize (sublist_vars _ _ i _ H2);intro...
   (*Not In*)
   rewrite list_eval_rewrite in H02. spec H02 b. spec H02...
   assert (disjoint (vars b) (vars (fst is'))).
    repeat intro.
    destruct H2.
    generalize (impl_partition_exist_Cond1 is);intro.
    destruct H4 as [_ [_ H4]]. spec H4 b H0.
    destruct H4 as [? [? ?]]. rewrite in_map_iff in H4.
    destruct H4 as [? [? ?]]. subst.
    apply nth_op_In in H6. apply nth_op_In in H1.
    destruct H1 as [i H1]. destruct H6 as [j H6].
    destruct (eq_dec i j). subst. 
    unfold impl_system in H1;congruence.
    generalize (impl_partition_disjoint_Cond1 is i j (fst is') (fst x1));intro.
    spec H4. apply nth_op_map_Some_iff.
    exists is'...
    spec H4. apply nth_op_map_Some_iff.
    exists x1...
    spec H4... spec H4 x.
    apply H4. split...
    generalize (sublist_vars _ _ H5 _ H2);intro.
    destruct (fst x1). simpl. repeat rewrite in_app_iff...
   assert (sublist (vars b) ((exclude (vars (fst is))
    (exclude (vars is') (exclude (impl_exvars (snd is')) (vars (fst is')))))++(impl_exvars (fst is)))).
    repeat intro. rewrite in_app_iff.
    destruct (in_dec eq_dec e (impl_exvars (fst is)))...
    left.
    repeat rewrite exclude_correct. split.
    generalize (impl_partition_exist_Cond1 is);intro.
    destruct H4 as [_ [_ H4]]. spec H4 b H0.
    destruct H4 as [? [? ?]].
    rewrite in_map_iff in H4.
    destruct H4 as [? [? ?]];subst.
    generalize (sublist_vars _ _ H0 _ H3);intro.
    destruct (fst is). simpl. repeat rewrite in_app_iff...
    intro. destruct H4. apply H5.
    split.
    destruct (in_dec eq_dec e (impl_exvars (snd is')))... 
    eapply is_partition_var_eqn;eauto.
    spec H2 e... destruct is'. simpl in H4.
    rewrite in_app_iff in H4. spec H2 e...
    intro. spec H2 e...
   apply eval_eqn_override_reduce2...
   apply eval_eqn_override_reduce3.
   destruct (fst is'). simpl in H2.
   repeat rewrite disjoint_app_iff in H2...
   rewrite context_override_idem...
   
   (*C3:nzvar*)
   rewrite list_eval_rewrite. intros.
   destruct (in_dec eq_dec b (impl_nzvars (fst is'))).
   (*In*)
   rewrite list_eval_rewrite in H23. spec H23 b. spec H23...
   rewrite eval_nzvar_override_disjoint.
   
    Focus 2.
    repeat intro.
    repeat rewrite exclude_correct in H2.
    destruct H2. destruct H2.
    apply H4. split.
    generalize (sublist_vars _ _ i x H3);intro. rewrite vars_var_id in H5.
    destruct is'. destruct i0. simpl in *;repeat rewrite in_app_iff...
    intro. destruct H5. apply H6.
    generalize (sublist_vars _ _ i x H3);intro. rewrite vars_var_id in H7.
    destruct is'. destruct i0. simpl in *;repeat rewrite in_app_iff...
    
   apply eval_nzvar_override_reduce...
   generalize (impl_partition_sub_Cond1 is (fst is'));intro.
   spec H2. rewrite in_map_iff. exists is'...
   unfold subsystem in H2.
   destruct (fst is');destruct (fst is)...
   intros. generalize (impl_partition_preserve_Cond1 is (fst is'));intro.
   spec H4. rewrite in_map_iff. exists is'...
   spec H4 v. apply H4...
   repeat rewrite in_app_iff.
   generalize (sublist_vars _ _ i _ H2);intro...
   (*Not In*)
   rewrite list_eval_rewrite in H03. spec H03 b. spec H03...
   assert (disjoint (vars b) (vars (fst is'))).
    repeat intro.
    destruct H2.
    generalize (impl_partition_exist_Cond1 is);intro.
    destruct H4 as [H4 [_ _]]. spec H4 b H0.
    destruct H4 as [? [? ?]]. rewrite in_map_iff in H4.
    destruct H4 as [? [? ?]]. subst.
    apply nth_op_In in H6. apply nth_op_In in H1.
    destruct H1 as [i H1]. destruct H6 as [j H6].
    destruct (eq_dec i j). subst. 
    unfold impl_system in H1;congruence.
    generalize (impl_partition_disjoint_Cond1 is i j (fst is') (fst x1));intro.
    spec H4. apply nth_op_map_Some_iff.
    exists is'...
    spec H4. apply nth_op_map_Some_iff.
    exists x1...
    spec H4... spec H4 x.
    apply H4. split...
    generalize (sublist_vars _ _ H5 _ H2);intro. rewrite vars_var_id in H7.
    destruct (fst x1). simpl. repeat rewrite in_app_iff...
   assert (sublist (vars b) ((exclude (vars (fst is))
    (exclude (vars is') (exclude (impl_exvars (snd is')) (vars (fst is')))))++(impl_exvars (fst is)))).
    repeat intro. rewrite in_app_iff.
    destruct (in_dec eq_dec e (impl_exvars (fst is)))...
    left.
    repeat rewrite exclude_correct. split.
    generalize (impl_partition_exist_Cond1 is);intro.
    destruct H4 as [H4 [_ _]]. spec H4 b H0.
    destruct H4 as [? [? ?]].
    rewrite in_map_iff in H4.
    destruct H4 as [? [? ?]];subst.
    generalize (sublist_vars _ _ H0 _ H3);intro. rewrite vars_var_id in H4.
    destruct (fst is). simpl. repeat rewrite in_app_iff...
    intro. destruct H4. apply H5.
    split.
    destruct (in_dec eq_dec e (impl_exvars (snd is')))... 
    eapply is_partition_var_nzvar;eauto.
    spec H2 e... destruct is'. simpl in H4.
    rewrite in_app_iff in H4. spec H2 e...
    intro. spec H2 e...
   apply eval_nzvar_override_reduce2...
   apply eval_nzvar_override_reduce3.
   destruct (fst is'). simpl in H2.
   repeat rewrite disjoint_app_iff in H2...
   rewrite context_override_idem...

  (*Now the easy part*)
  apply H in H3.
  apply subsystem_eval with (ies' := snd is') in H3.
  apply disjoint_ies_eval_stronger in H3...
  repeat intro. repeat rewrite exclude_correct in H4.
  destruct H4. destruct H4. apply H6.
  split... destruct H5.
  destruct is' as [? ?].
  simpl. rewrite in_app_iff...
  apply impl_partition_sub_Cond2.
  apply in_map_iff. exists is'...
  apply impl_partition_preserve_Cond2.
  apply in_map_iff. exists is'...
 Qed.

End System_Partition.
