Require Import msl.msl_standard.
Require Import share_dec_base.
Require Import base_properties.
Require Import NPeano.

  Inductive objectT {A B}: Type :=
   | Vobject : A -> objectT
   | Cobject : B -> objectT.

  Instance objectT_eq_dec : forall {A B} `{EqDec A} `{EqDec B}, EqDec (@objectT A B).
  Proof with congruence.
   repeat intro.
   icase a;icase a'.
   destruct (eq_dec a a0).
   left... right...
   right... right...
   destruct (eq_dec b b0).
   left... right...
  Defined.

  Definition get_obj_val {A B} (ctx : A -> B) (obj : @objectT A B) :=
   match obj with
   | Vobject v => ctx v
   | Cobject c => c
  end.
  Instance getable_obj_val {A B}: getable (A -> B) (@objectT A B) B :=
   Getable get_obj_val.

  Definition obj_h {A B} `{heightable B} := fun (obj : @objectT A B) =>
   match obj with
   | Vobject v => 0
   | Cobject c => |c|
   end.
  Definition is_height_zero_obj {A B} `{heightable B}: is_height_zero_spec (@obj_h A B _).
  Proof with auto.
   repeat intro.
   destruct a. left...
   destruct (is_height_zero b).
   left... right...
  Defined.
  Instance heightable_obj {A B} `{heightable B}: heightable (@objectT A B) :=
   Heightable obj_h is_height_zero_obj.

  Definition obj_ch {A B C} `{cheightable C A} := fun (ctx : C)(obj : @objectT A B) =>
   match obj with
   | Cobject c => 0
   | Vobject v => cheight ctx v
   end.
  Instance cheightable_obj {A B C} `{cheightable C A} : cheightable C (@objectT A B) :=
   Cheightable obj_ch.

  Instance obj_vars {A B} : varsable (@objectT A B) A.
   constructor. repeat intro. destruct X.
   apply (a::nil). apply nil.
  Defined.

Module Type DOMAIN.
 
 Parameter e : Type.
 Axiom e_eq_dec : EqDec e.
 Parameter join : e -> e -> e -> Prop.
 Parameter e_height : heightable e.
 Parameter bot : e.

End DOMAIN.

Module Share_Domain <: DOMAIN.

  Import Share.

  Definition e := share.
  Instance e_eq_dec : EqDec e := _.
  Definition join := fun (a b c : e) => join a b c.
  Instance e_height : heightable e := _.
  Definition bot := bot.

End Share_Domain.

Module Bool_Domain <: DOMAIN.

  Definition e : Type := bool.
  Instance e_eq_dec : EqDec e := bool_dec.
  Definition join := fun (b1 b2 b3 : bool) => b1 && b2 = false /\ b1||b2 = b3.
  Instance e_height : heightable e.
  constructor 1 with (fun e => 0).
  intro. left. trivial.
  Defined.
  Definition bot := false.

End Bool_Domain.

Module Type EQUATION_SYSTEM (Import sv : SV).

  Declare Module dom : DOMAIN.
  Import dom.
 
  Definition var := t.
  Definition s := e.
  Instance var_eq_dec : EqDec var := _.
  Definition object := @objectT var s.
  Definition equality := (object * object)%type.
  Axiom equality_eq_dec : EqDec equality.
  Definition equation := (object * object * object)%type.
  Axiom equation_eq_dec : EqDec equation.

  Record sat_equation_system : Type := Sat_equation_system {
    sat_nzvars        : list var;
    sat_equalities    : list equality;
    sat_equations     : list equation
  }.
  Record impl_equation_system : Type := Impl_equation_system {
    impl_exvars     : list var;
    impl_nzvars     : list var;
    impl_equalities : list equality;
    impl_equations  : list equation
  }.
  Definition impl_system : Type := (impl_equation_system * impl_equation_system)%type.

  (*EVAL*)
  Definition context := var -> s.
  Instance object_get : getable context object s := _ .
  Instance eval_equality : evalable context equality.
  constructor. repeat intro.
  destruct X0.
  apply (get X o = get X o0).
  Defined.
  Instance eval_equation : evalable context equation.
  constructor. repeat intro.
  destruct X0 as [[? ?] ?]. apply (join (get X o) (get X o0) (get X o1)).
  Defined.
  Instance eval_nzvars : evalable context var.
  constructor. repeat intro.
  apply (X X0 <> bot).
  Defined.

  Definition eval_sat_equation_system (ctx : context) (ses : sat_equation_system) : Prop :=
    ctx |= (sat_equalities ses) /\ 
    ctx |= (sat_equations ses) /\
    ctx |= (sat_nzvars ses).
  Instance evalable_sat_equation_system : evalable context sat_equation_system :=
    Evalable eval_sat_equation_system.

  Definition ies2ses := 
  fun (ies : impl_equation_system) => 
  Sat_equation_system (impl_nzvars ies) (impl_equalities ies) (impl_equations ies).

  Definition eval_impl_equation_system (ctx : context) (ies : impl_equation_system) : Prop:=
   e_eval ctx (impl_exvars ies) (ies2ses ies).
  Instance evalable_impl_equation_system : evalable context impl_equation_system :=
   Evalable eval_impl_equation_system.
 
  Definition eval_impl_system (ctx : context) (is : impl_system) : Prop :=
   ctx |= (fst is) -> ctx |= (snd is).
  Instance evalable_impl_system : evalable context impl_system :=
   Evalable eval_impl_system.

  Definition SAT (ses : sat_equation_system) := exists rho, rho |= ses.
  Definition IMPL (is : impl_system) := forall rho, rho |= is.

End EQUATION_SYSTEM.

Module Equation_system (Import sv : SV) (dom' : DOMAIN) <: EQUATION_SYSTEM sv with Module dom := dom'.

  Module dom := dom'.
  Import dom.

  Definition var := t.
  Definition s := e.
  Instance var_eq_dec : EqDec var := _.
  Definition object := @objectT var s.
  Definition equality := (object * object)%type.
  Instance equality_eq_dec : EqDec equality.
  Proof with congruence.
  repeat intro.
  destruct a;destruct a'.
  destruct (eq_dec o o1). subst.
  destruct (eq_dec o0 o2). subst.
  left... right... right...
  Defined.
  Definition equation := (object * object * object)%type.
  Instance equation_eq_dec : EqDec equation.
  Proof with congruence.
  repeat intro.
  destruct a as [[? ?] ?];destruct a' as [[? ?] ?].
  destruct (eq_dec o o2).
  destruct (eq_dec o0 o3).
  destruct (eq_dec o1 o4).
  left... right... right... right...
  Defined.

  Record sat_equation_system : Type := Sat_equation_system {
    sat_nzvars        : list var;
    sat_equalities    : list equality;
    sat_equations     : list equation
  }.
  Record impl_equation_system : Type := Impl_equation_system {
    impl_exvars     : list var;
    impl_nzvars     : list var;
    impl_equalities : list equality;
    impl_equations  : list equation
  }.

  Definition impl_system : Type := (impl_equation_system * impl_equation_system)%type.

  (*EVAL*)
  Definition context := var -> s.
  Instance object_get : getable context object s := _ .
  Instance eval_equality : evalable context equality.
  constructor. repeat intro.
  destruct X0.
  apply (get X o = get X o0).
  Defined.
  Instance eval_equation : evalable context equation.
  constructor. repeat intro.
  destruct X0 as [[? ?] ?]. apply (join (get X o) (get X o0) (get X o1)).
  Defined.
  Instance eval_nzvars : evalable context var.
  constructor. repeat intro.
  apply (X X0 <> bot).
  Defined.

  Definition eval_sat_equation_system (ctx : context) (ses : sat_equation_system) : Prop :=
    ctx |= (sat_equalities ses) /\ 
    ctx |= (sat_equations ses) /\
    ctx |= (sat_nzvars ses).
  Instance evalable_sat_equation_system : evalable context sat_equation_system :=
    Evalable eval_sat_equation_system.

  Definition ies2ses := 
  fun (ies : impl_equation_system) => 
  Sat_equation_system (impl_nzvars ies) (impl_equalities ies) (impl_equations ies).

  Definition eval_impl_equation_system (ctx : context) (ies : impl_equation_system) : Prop:=
   e_eval ctx (impl_exvars ies) (ies2ses ies).
  Instance evalable_impl_equation_system : evalable context impl_equation_system :=
   Evalable eval_impl_equation_system.
 
  Definition eval_impl_system (ctx : context) (is : impl_system) : Prop :=
   ctx |= (fst is) -> ctx |= (snd is).
  Instance evalable_impl_system : evalable context impl_system :=
   Evalable eval_impl_system.

  Definition SAT (ses : sat_equation_system) := exists rho, rho |= ses.
  Definition IMPL (is : impl_system) := forall rho, rho |= is.

End Equation_system.

Module Type SYSTEM_FEATURES (sv : SV )(Import es : EQUATION_SYSTEM sv).

  (*HEIGHT*)

  Instance object_height : heightable object := _.
  Definition equality_h := fun (eql : equality) => 
   let (o1,o2) := eql in max (|o1|) (|o2|).
  Definition equality_h_zero: is_height_zero_spec equality_h.
  Proof with tauto.
  repeat intro.
  destruct a. simpl.
  destruct (is_height_zero o).
  destruct (is_height_zero o0).
  left. rewrite max_zero...
  right. rewrite max_zero...
  right. rewrite max_zero...
  Defined.
  Instance equality_height : heightable equality :=
   Heightable equality_h equality_h_zero.
  Definition equation_h := fun (eqn : equation) => 
   match eqn with (o1,o2,o3) => max (max (|o1|)(|o2|)) (|o3|)  end.
  Definition equation_h_zero: is_height_zero_spec equation_h.
  Proof with tauto.
  repeat intro.
  destruct a as [[? ?] ?]. simpl.
  destruct (is_height_zero o).
  destruct (is_height_zero o0).
  destruct (is_height_zero o1).
  left. repeat rewrite max_zero...
  right. repeat rewrite max_zero...
  right. repeat rewrite max_zero...
  right. repeat rewrite max_zero...
  Defined.
  Instance equation_height : heightable equation :=
   Heightable equation_h equation_h_zero.
  
  Definition ses_h := fun (ses : sat_equation_system) =>
   max (|sat_equalities ses|) (|sat_equations ses|).
  Definition ses_h_zero: is_height_zero_spec ses_h.
  Proof with tauto.
  repeat intro.
  destruct a as [l1 l2 l3].
  unfold ses_h;simpl.
  destruct (is_height_zero l2).
  destruct (is_height_zero l3).
  left. simpl in e,e0. rewrite e,e0...
  right. intro. apply n.
  rewrite max_zero in H...
  right. intro. apply n.
  rewrite max_zero in H...
  Defined.
  Instance ses_height : heightable sat_equation_system :=
  Heightable ses_h ses_h_zero.
  Definition ies_h := fun (ies : impl_equation_system) =>
   max (|impl_equalities ies|) (|impl_equations ies|).
  Definition ies_h_zero: is_height_zero_spec ies_h.
  Proof with tauto.
  repeat intro.
  destruct a as [l1 l2 l3 l4].
  unfold ies_h;simpl.
  destruct (is_height_zero l3); try simpl in e.
  destruct (is_height_zero l4); try simpl in e0.
  left. rewrite e;rewrite e0...
  right. rewrite max_zero...
  right. rewrite max_zero...
  Defined.
  Instance ies_height : heightable impl_equation_system :=
  Heightable ies_h ies_h_zero.
  Definition is_h := fun (is :impl_system) => max (|fst is|)(|snd is|).
  Definition is_h_zero: is_height_zero_spec is_h.
  Proof with tauto.
  repeat intro.
  destruct a as [es1 es2].
  unfold is_h.
  destruct (is_height_zero es1).
  destruct (is_height_zero es2).
  left. rewrite max_zero...
  right. rewrite max_zero...
  right. rewrite max_zero...
  Defined.
  Instance is_height : heightable impl_system :=
  Heightable is_h is_h_zero.

  (*CHEIGHT*)

  Instance var_cheight : cheightable context var.
  constructor. repeat intro. apply (|X X0|).
  Defined.
  Instance object_cheight : cheightable context object := _.
  Instance equality_cheight : cheightable context equality.
  constructor. repeat intro. destruct X0. 
  apply (max (cheight X o) (cheight X o0)).
  Defined.
  Instance equation_cheight : cheightable context equation.
  constructor. repeat intro. destruct X0 as [[? ?] ?].
  apply (max (cheight X o) (max (cheight X o0)(cheight X o1))).
  Defined.

  Instance ses_cheight : cheightable context sat_equation_system.
  constructor. intros ctx ses.
  destruct ses as [a b c].
  apply (max (cheight ctx a) (max (cheight ctx b) (cheight ctx c))).
  Defined.

  Instance ies_cheight : cheightable context impl_equation_system.
  constructor. intros ctx ies.
  destruct ies as [a b c d].
  apply (max (cheight ctx b) (max (cheight ctx c) (cheight ctx d))).
  Defined.

  Instance is_cheight : cheightable context impl_system.
  constructor. intros ctx is.
  destruct is as [es1 es2].
  apply (max (cheight ctx es1) (cheight ctx es2)).
  Defined.

  (*VARSABLE*)

  Instance object_vars : varsable object var := _.
  Instance equality_vars : varsable equality var.
  constructor. repeat intro. destruct X.
  apply ((vars o)++(vars o0)).
  Defined.
  Instance equation_vars : varsable equation var.
  constructor. repeat intro. destruct X as [[? ?] ?].
  apply ((vars o)++(vars o0)++(vars o1)).
  Defined.
  
  Instance ses_vars : varsable sat_equation_system var.
  constructor. repeat intro.
  destruct X as [a b c].
  apply (a++(vars b)++(vars c)).
  Defined.
  
  Instance ies_vars : varsable impl_equation_system var.
  constructor. repeat intro.
  destruct X as [a b c d].
  apply (a++b++(vars c)++(vars d)).
  Defined.

  Instance is_vars : varsable impl_system var.
  constructor. repeat intro.
  destruct X as [es1 es2].
  apply ((vars es1)++(vars es2)).
  Defined.

 (*For convenience*)
 Definition vheight := fun (v : var) => 0.
 Lemma vheight_zero: is_height_zero_spec vheight.
 Proof. repeat intro. left. trivial. Qed.
 Instance height_var : heightable var := Heightable vheight vheight_zero.
 Instance varsable_var: varsable var var.
 constructor. intro. apply (X::nil). Defined.

 Lemma vars_var_list: forall (l : list var),
  vars l = l.
 Proof with try tauto.
  induction l...
  simpl in *. rewrite IHl...
 Qed.

 Lemma height_rewrite : forall {A} `{heightable A} (a : A) l,
 |a::l| = max (|a|) (|l|).
 Proof. tauto. Qed.
 Lemma cheight_rewrite : forall (l : list var) v ctx,
  cheight ctx (v::l) = max (cheight ctx v) (cheight ctx l).
 Proof. tauto. Qed.
 Lemma cheight_lt_rewrite: forall ctx l h,
  cheight ctx l < S h <-> forall v, In v l -> |ctx v| < S h.
 Proof with try tauto;try omega.
  induction l;intros.
  split;intros. inv H0. compute...
  rewrite cheight_rewrite.
  rewrite Nat.max_lub_lt_iff.
  split;intros.
  destruct H. destruct H0. subst. apply H.
  rewrite IHl in H1. apply H1...
  split. apply H. left...
  apply IHl. intros. apply H. right...
 Qed.  
 Lemma cheight_leq_rewrite: forall ctx l h,
  (cheight ctx l <= h)%nat <-> forall v, In v l -> (|ctx v| <= h)%nat.
 Proof with try tauto;try omega.
  induction l;intros.
  split;intros. inv H0. compute...
  rewrite cheight_rewrite.
  rewrite Nat.max_lub_iff.
  split;intros.
  destruct H. destruct H0. subst. apply H.
  rewrite IHl in H1. apply H1...
  split. apply H. left...
  apply IHl. intros. apply H. right...
 Qed. 
 Lemma cheight_sublist: forall ctx (l l' : list var),
  sublist l l' ->
  (cheight ctx l <= cheight ctx l')%nat.
 Proof with try tauto.
  induction l;intros.
  compute. omega.
  replace (a::l) with ((a::nil)++l) in H by tauto.
  rewrite sublist_app_iff in H.
  destruct H.
  spec IHl l' H0.
  rewrite cheight_rewrite.
  rewrite Nat.max_lub_iff.
  split...
  spec H a. detach H.
  revert H. revert a. clear.
  induction l';intros. inv H...
  rewrite cheight_rewrite.
  rewrite Nat.max_le_iff.
  destruct H;subst. left. omega.
  right. apply IHl'...
  left...
 Qed.
 (*End convenience*)

 Definition replace_snzvars := fun (ses : sat_equation_system) (l : list var) =>
  Sat_equation_system l (sat_equalities ses) (sat_equations ses).
 Definition replace_inzvars := fun (ies : impl_equation_system) (l : list var) =>
  Impl_equation_system (impl_exvars ies) l (impl_equalities ies) (impl_equations ies).
 Definition replace_isnzvars (is : impl_system) (l1 l2 : list var) : impl_system :=
  let (ies1,ies2) := is in
  (replace_inzvars ies1 l1, replace_inzvars ies2 l2).

  Definition nSAT (ses : sat_equation_system) : Prop :=
   SAT (replace_snzvars ses nil).
  Definition sSAT (ses : sat_equation_system) x : Prop :=
   SAT (replace_snzvars ses (x::nil)).
  Definition sIMPL (is : impl_system) (x y : var): Prop :=
   IMPL (replace_isnzvars is (x::nil) (y::nil)).
  Definition zIMPL (is : impl_system) (x : var): Prop :=
   IMPL (replace_isnzvars is nil (x::nil)).
  Definition nIMPL (is : impl_system) : Prop :=
   IMPL (replace_isnzvars is nil nil).

 Lemma replace_snzvars_nil_eval : forall ses ctx,
  ctx |= ses <-> ctx |= (replace_snzvars ses nil) /\ ctx |= (sat_nzvars ses).
 Proof with try tauto.
  intros.
  destruct ses as [l1 l2 l3].
  unfold replace_snzvars. simpl.
  unfold eval_sat_equation_system. simpl...
 Qed.

 Lemma replace_snzvars_correct : forall ses l,
  sat_nzvars (replace_snzvars ses l) = l.
 Proof.
  repeat intros.
  destruct ses as [l1 l2 l3].
  unfold replace_snzvars. simpl. auto.
 Qed.

 Lemma replace_snzvars_height: forall ses l,
  |replace_snzvars ses l| = |ses|.
 Proof.
  intros.
  destruct ses as [l1 l2 l3].
  simpl. unfold ses_h. simpl. auto.
 Qed.

 Lemma replace_snzvars_id: forall ses l,
  sat_nzvars ses = l ->
  replace_snzvars ses l = ses.
 Proof.
  intros.
  destruct ses as [l1 l2 l3].
  unfold replace_snzvars. simpl. simpl in H.
  congruence.
 Qed.

 Lemma replace_snzvars_reduce: forall ses l1 l2,
  replace_snzvars (replace_snzvars ses l1) l2 = replace_snzvars ses l2.
 Proof.
  intros.
  destruct ses as [l3 l4 l5].
  unfold replace_snzvars;simpl. auto.
 Qed.

 Lemma ies2ses_nzvars: forall ies,
  impl_nzvars ies = sat_nzvars (ies2ses ies).
 Proof. tauto. Qed.

 Lemma replace_inzvars_nil_eval: forall ies ctx,
  ctx |= ies <-> 
  exists ctx', [impl_exvars ies => ctx'] ctx |= replace_snzvars (ies2ses ies) nil /\
  [impl_exvars ies => ctx'] ctx |= impl_nzvars ies.
 Proof with try tauto.
  intros;split;intros.
  destruct H as [ctx' H].
  exists ctx'. apply replace_snzvars_nil_eval...
  destruct H as [ctx' H].
  exists ctx'. apply replace_snzvars_nil_eval...
 Qed.

 Lemma replace_inzvars_reduce: forall ies l l',
  replace_inzvars (replace_inzvars ies l) l' = replace_inzvars ies l'.
 Proof. intros;tauto. Qed.

 Lemma fst_replace_isnzvars: forall is l1 l2,
  fst (replace_isnzvars is l1 l2) = replace_inzvars (fst is) l1.
 Proof.
  intros.
  destruct is as [ies1 ies2].
  unfold replace_isnzvars. trivial.
 Qed.
 Lemma snd_replace_isnzvars: forall is l1 l2,
  snd (replace_isnzvars is l1 l2) = replace_inzvars (snd is) l2.
 Proof.
  intros. unfold replace_isnzvars.
  destruct is as [ies1 ies2]. trivial.
 Qed.

 Lemma replace_inzvars_id: forall ies,
  replace_inzvars ies (impl_nzvars ies) = ies.
 Proof.
  intros. 
  destruct ies as [l1 l2 l3 l4].
  unfold replace_inzvars. trivial.
 Qed.

 Lemma replace_inzvars_correct: forall ies l,
  impl_nzvars (replace_inzvars ies l) = l.
 Proof. intros. tauto. Qed.

 Lemma replace_inzvars_exvars: forall ies l,
  impl_exvars (replace_inzvars ies l) = impl_exvars ies.
 Proof. intros. tauto. Qed.

 Lemma replace_inzvars_ies2ses: forall ies l,
  ies2ses (replace_inzvars ies l) = replace_snzvars (ies2ses ies) l.
 Proof. intros. tauto. Qed.

 Lemma vars_replace_isnzvars: forall is l1 l2,
  vars (replace_isnzvars is l1 l2) = 
  vars (replace_inzvars (fst is) l1) ++ vars (replace_inzvars (snd is) l2).
 Proof.
  intros. destruct is as [ies1 ies2]. trivial.
 Qed.

 Lemma replace_isnzvars_eval: forall ctx is l1 l2,
  ctx |= replace_isnzvars is l1 l2 <->
  (ctx |= replace_inzvars (fst is) l1 -> ctx |= replace_inzvars (snd is) l2).
 Proof.
  intros. 
  destruct is as [ies1 ies2].
  unfold replace_isnzvars. simpl.
  unfold eval_impl_system. tauto.
 Qed.

 Lemma replace_isnzvars_reduce: forall is l1 l2 l3 l4,
  replace_isnzvars (replace_isnzvars is l1 l2) l3 l4 = replace_isnzvars is l3 l4.
 Proof.
  intros. destruct is as [ies1 ies2].
  unfold replace_isnzvars.
  repeat rewrite replace_inzvars_reduce. trivial.
 Qed.

 Lemma replace_inzvars_height: forall ies l,
  |replace_inzvars ies l| = |ies|.
 Proof. intros. tauto. Qed.

 Lemma replace_isnzvars_height: forall is l l',
  |replace_isnzvars is l l'| = |is|.
 Proof.
  intros.
  destruct is as [? ?]. simpl.
  unfold is_h;simpl.
  repeat rewrite replace_inzvars_height. auto.
 Qed.

 Lemma replace_inzvars_eval_nil: forall rho ies l,
  rho |= replace_inzvars ies l ->
  rho |= replace_inzvars ies nil.
 Proof with try tauto.
  intros.
  destruct H as [rho' H].
  exists rho'.
  rewrite replace_inzvars_ies2ses,replace_inzvars_exvars in *.
  rewrite replace_snzvars_nil_eval in H...
 Qed.

End SYSTEM_FEATURES.

Module System_Features (sv : SV ) (Import es : EQUATION_SYSTEM sv) <: 
       SYSTEM_FEATURES sv es.

  (*HEIGHT*)

  Instance object_height : heightable object := _.
  Definition equality_h := fun (eql : equality) => 
   let (o1,o2) := eql in max (|o1|) (|o2|).
  Definition equality_h_zero: is_height_zero_spec equality_h.
  Proof with tauto.
  repeat intro.
  destruct a. simpl.
  destruct (is_height_zero o).
  destruct (is_height_zero o0).
  left. rewrite max_zero...
  right. rewrite max_zero...
  right. rewrite max_zero...
  Defined.
  Instance equality_height : heightable equality :=
   Heightable equality_h equality_h_zero.
  Definition equation_h := fun (eqn : equation) => 
   match eqn with (o1,o2,o3) => max (max (|o1|)(|o2|)) (|o3|)  end.
  Definition equation_h_zero: is_height_zero_spec equation_h.
  Proof with tauto.
  repeat intro.
  destruct a as [[? ?] ?]. simpl.
  destruct (is_height_zero o).
  destruct (is_height_zero o0).
  destruct (is_height_zero o1).
  left. repeat rewrite max_zero...
  right. repeat rewrite max_zero...
  right. repeat rewrite max_zero...
  right. repeat rewrite max_zero...
  Defined.
  Instance equation_height : heightable equation :=
   Heightable equation_h equation_h_zero.
  
  Definition ses_h := fun (ses : sat_equation_system) =>
   max (|sat_equalities ses|) (|sat_equations ses|).
  Definition ses_h_zero: is_height_zero_spec ses_h.
  Proof with tauto.
  repeat intro.
  destruct a as [l1 l2 l3].
  unfold ses_h;simpl.
  destruct (is_height_zero l2).
  destruct (is_height_zero l3).
  left. simpl in e,e0. rewrite e,e0...
  right. intro. apply n.
  rewrite max_zero in H...
  right. intro. apply n.
  rewrite max_zero in H...
  Defined.
  Instance ses_height : heightable sat_equation_system :=
  Heightable ses_h ses_h_zero.
  Definition ies_h := fun (ies : impl_equation_system) =>
   max (|impl_equalities ies|) (|impl_equations ies|).
  Definition ies_h_zero: is_height_zero_spec ies_h.
  Proof with tauto.
  repeat intro.
  destruct a as [l1 l2 l3 l4].
  unfold ies_h;simpl.
  destruct (is_height_zero l3); try simpl in e.
  destruct (is_height_zero l4); try simpl in e0.
  left. rewrite e;rewrite e0...
  right. rewrite max_zero...
  right. rewrite max_zero...
  Defined.
  Instance ies_height : heightable impl_equation_system :=
  Heightable ies_h ies_h_zero.
  Definition is_h := fun (is :impl_system) => max (|fst is|)(|snd is|).
  Definition is_h_zero: is_height_zero_spec is_h.
  Proof with tauto.
  repeat intro.
  destruct a as [es1 es2].
  unfold is_h.
  destruct (is_height_zero es1).
  destruct (is_height_zero es2).
  left. rewrite max_zero...
  right. rewrite max_zero...
  right. rewrite max_zero...
  Defined.
  Instance is_height : heightable impl_system :=
  Heightable is_h is_h_zero.

  (*CHEIGHT*)

  Instance var_cheight : cheightable context var.
  constructor. repeat intro. apply (|X X0|).
  Defined.
  Instance object_cheight : cheightable context object := _.
  Instance equality_cheight : cheightable context equality.
  constructor. repeat intro. destruct X0. 
  apply (max (cheight X o) (cheight X o0)).
  Defined.
  Instance equation_cheight : cheightable context equation.
  constructor. repeat intro. destruct X0 as [[? ?] ?].
  apply (max (cheight X o) (max (cheight X o0)(cheight X o1))).
  Defined.

  Instance ses_cheight : cheightable context sat_equation_system.
  constructor. intros ctx ses.
  destruct ses as [a b c].
  apply (max (cheight ctx a) (max (cheight ctx b) (cheight ctx c))).
  Defined.

  Instance ies_cheight : cheightable context impl_equation_system.
  constructor. intros ctx ies.
  destruct ies as [a b c d].
  apply (max (cheight ctx b) (max (cheight ctx c) (cheight ctx d))).
  Defined.

  Instance is_cheight : cheightable context impl_system.
  constructor. intros ctx is.
  destruct is as [es1 es2].
  apply (max (cheight ctx es1) (cheight ctx es2)).
  Defined.

  (*VARSABLE*)

  Instance object_vars : varsable object var := _.
  Instance equality_vars : varsable equality var.
  constructor. repeat intro. destruct X.
  apply ((vars o)++(vars o0)).
  Defined.
  Instance equation_vars : varsable equation var.
  constructor. repeat intro. destruct X as [[? ?] ?].
  apply ((vars o)++(vars o0)++(vars o1)).
  Defined.
  
  Instance ses_vars : varsable sat_equation_system var.
  constructor. repeat intro.
  destruct X as [a b c].
  apply (a++(vars b)++(vars c)).
  Defined.
  
  Instance ies_vars : varsable impl_equation_system var.
  constructor. repeat intro.
  destruct X as [a b c d].
  apply (a++b++(vars c)++(vars d)).
  Defined.

  Instance is_vars : varsable impl_system var.
  constructor. repeat intro.
  destruct X as [es1 es2].
  apply ((vars es1)++(vars es2)).
  Defined.

 (*For convenience*)
 Definition vheight := fun (v : var) => 0.
 Lemma vheight_zero: is_height_zero_spec vheight.
 Proof. repeat intro. left. trivial. Qed.
 Instance height_var : heightable var := Heightable vheight vheight_zero.
 Instance varsable_var: varsable var var.
 constructor. intro. apply (X::nil). Defined.

 Lemma vars_var_list: forall (l : list var),
  vars l = l.
 Proof with try tauto.
  induction l...
  simpl in *. rewrite IHl...
 Qed.

 Lemma height_rewrite : forall {A} `{heightable A} (a : A) l,
 |a::l| = max (|a|) (|l|).
 Proof. tauto. Qed.
 Lemma cheight_rewrite : forall (l : list var) v ctx,
  cheight ctx (v::l) = max (cheight ctx v) (cheight ctx l).
 Proof. tauto. Qed.
 Lemma cheight_lt_rewrite: forall ctx l h,
  cheight ctx l < S h <-> forall v, In v l -> |ctx v| < S h.
 Proof with try tauto;try omega.
  induction l;intros.
  split;intros. inv H0. compute...
  rewrite cheight_rewrite.
  rewrite Nat.max_lub_lt_iff.
  split;intros.
  destruct H. destruct H0. subst. apply H.
  rewrite IHl in H1. apply H1...
  split. apply H. left...
  apply IHl. intros. apply H. right...
 Qed.  
 Lemma cheight_leq_rewrite: forall ctx l h,
  (cheight ctx l <= h)%nat <-> forall v, In v l -> (|ctx v| <= h)%nat.
 Proof with try tauto;try omega.
  induction l;intros.
  split;intros. inv H0. compute...
  rewrite cheight_rewrite.
  rewrite Nat.max_lub_iff.
  split;intros.
  destruct H. destruct H0. subst. apply H.
  rewrite IHl in H1. apply H1...
  split. apply H. left...
  apply IHl. intros. apply H. right...
 Qed. 
 Lemma cheight_sublist: forall ctx (l l' : list var),
  sublist l l' ->
  (cheight ctx l <= cheight ctx l')%nat.
 Proof with try tauto.
  induction l;intros.
  compute. omega.
  replace (a::l) with ((a::nil)++l) in H by tauto.
  rewrite sublist_app_iff in H.
  destruct H.
  spec IHl l' H0.
  rewrite cheight_rewrite.
  rewrite Nat.max_lub_iff.
  split...
  spec H a. detach H.
  revert H. revert a. clear.
  induction l';intros. inv H...
  rewrite cheight_rewrite.
  rewrite Nat.max_le_iff.
  destruct H;subst. left. omega.
  right. apply IHl'...
  left...
 Qed.
 (*End convenience*)

 Definition replace_snzvars := fun (ses : sat_equation_system) (l : list var) =>
  Sat_equation_system l (sat_equalities ses) (sat_equations ses).
 Definition replace_inzvars := fun (ies : impl_equation_system) (l : list var) =>
  Impl_equation_system (impl_exvars ies) l (impl_equalities ies) (impl_equations ies).
 Definition replace_isnzvars (is : impl_system) (l1 l2 : list var) : impl_system :=
  let (ies1,ies2) := is in
  (replace_inzvars ies1 l1, replace_inzvars ies2 l2).

  Definition nSAT (ses : sat_equation_system) : Prop :=
   SAT (replace_snzvars ses nil).
  Definition sSAT (ses : sat_equation_system) x : Prop :=
   SAT (replace_snzvars ses (x::nil)).
  Definition sIMPL (is : impl_system) (x y : var): Prop :=
   IMPL (replace_isnzvars is (x::nil) (y::nil)).
  Definition zIMPL (is : impl_system) (x : var): Prop :=
   IMPL (replace_isnzvars is nil (x::nil)).
  Definition nIMPL (is : impl_system) : Prop :=
   IMPL (replace_isnzvars is nil nil).

 Lemma replace_snzvars_nil_eval : forall ses ctx,
  ctx |= ses <-> ctx |= (replace_snzvars ses nil) /\ ctx |= (sat_nzvars ses).
 Proof with try tauto.
  intros.
  destruct ses as [l1 l2 l3].
  unfold replace_snzvars. simpl.
  unfold eval_sat_equation_system. simpl...
 Qed.

 Lemma replace_snzvars_correct : forall ses l,
  sat_nzvars (replace_snzvars ses l) = l.
 Proof.
  repeat intros.
  destruct ses as [l1 l2 l3].
  unfold replace_snzvars. simpl. auto.
 Qed.

 Lemma replace_snzvars_height: forall ses l,
  |replace_snzvars ses l| = |ses|.
 Proof.
  intros.
  destruct ses as [l1 l2 l3].
  simpl. unfold ses_h. simpl. auto.
 Qed.

 Lemma replace_snzvars_id: forall ses l,
  sat_nzvars ses = l ->
  replace_snzvars ses l = ses.
 Proof.
  intros.
  destruct ses as [l1 l2 l3].
  unfold replace_snzvars. simpl. simpl in H.
  congruence.
 Qed.

 Lemma replace_snzvars_reduce: forall ses l1 l2,
  replace_snzvars (replace_snzvars ses l1) l2 = replace_snzvars ses l2.
 Proof.
  intros.
  destruct ses as [l3 l4 l5].
  unfold replace_snzvars;simpl. auto.
 Qed.

 Lemma ies2ses_nzvars: forall ies,
  impl_nzvars ies = sat_nzvars (ies2ses ies).
 Proof. tauto. Qed.

 Lemma replace_inzvars_nil_eval: forall ies ctx,
  ctx |= ies <-> 
  exists ctx', [impl_exvars ies => ctx'] ctx |= replace_snzvars (ies2ses ies) nil /\
  [impl_exvars ies => ctx'] ctx |= impl_nzvars ies.
 Proof with try tauto.
  intros;split;intros.
  destruct H as [ctx' H].
  exists ctx'. apply replace_snzvars_nil_eval...
  destruct H as [ctx' H].
  exists ctx'. apply replace_snzvars_nil_eval...
 Qed.

 Lemma replace_inzvars_reduce: forall ies l l',
  replace_inzvars (replace_inzvars ies l) l' = replace_inzvars ies l'.
 Proof. intros;tauto. Qed.

 Lemma fst_replace_isnzvars: forall is l1 l2,
  fst (replace_isnzvars is l1 l2) = replace_inzvars (fst is) l1.
 Proof.
  intros.
  destruct is as [ies1 ies2].
  unfold replace_isnzvars. trivial.
 Qed.
 Lemma snd_replace_isnzvars: forall is l1 l2,
  snd (replace_isnzvars is l1 l2) = replace_inzvars (snd is) l2.
 Proof.
  intros. unfold replace_isnzvars.
  destruct is as [ies1 ies2]. trivial.
 Qed.

 Lemma replace_inzvars_id: forall ies,
  replace_inzvars ies (impl_nzvars ies) = ies.
 Proof.
  intros. 
  destruct ies as [l1 l2 l3 l4].
  unfold replace_inzvars. trivial.
 Qed.

 Lemma replace_inzvars_correct: forall ies l,
  impl_nzvars (replace_inzvars ies l) = l.
 Proof. intros. tauto. Qed.

 Lemma replace_inzvars_exvars: forall ies l,
  impl_exvars (replace_inzvars ies l) = impl_exvars ies.
 Proof. intros. tauto. Qed.

 Lemma replace_inzvars_ies2ses: forall ies l,
  ies2ses (replace_inzvars ies l) = replace_snzvars (ies2ses ies) l.
 Proof. intros. tauto. Qed.

 Lemma vars_replace_isnzvars: forall is l1 l2,
  vars (replace_isnzvars is l1 l2) = 
  vars (replace_inzvars (fst is) l1) ++ vars (replace_inzvars (snd is) l2).
 Proof.
  intros. destruct is as [ies1 ies2]. trivial.
 Qed.

 Lemma replace_isnzvars_eval: forall ctx is l1 l2,
  ctx |= replace_isnzvars is l1 l2 <->
  (ctx |= replace_inzvars (fst is) l1 -> ctx |= replace_inzvars (snd is) l2).
 Proof.
  intros. 
  destruct is as [ies1 ies2].
  unfold replace_isnzvars. simpl.
  unfold eval_impl_system. tauto.
 Qed.

 Lemma replace_isnzvars_reduce: forall is l1 l2 l3 l4,
  replace_isnzvars (replace_isnzvars is l1 l2) l3 l4 = replace_isnzvars is l3 l4.
 Proof.
  intros. destruct is as [ies1 ies2].
  unfold replace_isnzvars.
  repeat rewrite replace_inzvars_reduce. trivial.
 Qed.

 Lemma replace_inzvars_height: forall ies l,
  |replace_inzvars ies l| = |ies|.
 Proof. intros. tauto. Qed.

 Lemma replace_isnzvars_height: forall is l l',
  |replace_isnzvars is l l'| = |is|.
 Proof.
  intros.
  destruct is as [? ?]. simpl.
  unfold is_h;simpl.
  repeat rewrite replace_inzvars_height. auto.
 Qed.

 Lemma replace_inzvars_eval_nil: forall rho ies l,
  rho |= replace_inzvars ies l ->
  rho |= replace_inzvars ies nil.
 Proof with try tauto.
  intros.
  destruct H as [rho' H].
  exists rho'.
  rewrite replace_inzvars_ies2ses,replace_inzvars_exvars in *.
  rewrite replace_snzvars_nil_eval in H...
 Qed.

End System_Features.

(*
  (*EVAL*)
  Definition context := var -> s.
  Instance object_get : getable context object s := _ .
  Instance eval_equality : evalable context equality.
  constructor. repeat intro.
  destruct X0.
  apply (get X o = get X o0).
  Defined.
  Instance eval_equation : evalable context equation.
  constructor. repeat intro.
  destruct X0 as [[? ?] ?]. apply (join (get X o) (get X o0) (get X o1)).
  Defined.
  Instance eval_nzvars : evalable context var.
  constructor. repeat intro.
  apply (X X0 <> bot).
  Defined.

  Definition eval_sat_equation_system (ctx : context) (ses : sat_equation_system) : Prop :=
    ctx |= (sat_equalities ses) /\ 
    ctx |= (sat_equations ses) /\
    ctx |= (sat_nzvars ses).
  Instance evalable_sat_equation_system : evalable context sat_equation_system :=
    Evalable eval_sat_equation_system.

  Definition ies2ses := 
  fun (ies : impl_equation_system) => 
  Sat_equation_system (impl_nzvars ies) (impl_equalities ies) (impl_equations ies).

  Definition eval_impl_equation_system (ctx : context) (ies : impl_equation_system) : Prop:=
   e_eval ctx (impl_exvars ies) (ies2ses ies).
  Instance evalable_impl_equation_system : evalable context impl_equation_system :=
   Evalable eval_impl_equation_system.
 
  Definition eval_impl_system (ctx : context) (is : impl_system) : Prop :=
   ctx |= (fst is) -> ctx |= (snd is).
  Instance evalable_impl_system : evalable context impl_system :=
   Evalable eval_impl_system.

  (*HEIGHT*)

  Instance object_height : heightable object := _.
  Definition equality_h := fun (eql : equality) => 
   let (o1,o2) := eql in max (|o1|) (|o2|).
  Axiom equality_h_zero: is_height_zero_spec equality_h.
  Instance equality_height : heightable equality :=
   Heightable equality_h equality_h_zero.
  Definition equation_h := fun (eqn : equation) => 
   match eqn with (o1,o2,o3) => max (max (|o1|)(|o2|)) (|o3|) end.
  Axiom equation_h_zero: is_height_zero_spec equation_h.
  Instance equation_height : heightable equation :=
   Heightable equation_h equation_h_zero.
  Definition ses_h := fun (ses : sat_equation_system) =>
   max (|sat_equalities ses|) (|sat_equations ses|).
  Axiom ses_h_zero: is_height_zero_spec ses_h.
  Instance ses_height : heightable sat_equation_system :=
  Heightable ses_h ses_h_zero.
  Definition ies_h := fun (ies : impl_equation_system) =>
   max (|impl_equalities ies|) (|impl_equations ies|).
  Axiom ies_h_zero: is_height_zero_spec ies_h.
  Instance ies_height : heightable impl_equation_system :=
  Heightable ies_h ies_h_zero.
  Definition is_h := fun (is :impl_system) => max (|fst is|)(|snd is|).
  Axiom is_h_zero: is_height_zero_spec is_h.
  Instance is_height : heightable impl_system :=
  Heightable is_h is_h_zero.

  (*CHEIGHT*)
  Instance var_cheight : cheightable context var.
  constructor. repeat intro. apply (|X X0|).
  Defined.
  Instance object_cheight : cheightable context object := _.
  Instance equality_cheight : cheightable context equality.
  constructor. repeat intro. destruct X0. 
  apply (max (cheight X o) (cheight X o0)).
  Defined.
  Instance equation_cheight : cheightable context equation.
  constructor. repeat intro. destruct X0 as [[? ?] ?].
  apply (max (cheight X o) (max (cheight X o0)(cheight X o1))).
  Defined.

  Instance ses_cheight : cheightable context sat_equation_system.
  constructor. intros ctx ses.
  destruct ses as [a b c].
  apply (max (cheight ctx a) (max (cheight ctx b) (cheight ctx c))).
  Defined.

  Instance ies_cheight : cheightable context impl_equation_system.
  constructor. intros ctx ies.
  destruct ies as [a b c d].
  apply (max (cheight ctx b) (max (cheight ctx c) (cheight ctx d))).
  Defined.

  Instance is_cheight : cheightable context impl_system.
  constructor. intros ctx is.
  destruct is as [es1 es2].
  apply (max (cheight ctx es1) (cheight ctx es2)).
  Defined.

  (*VARSABLE*)
  Instance object_vars : varsable object var := _.
  Instance equality_vars : varsable equality var.
  constructor. repeat intro. destruct X.
  apply ((vars o)++(vars o0)).
  Defined.
  Instance equation_vars : varsable equation var.
  constructor. repeat intro. destruct X as [[? ?] ?].
  apply ((vars o)++(vars o0)++(vars o1)).
  Defined.
  
  Instance ses_vars : varsable sat_equation_system var.
  constructor. repeat intro.
  destruct X as [a b c].
  apply (a++(vars b)++(vars c)).
  Defined.
  
  Instance ies_vars : varsable impl_equation_system var.
  constructor. repeat intro.
  destruct X as [a b c d].
  apply (a++b++(vars c)++(vars d)).
  Defined.

  Instance is_vars : varsable impl_system var.
  constructor. repeat intro.
  destruct X as [es1 es2].
  apply ((vars es1)++(vars es2)).
  Defined.

 (*For convenience*)
 Definition vheight := fun (v : var) => 0.
 Axiom vheight_zero: is_height_zero_spec vheight.
 Instance height_var : heightable var := Heightable vheight vheight_zero.
 Instance varsable_var: varsable var var.
 constructor. intro. apply (X::nil). Defined.
 Axiom vars_var_list: forall (l : list var),
  vars l = l.
 Axiom height_rewrite : forall {A} `{heightable A} (a : A) l,
 |a::l| = max (|a|) (|l|).
 Axiom cheight_rewrite : forall (l : list var) v ctx,
  cheight ctx (v::l) = max (cheight ctx v) (cheight ctx l).
 Axiom cheight_lt_rewrite: forall ctx l h,
  cheight ctx l < S h <-> forall v, In v l -> |ctx v| < S h.
 Axiom cheight_leq_rewrite: forall ctx l h,
  (cheight ctx l <= h)%nat <-> forall v, In v l -> (|ctx v| <= h)%nat.
 Axiom cheight_sublist: forall ctx (l l' : list var),
  sublist l l' ->
  (cheight ctx l <= cheight ctx l')%nat.
 (*End convenience*)

 Definition replace_snzvars := fun (ses : sat_equation_system) (l : list var) =>
  Sat_equation_system l (sat_equalities ses) (sat_equations ses).
 Definition replace_inzvars := fun (ies : impl_equation_system) (l : list var) =>
  Impl_equation_system (impl_exvars ies) l (impl_equalities ies) (impl_equations ies).
 Definition replace_isnzvars (is : impl_system) (l1 l2 : list var) : impl_system :=
  let (ies1,ies2) := is in
  (replace_inzvars ies1 l1, replace_inzvars ies2 l2).

  Definition SAT {A B} `{evalable A B} := 
   fun (b : B) => exists (a : A), a |= b.
  Definition IMPL {A B} `{evalable A B} :=
   fun (b : B) => forall a, a |= b.
  Definition nSAT (ses : sat_equation_system) : Prop :=
   SAT (replace_snzvars ses nil).
  Definition sSAT (ses : sat_equation_system) x : Prop :=
   SAT (replace_snzvars ses (x::nil)).
  Definition sIMPL (is : impl_system) (x y : var): Prop :=
   IMPL (replace_isnzvars is (x::nil) (y::nil)).
  Definition zIMPL (is : impl_system) (x : var): Prop :=
   IMPL (replace_isnzvars is nil (x::nil)).
  Definition nIMPL (is : impl_system) : Prop :=
   IMPL (replace_isnzvars is nil nil).

  Axiom replace_snzvars_nil_eval : forall ses ctx,
   ctx |= ses <-> ctx |= (replace_snzvars ses nil) /\ ctx |= (sat_nzvars ses).
  Axiom replace_snzvars_correct : forall ses l,
   sat_nzvars (replace_snzvars ses l) = l.
  Axiom replace_snzvars_height: forall ses l,
  |replace_snzvars ses l| = |ses|.
  Axiom replace_snzvars_id: forall ses l,
  sat_nzvars ses = l ->
  replace_snzvars ses l = ses.
  Axiom replace_snzvars_reduce: forall ses l1 l2,
  replace_snzvars (replace_snzvars ses l1) l2 = replace_snzvars ses l2.
  Axiom ies2ses_nzvars: forall ies,
  impl_nzvars ies = sat_nzvars (ies2ses ies).
  Axiom replace_inzvars_nil_eval: forall ies ctx,
  ctx |= ies <-> 
  exists ctx', [impl_exvars ies => ctx'] ctx |= replace_snzvars (ies2ses ies) nil /\
  [impl_exvars ies => ctx'] ctx |= impl_nzvars ies.
  Axiom replace_inzvars_reduce: forall ies l l',
  replace_inzvars (replace_inzvars ies l) l' = replace_inzvars ies l'.
  Axiom fst_replace_isnzvars: forall is l1 l2,
  fst (replace_isnzvars is l1 l2) = replace_inzvars (fst is) l1.
  Axiom snd_replace_isnzvars: forall is l1 l2,
  snd (replace_isnzvars is l1 l2) = replace_inzvars (snd is) l2.
  Axiom replace_inzvars_id: forall ies,
  replace_inzvars ies (impl_nzvars ies) = ies.
  Axiom replace_inzvars_correct: forall ies l,
  impl_nzvars (replace_inzvars ies l) = l.
  Axiom replace_inzvars_exvars: forall ies l,
  impl_exvars (replace_inzvars ies l) = impl_exvars ies.
  Axiom replace_inzvars_ies2ses: forall ies l,
  ies2ses (replace_inzvars ies l) = replace_snzvars (ies2ses ies) l.
  Axiom vars_replace_isnzvars: forall is l1 l2,
  vars (replace_isnzvars is l1 l2) = 
  vars (replace_inzvars (fst is) l1) ++ vars (replace_inzvars (snd is) l2).
  Axiom replace_isnzvars_eval: forall ctx is l1 l2,
  ctx |= replace_isnzvars is l1 l2 <->
  (ctx |= replace_inzvars (fst is) l1 -> ctx |= replace_inzvars (snd is) l2).
  Axiom replace_isnzvars_reduce: forall is l1 l2 l3 l4,
  replace_isnzvars (replace_isnzvars is l1 l2) l3 l4 = replace_isnzvars is l3 l4.
  Axiom replace_inzvars_height: forall ies l,
  |replace_inzvars ies l| = |ies|.
  Axiom replace_isnzvars_height: forall is l l',
  |replace_isnzvars is l l'| = |is|.
  Axiom replace_inzvars_eval_nil: forall rho ies l,
  rho |= replace_inzvars ies l ->
  rho |= replace_inzvars ies nil.
  
 End ES_FEATURES.

Module Share_equation_system (Import sv : SV) <: EQUATION_SYSTEM sv with Definition s := share.

  Definition s := share.
  Instance s_eq_dec : EqDec s := _.
  Definition var := t.
  Instance var_eq_dec : EqDec var := _.
  Definition object := @objectT var s.
  Definition equality := (object * object)%type.
  Instance equality_eq_dec : EqDec equality.
  Proof with congruence.
  repeat intro.
  destruct a;destruct a'.
  destruct (eq_dec o o1). subst.
  destruct (eq_dec o0 o2). subst.
  left... right... right...
  Defined.
  Definition equation := (object * object * object)%type.
  Instance equation_eq_dec : EqDec equation.
  Proof with congruence.
  repeat intro.
  destruct a as [[? ?] ?];destruct a' as [[? ?] ?].
  destruct (eq_dec o o2).
  destruct (eq_dec o0 o3).
  destruct (eq_dec o1 o4).
  left... right... right... right...
  Defined.

  Record sat_equation_system : Type := Sat_equation_system {
    sat_nzvars        : list var;
    sat_equalities    : list equality;
    sat_equations     : list equation
  }.
  Record impl_equation_system : Type := Impl_equation_system {
    impl_exvars     : list var;
    impl_nzvars     : list var;
    impl_equalities : list equality;
    impl_equations  : list equation
  }.
  Definition impl_system : Type := (impl_equation_system * impl_equation_system)%type.

End Share_equation_system.

Module Bool_equation_system (Import sv : SV) <: EQUATION_SYSTEM sv with Definition s := bool.

  Definition s := bool.
  Instance s_eq_dec : EqDec s := bool_dec.
  Definition var := t.
  Instance var_eq_dec : EqDec var := _.
  Definition object := @objectT var s.
  Definition equality := (object * object)%type.
  Instance equality_eq_dec : EqDec equality.
  Proof with congruence.
  repeat intro.
  destruct a;destruct a'.
  destruct (eq_dec o o1). subst.
  destruct (eq_dec o0 o2). subst.
  left... right... right...
  Defined.
  Definition equation := (object * object * object)%type.
  Instance equation_eq_dec : EqDec equation.
  Proof with congruence.
  repeat intro.
  destruct a as [[? ?] ?];destruct a' as [[? ?] ?].
  destruct (eq_dec o o2).
  destruct (eq_dec o0 o3).
  destruct (eq_dec o1 o4).
  left... right... right... right...
  Defined.

  Record sat_equation_system : Type := Sat_equation_system {
    sat_nzvars        : list var;
    sat_equalities    : list equality;
    sat_equations     : list equation
  }.
  Record impl_equation_system : Type := Impl_equation_system {
    impl_exvars     : list var;
    impl_nzvars     : list var;
    impl_equalities : list equality;
    impl_equations  : list equation
  }.
  Definition impl_system : Type := (impl_equation_system * impl_equation_system)%type.

End Bool_equation_system.

Module Share_es_features (sv : SV )
                         (Import es : EQUATION_SYSTEM sv with Definition s := share) <: 
                          SHARE_ES_FEATURES sv es.
  (*EVAL*)
  Definition context := var -> s.
  Instance object_get : getable context object share := _ .
  Instance eval_equality : evalable context equality.
  constructor. repeat intro.
  destruct X0.
  apply (get X o = get X o0).
  Defined.
  Instance eval_equation : evalable context equation.
  constructor. repeat intro.
  destruct X0 as [[? ?] ?]. apply (join (get X o) (get X o0) (get X o1)).
  Defined.
  Instance eval_nzvars : evalable context var.
  constructor. repeat intro.
  apply (X X0 <> emptyshare).
  Defined.

  Definition eval_sat_equation_system (ctx : context) (ses : sat_equation_system) : Prop :=
    ctx |= (sat_equalities ses) /\ 
    ctx |= (sat_equations ses) /\
    ctx |= (sat_nzvars ses).
  Instance evalable_sat_equation_system : evalable context sat_equation_system :=
    Evalable eval_sat_equation_system.

  Definition ies2ses := 
  fun (ies : impl_equation_system) => 
  Sat_equation_system (impl_nzvars ies) (impl_equalities ies) (impl_equations ies).

  Definition eval_impl_equation_system (ctx : context) (ies : impl_equation_system) : Prop:=
   e_eval ctx (impl_exvars ies) (ies2ses ies).
  Instance evalable_impl_equation_system : evalable context impl_equation_system :=
   Evalable eval_impl_equation_system.
 
  Definition eval_impl_system (ctx : context) (is : impl_system) : Prop :=
   ctx |= (fst is) -> ctx |= (snd is).
  Instance evalable_impl_system : evalable context impl_system :=
   Evalable eval_impl_system.


  (*HEIGHT*)

  Instance object_height : heightable object := _.
  Definition equality_h := fun (eql : equality) => 
   let (o1,o2) := eql in max (|o1|) (|o2|).
  Definition equality_h_zero: is_height_zero_spec equality_h.
  Proof with tauto.
  repeat intro.
  destruct a. simpl.
  destruct (is_height_zero o).
  destruct (is_height_zero o0).
  left. rewrite max_zero...
  right. rewrite max_zero...
  right. rewrite max_zero...
  Defined.
  Instance equality_height : heightable equality :=
   Heightable equality_h equality_h_zero.
  Definition equation_h := fun (eqn : equation) => 
   match eqn with (o1,o2,o3) => max (max (|o1|)(|o2|)) (|o3|)  end.
  Definition equation_h_zero: is_height_zero_spec equation_h.
  Proof with tauto.
  repeat intro.
  destruct a as [[? ?] ?]. simpl.
  destruct (is_height_zero o).
  destruct (is_height_zero o0).
  destruct (is_height_zero o1).
  left. repeat rewrite max_zero...
  right. repeat rewrite max_zero...
  right. repeat rewrite max_zero...
  right. repeat rewrite max_zero...
  Defined.
  Instance equation_height : heightable equation :=
   Heightable equation_h equation_h_zero.
  
  Definition ses_h := fun (ses : sat_equation_system) =>
   max (|sat_equalities ses|) (|sat_equations ses|).
  Definition ses_h_zero: is_height_zero_spec ses_h.
  Proof with tauto.
  repeat intro.
  destruct a as [l1 l2 l3].
  unfold ses_h;simpl.
  destruct (is_height_zero l2).
  destruct (is_height_zero l3).
  left. simpl in e,e0. rewrite e,e0...
  right. intro. apply n.
  rewrite max_zero in H...
  right. intro. apply n.
  rewrite max_zero in H...
  Defined.
  Instance ses_height : heightable sat_equation_system :=
  Heightable ses_h ses_h_zero.
  Definition ies_h := fun (ies : impl_equation_system) =>
   max (|impl_equalities ies|) (|impl_equations ies|).
  Definition ies_h_zero: is_height_zero_spec ies_h.
  Proof with tauto.
  repeat intro.
  destruct a as [l1 l2 l3 l4].
  unfold ies_h;simpl.
  destruct (is_height_zero l3); try simpl in e.
  destruct (is_height_zero l4); try simpl in e0.
  left. rewrite e;rewrite e0...
  right. rewrite max_zero...
  right. rewrite max_zero...
  Defined.
  Instance ies_height : heightable impl_equation_system :=
  Heightable ies_h ies_h_zero.
  Definition is_h := fun (is :impl_system) => max (|fst is|)(|snd is|).
  Definition is_h_zero: is_height_zero_spec is_h.
  Proof with tauto.
  repeat intro.
  destruct a as [es1 es2].
  unfold is_h.
  destruct (is_height_zero es1).
  destruct (is_height_zero es2).
  left. rewrite max_zero...
  right. rewrite max_zero...
  right. rewrite max_zero...
  Defined.
  Instance is_height : heightable impl_system :=
  Heightable is_h is_h_zero.


  (*CHEIGHT*)
  Instance var_cheight : cheightable context var.
  constructor. repeat intro. apply (|X X0|).
  Defined.
  Instance object_cheight : cheightable context object := _.
  Instance equality_cheight : cheightable context equality.
  constructor. repeat intro. destruct X0. 
  apply (max (cheight X o) (cheight X o0)).
  Defined.
  Instance equation_cheight : cheightable context equation.
  constructor. repeat intro. destruct X0 as [[? ?] ?].
  apply (max (cheight X o) (max (cheight X o0)(cheight X o1))).
  Defined.

  Instance ses_cheight : cheightable context sat_equation_system.
  constructor. intros ctx ses.
  destruct ses as [a b c].
  apply (max (cheight ctx a) (max (cheight ctx b) (cheight ctx c))).
  Defined.

  Instance ies_cheight : cheightable context impl_equation_system.
  constructor. intros ctx ies.
  destruct ies as [a b c d].
  apply (max (cheight ctx b) (max (cheight ctx c) (cheight ctx d))).
  Defined.

  Instance is_cheight : cheightable context impl_system.
  constructor. intros ctx is.
  destruct is as [es1 es2].
  apply (max (cheight ctx es1) (cheight ctx es2)).
  Defined.

  (*VARSABLE*)
  Instance object_vars : varsable object var := _.
  Instance equality_vars : varsable equality var.
  constructor. repeat intro. destruct X.
  apply ((vars o)++(vars o0)).
  Defined.
  Instance equation_vars : varsable equation var.
  constructor. repeat intro. destruct X as [[? ?] ?].
  apply ((vars o)++(vars o0)++(vars o1)).
  Defined.
  
  Instance ses_vars : varsable sat_equation_system var.
  constructor. repeat intro.
  destruct X as [a b c].
  apply (a++(vars b)++(vars c)).
  Defined.
  
  Instance ies_vars : varsable impl_equation_system var.
  constructor. repeat intro.
  destruct X as [a b c d].
  apply (a++b++(vars c)++(vars d)).
  Defined.

  Instance is_vars : varsable impl_system var.
  constructor. repeat intro.
  destruct X as [es1 es2].
  apply ((vars es1)++(vars es2)).
  Defined.

 (*For convenience*)
 Definition vheight := fun (v : var) => 0.
 Lemma vheight_zero: is_height_zero_spec vheight.
 Proof. repeat intro. left. trivial. Qed.
 Instance height_var : heightable var := Heightable vheight vheight_zero.
 Instance varsable_var: varsable var var.
 constructor. intro. apply (X::nil). Defined.

 Lemma vars_var_list: forall (l : list var),
  vars l = l.
 Proof with try tauto.
  induction l...
  simpl in *. rewrite IHl...
 Qed.

 Lemma height_rewrite : forall {A} `{heightable A} (a : A) l,
 |a::l| = max (|a|) (|l|).
 Proof. tauto. Qed.
 Lemma cheight_rewrite : forall (l : list var) v ctx,
  cheight ctx (v::l) = max (cheight ctx v) (cheight ctx l).
 Proof. tauto. Qed.
 Lemma cheight_lt_rewrite: forall ctx l h,
  cheight ctx l < S h <-> forall v, In v l -> |ctx v| < S h.
 Proof with try tauto;try omega.
  induction l;intros.
  split;intros. inv H0. compute...
  rewrite cheight_rewrite.
  rewrite Nat.max_lub_lt_iff.
  split;intros.
  destruct H. destruct H0. subst. apply H.
  rewrite IHl in H1. apply H1...
  split. apply H. left...
  apply IHl. intros. apply H. right...
 Qed.  
 Lemma cheight_leq_rewrite: forall ctx l h,
  (cheight ctx l <= h)%nat <-> forall v, In v l -> (|ctx v| <= h)%nat.
 Proof with try tauto;try omega.
  induction l;intros.
  split;intros. inv H0. compute...
  rewrite cheight_rewrite.
  rewrite Nat.max_lub_iff.
  split;intros.
  destruct H. destruct H0. subst. apply H.
  rewrite IHl in H1. apply H1...
  split. apply H. left...
  apply IHl. intros. apply H. right...
 Qed. 
 Lemma cheight_sublist: forall ctx (l l' : list var),
  sublist l l' ->
  (cheight ctx l <= cheight ctx l')%nat.
 Proof with try tauto.
  induction l;intros.
  compute. omega.
  replace (a::l) with ((a::nil)++l) in H by tauto.
  rewrite sublist_app_iff in H.
  destruct H.
  spec IHl l' H0.
  rewrite cheight_rewrite.
  rewrite Nat.max_lub_iff.
  split...
  spec H a. detach H.
  revert H. revert a. clear.
  induction l';intros. inv H...
  rewrite cheight_rewrite.
  rewrite Nat.max_le_iff.
  destruct H;subst. left. omega.
  right. apply IHl'...
  left...
 Qed.
 (*End convenience*)

 Definition replace_snzvars := fun (ses : sat_equation_system) (l : list var) =>
  Sat_equation_system l (sat_equalities ses) (sat_equations ses).
 Definition replace_inzvars := fun (ies : impl_equation_system) (l : list var) =>
  Impl_equation_system (impl_exvars ies) l (impl_equalities ies) (impl_equations ies).
 Definition replace_isnzvars (is : impl_system) (l1 l2 : list var) : impl_system :=
  let (ies1,ies2) := is in
  (replace_inzvars ies1 l1, replace_inzvars ies2 l2).

  Definition SAT {A B} `{evalable A B}:= 
   fun (b : B) => exists (a : A), a |= b.
  Definition IMPL {A B} `{evalable A B} :=
   fun (b : B) => forall a, a |= b.
  Definition nSAT (ses : sat_equation_system) : Prop :=
   SAT (replace_snzvars ses nil).
  Definition sSAT (ses : sat_equation_system) x : Prop :=
   SAT (replace_snzvars ses (x::nil)).
  Definition sIMPL (is : impl_system) (x y : var): Prop :=
   IMPL (replace_isnzvars is (x::nil) (y::nil)).
  Definition zIMPL (is : impl_system) (x : var): Prop :=
   IMPL (replace_isnzvars is nil (x::nil)).
  Definition nIMPL (is : impl_system) : Prop :=
   IMPL (replace_isnzvars is nil nil).

 Lemma replace_snzvars_nil_eval : forall ses ctx,
  ctx |= ses <-> ctx |= (replace_snzvars ses nil) /\ ctx |= (sat_nzvars ses).
 Proof with try tauto.
  intros.
  destruct ses as [l1 l2 l3].
  unfold replace_snzvars. simpl.
  unfold eval_sat_equation_system. simpl...
 Qed.

 Lemma replace_snzvars_correct : forall ses l,
  sat_nzvars (replace_snzvars ses l) = l.
 Proof.
  repeat intros.
  destruct ses as [l1 l2 l3].
  unfold replace_snzvars. simpl. auto.
 Qed.

 Lemma replace_snzvars_height: forall ses l,
  |replace_snzvars ses l| = |ses|.
 Proof.
  intros.
  destruct ses as [l1 l2 l3].
  simpl. unfold ses_h. simpl. auto.
 Qed.

 Lemma replace_snzvars_id: forall ses l,
  sat_nzvars ses = l ->
  replace_snzvars ses l = ses.
 Proof.
  intros.
  destruct ses as [l1 l2 l3].
  unfold replace_snzvars. simpl. simpl in H.
  congruence.
 Qed.

 Lemma replace_snzvars_reduce: forall ses l1 l2,
  replace_snzvars (replace_snzvars ses l1) l2 = replace_snzvars ses l2.
 Proof.
  intros.
  destruct ses as [l3 l4 l5].
  unfold replace_snzvars;simpl. auto.
 Qed.

 Lemma ies2ses_nzvars: forall ies,
  impl_nzvars ies = sat_nzvars (ies2ses ies).
 Proof. tauto. Qed.

 Lemma replace_inzvars_nil_eval: forall ies ctx,
  ctx |= ies <-> 
  exists ctx', [impl_exvars ies => ctx'] ctx |= replace_snzvars (ies2ses ies) nil /\
  [impl_exvars ies => ctx'] ctx |= impl_nzvars ies.
 Proof with try tauto.
  intros;split;intros.
  destruct H as [ctx' H].
  exists ctx'. apply replace_snzvars_nil_eval...
  destruct H as [ctx' H].
  exists ctx'. apply replace_snzvars_nil_eval...
 Qed.

 Lemma replace_inzvars_reduce: forall ies l l',
  replace_inzvars (replace_inzvars ies l) l' = replace_inzvars ies l'.
 Proof. intros;tauto. Qed.

 Lemma fst_replace_isnzvars: forall is l1 l2,
  fst (replace_isnzvars is l1 l2) = replace_inzvars (fst is) l1.
 Proof.
  intros.
  destruct is as [ies1 ies2].
  unfold replace_isnzvars. trivial.
 Qed.
 Lemma snd_replace_isnzvars: forall is l1 l2,
  snd (replace_isnzvars is l1 l2) = replace_inzvars (snd is) l2.
 Proof.
  intros. unfold replace_isnzvars.
  destruct is as [ies1 ies2]. trivial.
 Qed.

 Lemma replace_inzvars_id: forall ies,
  replace_inzvars ies (impl_nzvars ies) = ies.
 Proof.
  intros. 
  destruct ies as [l1 l2 l3 l4].
  unfold replace_inzvars. trivial.
 Qed.

 Lemma replace_inzvars_correct: forall ies l,
  impl_nzvars (replace_inzvars ies l) = l.
 Proof. intros. tauto. Qed.

 Lemma replace_inzvars_exvars: forall ies l,
  impl_exvars (replace_inzvars ies l) = impl_exvars ies.
 Proof. intros. tauto. Qed.

 Lemma replace_inzvars_ies2ses: forall ies l,
  ies2ses (replace_inzvars ies l) = replace_snzvars (ies2ses ies) l.
 Proof. intros. tauto. Qed.

 Lemma vars_replace_isnzvars: forall is l1 l2,
  vars (replace_isnzvars is l1 l2) = 
  vars (replace_inzvars (fst is) l1) ++ vars (replace_inzvars (snd is) l2).
 Proof.
  intros. destruct is as [ies1 ies2]. trivial.
 Qed.

 Lemma replace_isnzvars_eval: forall ctx is l1 l2,
  ctx |= replace_isnzvars is l1 l2 <->
  (ctx |= replace_inzvars (fst is) l1 -> ctx |= replace_inzvars (snd is) l2).
 Proof.
  intros. 
  destruct is as [ies1 ies2].
  unfold replace_isnzvars. simpl.
  unfold eval_impl_system. tauto.
 Qed.

 Lemma replace_isnzvars_reduce: forall is l1 l2 l3 l4,
  replace_isnzvars (replace_isnzvars is l1 l2) l3 l4 = replace_isnzvars is l3 l4.
 Proof.
  intros. destruct is as [ies1 ies2].
  unfold replace_isnzvars.
  repeat rewrite replace_inzvars_reduce. trivial.
 Qed.

 Lemma replace_inzvars_height: forall ies l,
  |replace_inzvars ies l| = |ies|.
 Proof. intros. tauto. Qed.

 Lemma replace_isnzvars_height: forall is l l',
  |replace_isnzvars is l l'| = |is|.
 Proof.
  intros.
  destruct is as [? ?]. simpl.
  unfold is_h;simpl.
  repeat rewrite replace_inzvars_height. auto.
 Qed.

 Lemma replace_inzvars_eval_nil: forall rho ies l,
  rho |= replace_inzvars ies l ->
  rho |= replace_inzvars ies nil.
 Proof with try tauto.
  intros.
  destruct H as [rho' H].
  exists rho'.
  rewrite replace_inzvars_ies2ses,replace_inzvars_exvars in *.
  rewrite replace_snzvars_nil_eval in H...
 Qed.

End Share_es_features.

Module Type BOOL_ES_FEATURES (sv : SV )(Import es : EQUATION_SYSTEM sv with Definition s := bool).
  (*EVAL*)
  Definition context := var -> s.
  Instance object_get : getable context object s := _ .
  Instance eval_equality : evalable context equality.
  constructor. repeat intro.
  destruct X0.
  apply (get X o = get X o0).
  Defined.
  Definition bjoin := fun (b1 b2 b3 : bool) => b1 && b2 = false /\ b1||b2 = b3.
  Instance eval_equation : evalable context equation.
  constructor. repeat intro.
  destruct X0 as [[? ?] ?]. apply (bjoin (get X o) (get X o0) (get X o1)).
  Defined.
  Instance eval_nzvars : evalable context var.
  constructor. repeat intro.
  apply (X X0 <> false).
  Defined.

  Definition eval_sat_equation_system (ctx : context) (ses : sat_equation_system) : Prop :=
    ctx |= (sat_equalities ses) /\ 
    ctx |= (sat_equations ses) /\
    ctx |= (sat_nzvars ses).
  Instance evalable_sat_equation_system : evalable context sat_equation_system :=
    Evalable eval_sat_equation_system.

  Definition ies2ses := 
  fun (ies : impl_equation_system) => 
  Sat_equation_system (impl_nzvars ies) (impl_equalities ies) (impl_equations ies) .

  Definition eval_impl_equation_system (ctx : context) (ies : impl_equation_system) : Prop:=
   e_eval ctx (impl_exvars ies) (ies2ses ies).
  Instance evalable_impl_equation_system : evalable context impl_equation_system :=
   Evalable eval_impl_equation_system.

  Definition eval_impl_system (ctx : context) (is : impl_system) : Prop :=
   ctx |= (fst is) -> ctx |= (snd is).
  Instance evalable_impl_system : evalable context impl_system :=
   Evalable eval_impl_system.

  (*VARSABLE*)
  Instance object_vars : varsable object var := _.
  Instance equality_vars : varsable equality var.
  constructor. repeat intro. destruct X.
  apply ((vars o)++(vars o0)).
  Defined.
  Instance equation_vars : varsable equation var.
  constructor. repeat intro. destruct X as [[? ?] ?].
  apply ((vars o)++(vars o0)++(vars o1)).
  Defined.
  Instance ses_vars : varsable sat_equation_system var.
  constructor. repeat intro.
  destruct X as [a b c].
  apply (a++(vars b)++(vars c)).
  Defined.
  Instance ies_vars : varsable impl_equation_system var.
  constructor. repeat intro.
  destruct X as [a b c d].
  apply (a++b++(vars c)++(vars d)).
  Defined.
  Instance is_vars : varsable impl_system var.
  constructor. repeat intro.
  destruct X as [es1 es2].
  apply ((vars es1)++(vars es2)).
  Defined.

 Definition replace_snzvars := fun (ses : sat_equation_system) (l : list var) =>
  Sat_equation_system l (sat_equalities ses) (sat_equations ses).
 Definition replace_inzvars := fun (ies : impl_equation_system) (l : list var) =>
  Impl_equation_system (impl_exvars ies) l (impl_equalities ies) (impl_equations ies).
 Definition replace_isnzvars (is : impl_system) (l1 l2 : list var) : impl_system :=
  let (ies1,ies2) := is in
  (replace_inzvars ies1 l1, replace_inzvars ies2 l2).

  Definition SAT {A B} `{evalable A B} := 
   fun (b : B) => exists (a : A), a |= b.
  Definition IMPL {A B} `{evalable A B} :=
   fun (b : B) => forall a, a |= b.
  Definition nSAT (ses : sat_equation_system) : Prop :=
   SAT (replace_snzvars ses nil).
  Definition sSAT (ses : sat_equation_system) x : Prop :=
   SAT (replace_snzvars ses (x::nil)).
  Definition sIMPL (is : impl_system) (x y : var): Prop :=
   IMPL (replace_isnzvars is (x::nil) (y::nil)).
  Definition zIMPL (is : impl_system) (x : var): Prop :=
   IMPL (replace_isnzvars is nil (x::nil)).
  Definition nIMPL (is : impl_system) : Prop :=
   IMPL (replace_isnzvars is nil nil).

 Axiom replace_snzvars_nil_eval : forall ses ctx,
  ctx |= ses <-> ctx |= (replace_snzvars ses nil) /\ ctx |= (sat_nzvars ses).
 Axiom replace_snzvars_correct : forall ses l,
  sat_nzvars (replace_snzvars ses l) = l.
 Axiom replace_snzvars_id: forall ses l,
  sat_nzvars ses = l ->
  replace_snzvars ses l = ses.
 Axiom replace_snzvars_reduce: forall ses l1 l2,
  replace_snzvars (replace_snzvars ses l1) l2 = replace_snzvars ses l2.
 Axiom ies2ses_nzvars: forall ies,
  impl_nzvars ies = sat_nzvars (ies2ses ies).
 Axiom replace_inzvars_nil_eval: forall ies ctx,
  ctx |= ies <-> 
  exists ctx', [impl_exvars ies => ctx'] ctx |= replace_snzvars (ies2ses ies) nil /\
  [impl_exvars ies => ctx'] ctx |= impl_nzvars ies.
 Axiom replace_inzvars_reduce: forall ies l l',
  replace_inzvars (replace_inzvars ies l) l' = replace_inzvars ies l'.
 Axiom fst_replace_isnzvars: forall is l1 l2,
  fst (replace_isnzvars is l1 l2) = replace_inzvars (fst is) l1.
 Axiom snd_replace_isnzvars: forall is l1 l2,
  snd (replace_isnzvars is l1 l2) = replace_inzvars (snd is) l2.
 Axiom replace_inzvars_id: forall ies,
  replace_inzvars ies (impl_nzvars ies) = ies.
 Axiom replace_inzvars_correct: forall ies l,
  impl_nzvars (replace_inzvars ies l) = l.
 Axiom replace_inzvars_exvars: forall ies l,
  impl_exvars (replace_inzvars ies l) = impl_exvars ies.
 Axiom replace_inzvars_ies2ses: forall ies l,
  ies2ses (replace_inzvars ies l) = replace_snzvars (ies2ses ies) l.
 Axiom vars_replace_isnzvars: forall is l1 l2,
  vars (replace_isnzvars is l1 l2) = 
  vars (replace_inzvars (fst is) l1) ++ vars (replace_inzvars (snd is) l2).
 Axiom replace_isnzvars_eval: forall ctx is l1 l2,
  ctx |= replace_isnzvars is l1 l2 <->
  (ctx |= replace_inzvars (fst is) l1 -> ctx |= replace_inzvars (snd is) l2).
 Axiom replace_isnzvars_reduce: forall is l1 l2 l3 l4,
  replace_isnzvars (replace_isnzvars is l1 l2) l3 l4 = replace_isnzvars is l3 l4.
 Axiom replace_inzvars_eval_nil: forall rho ies l,
  rho |= replace_inzvars ies l ->
  rho |= replace_inzvars ies nil.

End BOOL_ES_FEATURES.

Module Bool_es_features (sv : SV )
                        (Import es : EQUATION_SYSTEM sv with Definition s := bool)<:
                        BOOL_ES_FEATURES sv es.
  (*EVAL*)
  Definition context := var -> s.
  Instance object_get : getable context object s := _ .
  Instance eval_equality : evalable context equality.
  constructor. repeat intro.
  destruct X0.
  apply (get X o = get X o0).
  Defined.
  Definition bjoin := fun (b1 b2 b3 : bool) => b1 && b2 = false /\ b1||b2 = b3.
  Instance eval_equation : evalable context equation.
  constructor. repeat intro.
  destruct X0 as [[? ?] ?]. apply (bjoin (get X o) (get X o0) (get X o1)).
  Defined.
  Instance eval_nzvars : evalable context var.
  constructor. repeat intro.
  apply (X X0 <> false).
  Defined.

  Definition eval_sat_equation_system (ctx : context) (ses : sat_equation_system) : Prop :=
    ctx |= (sat_equalities ses) /\ 
    ctx |= (sat_equations ses) /\
    ctx |= (sat_nzvars ses).
  Instance evalable_sat_equation_system : evalable context sat_equation_system :=
    Evalable eval_sat_equation_system.

  Definition ies2ses := 
  fun (ies : impl_equation_system) => 
  Sat_equation_system (impl_nzvars ies) (impl_equalities ies) (impl_equations ies).

  Definition eval_impl_equation_system (ctx : context) (ies : impl_equation_system) : Prop:=
   e_eval ctx (impl_exvars ies) (ies2ses ies).
  Instance evalable_impl_equation_system : evalable context impl_equation_system :=
   Evalable eval_impl_equation_system.

  Definition eval_impl_system (ctx : context) (is : impl_system) : Prop :=
   ctx |= (fst is) -> ctx |= (snd is).
  Instance evalable_impl_system : evalable context impl_system :=
   Evalable eval_impl_system.

  (*VARSABLE*)
  Instance object_vars : varsable object var := _.
  Instance equality_vars : varsable equality var.
  constructor. repeat intro. destruct X.
  apply ((vars o)++(vars o0)).
  Defined.
  Instance equation_vars : varsable equation var.
  constructor. repeat intro. destruct X as [[? ?] ?].
  apply ((vars o)++(vars o0)++(vars o1)).
  Defined.
  Instance ses_vars : varsable sat_equation_system var.
  constructor. repeat intro.
  destruct X as [a b c].
  apply (a++(vars b)++(vars c)).
  Defined.
  Instance ies_vars : varsable impl_equation_system var.
  constructor. repeat intro.
  destruct X as [a b c d].
  apply (a++b++(vars c)++(vars d)).
  Defined.
  Instance is_vars : varsable impl_system var.
  constructor. repeat intro.
  destruct X as [es1 es2].
  apply ((vars es1)++(vars es2)).
  Defined.

 Definition replace_snzvars := fun (ses : sat_equation_system) (l : list var) =>
  Sat_equation_system l (sat_equalities ses) (sat_equations ses).
 Definition replace_inzvars := fun (ies : impl_equation_system) (l : list var) =>
  Impl_equation_system (impl_exvars ies) l (impl_equalities ies) (impl_equations ies).
 Definition replace_isnzvars (is : impl_system) (l1 l2 : list var) : impl_system :=
  let (ies1,ies2) := is in
  (replace_inzvars ies1 l1, replace_inzvars ies2 l2).

  Definition SAT {A B} `{evalable A B}:= 
   fun (b : B) => exists (a : A), a |= b.
  Definition IMPL {A B} `{evalable A B} :=
   fun (b : B) => forall a, a |= b.
  Definition nSAT (ses : sat_equation_system) : Prop :=
   SAT (replace_snzvars ses nil).
  Definition sSAT (ses : sat_equation_system) x : Prop :=
   SAT (replace_snzvars ses (x::nil)).
  Definition sIMPL (is : impl_system) (x y : var): Prop :=
   IMPL (replace_isnzvars is (x::nil) (y::nil)).
  Definition zIMPL (is : impl_system) (x : var): Prop :=
   IMPL (replace_isnzvars is nil (x::nil)).
  Definition nIMPL (is : impl_system) : Prop :=
   IMPL (replace_isnzvars is nil nil).

 Lemma replace_snzvars_nil_eval : forall ses ctx,
  ctx |= ses <-> ctx |= (replace_snzvars ses nil) /\ ctx |= (sat_nzvars ses).
 Proof with try tauto.
  intros.
  destruct ses as [l1 l2 l3].
  unfold replace_snzvars. simpl.
  unfold eval_sat_equation_system. simpl...
 Qed.

 Lemma replace_snzvars_correct : forall ses l,
  sat_nzvars (replace_snzvars ses l) = l.
 Proof.
  repeat intros.
  destruct ses as [l1 l2 l3].
  unfold replace_snzvars. simpl. auto.
 Qed.

 Lemma replace_snzvars_id: forall ses l,
  sat_nzvars ses = l ->
  replace_snzvars ses l = ses.
 Proof.
  intros.
  destruct ses as [l1 l2 l3].
  unfold replace_snzvars. simpl. simpl in H.
  congruence.
 Qed.

 Lemma replace_snzvars_reduce: forall ses l1 l2,
  replace_snzvars (replace_snzvars ses l1) l2 = replace_snzvars ses l2.
 Proof.
  intros.
  destruct ses as [l3 l4 l5].
  unfold replace_snzvars;simpl. auto.
 Qed.

 Lemma ies2ses_nzvars: forall ies,
  impl_nzvars ies = sat_nzvars (ies2ses ies).
 Proof. tauto. Qed.

 Lemma replace_inzvars_nil_eval: forall ies ctx,
  ctx |= ies <-> 
  exists ctx', [impl_exvars ies => ctx'] ctx |= replace_snzvars (ies2ses ies) nil /\
  [impl_exvars ies => ctx'] ctx |= impl_nzvars ies.
 Proof with try tauto.
  intros;split;intros.
  destruct H as [ctx' H].
  exists ctx'. apply replace_snzvars_nil_eval...
  destruct H as [ctx' H].
  exists ctx'. apply replace_snzvars_nil_eval...
 Qed.

 Lemma replace_inzvars_reduce: forall ies l l',
  replace_inzvars (replace_inzvars ies l) l' = replace_inzvars ies l'.
 Proof. intros;tauto. Qed.

 Lemma fst_replace_isnzvars: forall is l1 l2,
  fst (replace_isnzvars is l1 l2) = replace_inzvars (fst is) l1.
 Proof.
  intros.
  destruct is as [ies1 ies2].
  unfold replace_isnzvars. trivial.
 Qed.
 Lemma snd_replace_isnzvars: forall is l1 l2,
  snd (replace_isnzvars is l1 l2) = replace_inzvars (snd is) l2.
 Proof.
  intros. unfold replace_isnzvars.
  destruct is as [ies1 ies2]. trivial.
 Qed.

 Lemma replace_inzvars_id: forall ies,
  replace_inzvars ies (impl_nzvars ies) = ies.
 Proof.
  intros. 
  destruct ies as [l1 l2 l3 l4].
  unfold replace_inzvars. trivial.
 Qed.

 Lemma replace_inzvars_correct: forall ies l,
  impl_nzvars (replace_inzvars ies l) = l.
 Proof. intros. tauto. Qed.

 Lemma replace_inzvars_exvars: forall ies l,
  impl_exvars (replace_inzvars ies l) = impl_exvars ies.
 Proof. intros. tauto. Qed.

 Lemma replace_inzvars_ies2ses: forall ies l,
  ies2ses (replace_inzvars ies l) = replace_snzvars (ies2ses ies) l.
 Proof. intros. tauto. Qed.

 Lemma vars_replace_isnzvars: forall is l1 l2,
  vars (replace_isnzvars is l1 l2) = 
  vars (replace_inzvars (fst is) l1) ++ vars (replace_inzvars (snd is) l2).
 Proof.
  intros. destruct is as [ies1 ies2]. trivial.
 Qed.

 Lemma replace_isnzvars_eval: forall ctx is l1 l2,
  ctx |= replace_isnzvars is l1 l2 <->
  (ctx |= replace_inzvars (fst is) l1 -> ctx |= replace_inzvars (snd is) l2).
 Proof.
  intros. 
  destruct is as [ies1 ies2].
  unfold replace_isnzvars. simpl.
  unfold eval_impl_system. tauto.
 Qed.

 Lemma replace_isnzvars_reduce: forall is l1 l2 l3 l4,
  replace_isnzvars (replace_isnzvars is l1 l2) l3 l4 = replace_isnzvars is l3 l4.
 Proof.
  intros. destruct is as [ies1 ies2].
  unfold replace_isnzvars.
  repeat rewrite replace_inzvars_reduce. trivial.
 Qed.

 Lemma replace_inzvars_eval_nil: forall rho ies l,
  rho |= replace_inzvars ies l ->
  rho |= replace_inzvars ies nil.
 Proof with try tauto.
  intros.
  destruct H as [rho' H].
  exists rho'.
  rewrite replace_inzvars_ies2ses,replace_inzvars_exvars in *.
  rewrite replace_snzvars_nil_eval in H...
 Qed.
End Bool_es_features.
*)
(*
  Inductive result (A B : Type) : Type := 
    | Absurd (* reach contradiction *)
    | Simpler : B -> result A B
    | Same : A -> result A B.
  Implicit Arguments Absurd [A B].
  Implicit Arguments Simpler [A B].
  Implicit Arguments Same [A B].

Module Type IEQUATION_SYSTEM (sv : SV) (Import es : EQUATION_SYSTEM sv).

  Parameter substitution : Type.
  Parameter sbst_var : substitution -> var.
  Parameter sbst_object : substitution -> object.
  Parameter mkCsubstitution : var -> s -> substitution.
  Parameter mkVsubstitution : forall (x y : var), x <> y -> substitution.
  Parameter dec_eq_substitution : EqDec substitution.

  Record equation_system : Type := Equation_system {
    eqs_nzvars        : list var;
    eqs_substitutions : list substitution;
    eqs_equations     : list equation
  }.

 Parameter eql2subst : equality -> result substitution unit.
 Parameter eql2subst_list : (list equality) -> option (list (substitution)).
 Parameter subst2eql : substitution -> equality.
 Parameter subst2eql_list : list substitution -> list equality.

 Definition wrapped_ses:= fun (ses : sat_equation_system) =>
   let l1 := sat_nzvars ses in
   let l2 := sat_equalities ses in
   let l3 := sat_equations ses in
    match eql2subst_list l2 with
    |None => None
    |Some l2' => Some (Equation_system l1 l2' l3)
    end.

 Definition unwrapped_ses:= fun ses =>
   let l1 := eqs_nzvars ses in
   let l2 := eqs_substitutions ses in
   let l3 := eqs_equations ses in
    Sat_equation_system l1 (subst2eql_list l2) l3.

End IEQUATION_SYSTEM.

Module Iequation_system (sv : SV) 
 (Import es : EQUATION_SYSTEM sv) <: IEQUATION_SYSTEM sv es.

 Import Share.

  Definition substitution : Type :=
    {p : (var * object)%type | snd p <> Vobject (fst p)}.
  Definition sbst_var (sbst : substitution) : var := fst (projT1 sbst).
  Definition sbst_object (sbst : substitution) : object := snd (projT1 sbst).
  Program Definition mkCsubstitution (x : var) (sh : s) : substitution :=
    (x, Cobject sh).
  Next Obligation. disc. Defined.
  Program Definition mkVsubstitution (x : var) (y : var) (pf : x <> y) : substitution :=
    (x, Vobject y).
  Next Obligation. unfold fst, snd. intro. apply pf. inv H. trivial. Defined.
  
  Instance dec_eq_substitution : EqDec substitution.
  Proof.
    repeat intro. destruct a. destruct a'.
    destruct x. destruct x0.
    case (eq_dec v v0). case (eq_dec o o0).
    left. subst. apply exist_ext. trivial.
    right. intro. inv H. apply n1. trivial.
    right. intro. inv H. apply n1. trivial.
  Qed.

  Record equation_system : Type := Equation_system {
    eqs_nzvars       : list var;
    eqs_substitutions : list substitution;
    eqs_equations     : list equation
  }.

 Program Definition eql2subst (eql : equality) : result substitution unit:=
  match eql with
  |(Vobject v, obj)
  |(obj, Vobject v)=> match eq_dec obj (Vobject v) with
                      |left _ => Simpler tt
                      |right _ => Same (v,obj)
                      end
  |(Cobject c1, Cobject c2) => match eq_dec c1 c2 with
                               |left _ => Simpler tt
                               |right _ => Absurd
                               end
  end.
  Next Obligation. intro. inv H. Defined.
  
 Fixpoint eql2subst_list (l : list equality) : option (list (substitution)) :=
  match l with
  |nil => Some nil
  |eql::l' => match eql2subst eql with
              |Same subst' => match eql2subst_list l' with 
                                    |Some l'' => Some (subst'::l'')
                                    |None => None
                                    end
              |Simpler tt => eql2subst_list l'
              |Absurd => None
              end
  end.

  Definition subst2eql (subst : substitution) : equality :=
   let (v,obj) := projT1 subst in (Vobject v,obj).
  Definition subst2eql_list := fun l =>
   fold_right (fun sbst l' => (subst2eql sbst)::l') nil l.

  Definition wrapped_ses:= fun (ses : sat_equation_system) =>
   let l1 := sat_nzvars ses in
   let l2 := sat_equalities ses in
   let l3 := sat_equations ses in
    match eql2subst_list l2 with
    |None => None
    |Some l2' => Some (Equation_system l1 l2' l3)
    end.

  Definition unwrapped_ses:= fun ses =>
   let l1 := eqs_nzvars ses in
   let l2 := eqs_substitutions ses in
   let l3 := eqs_equations ses in
    Sat_equation_system l1 (subst2eql_list l2) l3.

End Iequation_system. 

Module Share_internal_system (sv : SV) 
 (Import es : EQUATION_SYSTEM sv with Definition s := share)
 (Import esf : SHARE_ES_FEATURES sv es).

  Definition substitution : Type :=
    {p : (var * object)%type | snd p <> Vobject (fst p)}.
  Definition sbst_var (sbst : substitution) : var := fst (projT1 sbst).
  Definition sbst_object (sbst : substitution) : object := snd (projT1 sbst).
  Program Definition mkCsubstitution (x : var) (sh : s) : substitution :=
    (x, Cobject sh).
  Next Obligation. disc. Defined.
  Program Definition mkVsubstitution (x : var) (y : var) (pf : x <> y) : substitution :=
    (x, Vobject y).
  Next Obligation. unfold fst, snd. intro. apply pf. inv H. trivial. Defined.
  
  Instance dec_eq_substitution : EqDec substitution.
  Proof.
    repeat intro. destruct a. destruct a'.
    destruct x. destruct x0.
    case (eq_dec v v0). case (eq_dec o o0).
    left. subst. apply exist_ext. trivial.
    right. intro. inv H. apply n1. trivial.
    right. intro. inv H. apply n1. trivial.
  Qed.

  Record equation_system : Type := Equation_system {
    eqs_nzvars       : list var;
    eqs_substitutions : list substitution;
    eqs_equations     : list equation
  }.

 Program Definition eql2subst (eql : equality) : result substitution unit:=
  match eql with
  |(Vobject v, obj)
  |(obj, Vobject v)=> match eq_dec obj (Vobject v) with
                      |left _ => Simpler tt
                      |right _ => Same (v,obj)
                      end
  |(Cobject c1, Cobject c2) => match eq_dec c1 c2 with
                               |left _ => Simpler tt
                               |right _ => Absurd
                               end
  end.
  Next Obligation. intro. inv H. Defined.
  
 Fixpoint eql2subst_list (l : list equality) : option (list (substitution)) :=
  match l with
  |nil => Some nil
  |eql::l' => match eql2subst eql with
              |Same subst' => match eql2subst_list l' with 
                                    |Some l'' => Some (subst'::l'')
                                    |None => None
                                    end
              |Simpler tt => eql2subst_list l'
              |Absurd => None
              end
  end.

  Definition subst2eql (subst : substitution) : equality :=
   let (v,obj) := projT1 subst in (Vobject v,obj).
  Definition subst2eql_list := fun l =>
   fold_right (fun sbst l' => (subst2eql sbst)::l') nil l.

  Definition wrapped_ses:= fun (ses : sat_equation_system) =>
   let l1 := sat_nzvars ses in
   let l2 := sat_equalities ses in
   let l3 := sat_equations ses in
    match eql2subst_list l2 with
    |None => None
    |Some l2' => Some (Equation_system l1 l2' l3)
    end.

  Definition unwrapped_ses:= fun ses =>
   let l1 := eqs_nzvars ses in
   let l2 := eqs_substitutions ses in
   let l3 := eqs_equations ses in
    Sat_equation_system l1 (subst2eql_list l2) l3.

  Lemma equiv_equation_comm: forall (fp1 fp2 fp3 : object),
    equiv_eval (fp1, fp2, fp3) (fp2, fp1, fp3).
  Proof.
    repeat intro.
    simpl. split; apply join_comm; trivial.
  Qed.

  Class substable (A : Type) (B : Type) : Type := Substable 
   {subst: substitution -> A -> B}.
  Implicit Arguments Substable [A B].

  Definition eval_substitution (ctx : context) (subst : substitution) : Prop :=
    match subst with exist (x, fp) pf => ctx x = get ctx fp end.
  Instance evalable_substitution : evalable context substitution :=
    Evalable eval_substitution.
  Definition vars_subst (subst : substitution) : list var :=
   (sbst_var subst) :: (vars (sbst_object subst)).
  Instance varsable_subst : varsable substitution var :=
   Varsable vars_subst.
  Definition eval_equation_system (ctx : context) (eqs : equation_system) : Prop :=
    ctx |= (eqs_nzvars eqs) /\ ctx |= (eqs_substitutions eqs) /\ ctx |= (eqs_equations eqs).
  Instance evalable_equation_system : evalable context equation_system :=
    Evalable eval_equation_system.


  Lemma eql2subst_Simpler: forall eql,
   eql2subst eql = Simpler tt ->
   valid eql.
  Proof with try tauto.
   repeat intro.
   destruct eql as [obj1 obj2].
   icase obj1;icase obj2.
   compute in H.
   destruct (sv.t_eq_dec v0 v);subst;simpl...
   inv H. simpl in H.
   destruct (eq_dec s0 s1);subst;simpl;inv H...
  Qed.

  Lemma eql2subst_Absurd: forall eql,
   eql2subst eql = Absurd ->
   forall rho, ~rho|=eql.
  Proof with try tauto.
   repeat intro.
   destruct eql as [obj1 obj2].
   icase obj1;icase obj2;compute in H.
   destruct (sv.t_eq_dec v0 v);subst;simpl;inv H...
   destruct (s_eq_dec s0 s1);inv H.
   compute in H0...
  Qed.

  Lemma eql2subst_Same: forall eql subst,
    eql2subst eql = Same subst ->
    equiv_eval eql subst.
  Proof with try tauto.
   repeat intro.
   destruct eql as [obj1 obj2].
   icase obj1;icase obj2;compute in H;
   try destruct (sv.t_eq_dec v0 v);subst;simpl;inv H...
   compute. split;intros;subst...
   destruct (s_eq_dec s0 s1);inv H1.
  Qed.

  Lemma eql2subst_list_None: forall l,
   eql2subst_list l = None -> forall rho, ~rho |= l.
  Proof with try tauto.
   induction l;repeat intro;inv H.
   destruct H0.
   remember (eql2subst a). symmetry in Heqr.
   destruct r;inv H2.
   apply eql2subst_Absurd with (rho:=rho) in Heqr...
   icase u. spec IHl H3 rho...
   remember (eql2subst_list l).
   symmetry in Heqo. icase o.
   spec IHl... spec IHl rho...
  Qed.

  Lemma eql2subst_list_Some: forall l l',
   eql2subst_list l = Some l' -> equiv_eval l l'.
  Proof with try tauto.
   induction l;repeat intro;inv H.
   simpl...
   remember (eql2subst a). symmetry in Heqr.
   destruct r;inv H1. icase u.
   apply eql2subst_Simpler in Heqr...
   spec Heqr rho. spec IHl l' H0 rho. simpl in *...
   remember (eql2subst_list l).
   symmetry in Heqo. icase o.
   inv H0. spec IHl l0. spec IHl...
   apply eql2subst_Same in Heqr.
   spec IHl rho. spec Heqr rho. simpl in *...
  Qed.


  Lemma subst2eql_eval: forall sbst,
   equiv_eval sbst (subst2eql sbst).
  Proof with try tauto.
   repeat intro.
   destruct sbst as [[? ?] ?].
   icase o;compute...
  Qed.
  Lemma subst2eql_list_eval: forall l,
   equiv_eval l (subst2eql_list l).
  Proof with try tauto.
   induction l;repeat intro;simpl...
   spec IHl rho.
   generalize (subst2eql_eval a rho);simpl;intro...
  Qed.

  Lemma wrapped_ses_None: forall ses,
   wrapped_ses ses = None -> forall rho, ~rho|=ses.
  Proof with try tauto.
   intros.
   destruct ses as [l1 l2 l3].
   unfold wrapped_ses in H. simpl in H.
   remember (eql2subst_list l2).
   symmetry in Heqo. icase o;inv H.
   apply eql2subst_list_None with (rho:=rho) in Heqo.
   intro;apply Heqo. simpl in *.
   unfold eval_sat_equation_system in *;simpl in *...
  Qed.

  Lemma wrapped_ses_Some: forall ses ses',
   wrapped_ses ses = Some ses' -> equiv_eval ses ses'.
  Proof with try tauto.
   intros.
   destruct ses as [l1 l2 l3].
   unfold wrapped_ses in H. simpl in H.
   remember (eql2subst_list l2).
   symmetry in Heqo. icase o;inv H.
   apply eql2subst_list_Some in Heqo.
   repeat intro; simpl in *;spec Heqo rho;
   unfold eval_sat_equation_system,eval_equation_system in *;simpl in *...
  Qed.

  Lemma unwrapped_ses_eval: forall ses,
   equiv_eval ses (unwrapped_ses ses).
  Proof with try tauto.
   repeat intro.
   destruct ses as [l1 l2 l3].
   generalize (subst2eql_list_eval l2 rho);simpl;intro.
   unfold eval_equation_system,eval_sat_equation_system...
  Qed.

  Definition subst_object (sbst : substitution) (fp' : object) : object :=
    match sbst, fp' with
     | _, Cobject c => Cobject c
     | exist (x, fp) _, Vobject v => if eq_dec x v then fp else Vobject v
    end.
  Instance substable_object : substable object object :=
   Substable subst_object.

  Lemma eval_subst_correct: forall (sbst : substitution) ctx,
   ctx |= sbst ->
   ctx (sbst_var sbst) = get ctx (sbst_object sbst).
  Proof.
   intros.
   destruct sbst as [[? ?] ?]. icase o.
  Qed.
 
  Lemma subst_object_id: forall sbst,
    subst sbst (sbst_object sbst) = (sbst_object sbst).
  Proof.
    destruct sbst; auto. simpl. destruct x. unfold sbst_object. simpl. 
    destruct o; auto. case (eq_dec v v0); auto.
  Qed.

  Definition upd_subst (ctx : context) (sbst : substitution) : context :=
    upd ctx (sbst_var sbst) (get ctx (sbst_object sbst)).
   
  Lemma subst_object_upd: forall sbst fp' ctx,
    get ctx (subst sbst fp') = get (upd_subst ctx sbst) fp'.
  Proof with try tauto.
    intros. destruct sbst. simpl. destruct x. destruct fp'; auto.
    unfold upd_subst, upd, sbst_var. simpl. case (eq_dec v v0); simpl...
  Qed.

  Lemma subst_object_vars: forall sbst fp' fp'',
    (sbst_object sbst <> Vobject (sbst_var sbst)) ->
    subst sbst fp' = fp'' ->
    (forall x', In x' (vars fp'') -> 
       In x' ((vars sbst) ++ (vars fp'))) /\
       ~In (sbst_var sbst) (vars fp'').
  Proof.
    repeat intro. destruct sbst. destruct x.
    icase fp'; icase fp''; unfold fst,snd in n; simpl in *.
    Focus 2.  split. intros. contradiction H1. auto.
    Focus 2. split. intros. contradiction H1. auto.
    split. intros. destruct H1. Focus 2. contradiction H1.
    subst. destruct (eq_dec v v0);subst. right. simpl. left;trivial.
    injection H0; intro;subst. right. apply in_app_iff;right. apply in_eq.
    destruct (eq_dec v v0). 
    subst. unfold sbst_object,sbst_var in *. simpl in *.
    apply neg_false. split. intros. destruct H0;trivial.
    Focus 2. auto. subst. Focus 2.
    injection H0; intro;subst.
    revert H. unfold sbst_object,sbst_var. simpl. intro.
    apply neg_false. split;auto. intro. destruct H1;subst. 
    auto. trivial.
    contradiction H. trivial.
  Qed.

  Definition subst_substitution (sbst sbst' : substitution) : result substitution unit :=
    match sbst, sbst' with
      exist (x, o) _, exist (x', o') _ =>
        if eq_dec x x' then
          match o, o' with
           | Cobject c1, Cobject c2 => if eq_dec c1 c2 then Simpler tt else Absurd
           | Cobject c1, Vobject v2 => Same (mkCsubstitution v2 c1)
           | Vobject v1, Cobject c2 => Same (mkCsubstitution v1 c2)
           | Vobject v1, Vobject v2 =>
             match eq_dec v1 v2 with
              | left _ => Simpler tt
              | right pf => Same (mkVsubstitution v1 v2 pf)
             end
          end
        else match subst sbst o' with
          | Cobject c2' => Same (mkCsubstitution x' c2')
          | Vobject v2' => 
            match eq_dec x' v2' with
             | left _ => Simpler tt
             | right pf => Same (mkVsubstitution x' v2' pf)
            end
        end
    end.
 Instance substable_substitution : substable substitution (result substitution unit) :=
  Substable subst_substitution.

  Lemma subst_substitution_equiv: forall sbst sbst' sbst'',
    subst sbst sbst' = Same sbst'' ->
      (forall ctx, eval ctx sbst'' <-> eval (upd_subst ctx sbst) sbst') /\
      (forall x, In x (vars sbst'') -> In x ((vars (sbst_object sbst)) ++ (vars sbst'))) /\
      ~In (sbst_var sbst) (vars sbst'').
  Proof with try tauto.
    intros.
    icase sbst. icase sbst'. icase sbst''. icase x. icase x0. icase x1. unfold upd_subst, sbst_var in *. simpl in *.
    revert H.
    case (eq_dec v v0); simpl. destruct o; destruct o0; simpl.
    case (eq_dec v2 v3); disc; intros. inv H. simpl. split; intros.
    rewrite upd_eq. split; intros.
    rewrite H. rewrite upd_eq'. trivial.
    rewrite upd_neq in H; auto.
    intro. apply n0. rewrite H0. trivial.
    split; intros. tauto.
    intro. icase H. apply n. inv H...
    icase H. congr.
    intros. inv H. simpl.
    split; intros. rewrite upd_eq. split; trivial.
    split; intros. icase H.
    intro. icase H. unfold sbst_var in *;simpl in *. congr.
    intros. inv H. simpl.
    split; intros. rewrite upd_eq.
    split; intro. rewrite <- H. rewrite upd_eq'. trivial.
    rewrite H. rewrite upd_neq; trivial. congr.
    split; intros. icase H. intro. icase H. unfold sbst_var in *;simpl in *. congr.
    case (eq_dec s0 s1); disc.
    icase o0. case (eq_dec v v2).
    icase o. case (eq_dec v0 v3); disc. simpl. intros.
    inv H. split; intros.
    rewrite upd_eq.
    rewrite upd_neq; auto. tauto.
    split; intros. icase H. simpl in H. icase H. simpl.
    intro. icase H; congr. icase H; congr.
    simpl. intros. inv H.
    split; intros. rewrite upd_eq. rewrite upd_neq; auto. tauto.
    split; intros. icase H. intro. icase H.
    case (eq_dec v0 v2); disc. simpl. intros.
    inv H. unfold sbst_object. simpl.
    split; intros. rewrite upd_neq; auto. rewrite upd_neq; auto. tauto.
    split; intros. icase o. simpl. tauto.
    intro. icase H. icase H.
    unfold sbst_object. simpl.
    split; intros. inv H. rewrite upd_neq; auto. tauto.
    inv H. simpl. split; intros. icase o. icase H. simpl. tauto.
    intro. icase H.
  Qed.

  Lemma subst_substitution_valid: forall sbst sbst',
    subst sbst sbst' = Simpler tt ->
    forall ctx, eval (upd_subst ctx sbst) sbst'.
  Proof.
    intros.
    icase sbst. icase sbst'. icase x. icase x0. unfold subst_substitution, upd_subst, sbst_var in *. simpl in *.
    revert H. case (eq_dec v v0); disc. icase o. icase o0. case (eq_dec v1 v2); disc. simpl. intros. subst.
    rewrite upd_eq. rewrite upd_eq'. trivial.
    icase o0. case (eq_dec s0 s1); disc. simpl. intros. subst. rewrite upd_eq. trivial.
    icase o0. case (eq_dec v v1). icase o. case (eq_dec v0 v2); disc. simpl. intros. subst. rewrite upd_eq, upd_eq'. trivial.
    case (eq_dec v0 v1); disc. simpl. intros. subst. unfold sbst_object. simpl. trivial.
  Qed.

  Lemma subst_substitution_unsat: forall sbst sbst',
    subst_substitution sbst sbst' = Absurd ->
    forall ctx, ~eval (upd_subst ctx sbst) sbst'.
  Proof.
    intros.
    icase sbst. icase sbst'. icase x. icase x0. unfold subst_substitution, upd_subst, sbst_var in *. simpl in *.
    revert H. case (eq_dec v v0); disc. icase o. icase o0. case (eq_dec v1 v2); disc.
    icase o0. case (eq_dec s0 s1); disc. intros. subst. unfold sbst_object. simpl. rewrite upd_eq. congr.
    icase o0. case (eq_dec v v1). icase o. case (eq_dec v0 v2); disc.
    case (eq_dec v0 v1); disc.
  Qed.

  Implicit Arguments inl [A B].
  Implicit Arguments inr [A B].

  Fixpoint subst_substitution_list (sbst : substitution) (sbst_list : list substitution) : option (list substitution) :=
    match sbst_list with
     | nil => Some nil
     | sbst1::sbst_list' => 
       match subst sbst sbst1 with
        | Absurd => None
        | Simpler tt => subst_substitution_list sbst sbst_list'
        | Same sbst1' => 
          match subst_substitution_list sbst sbst_list' with
           | None => None
           | Some sbst_list'' => Some (sbst1'::sbst_list'')
          end
       end
    end.
  Instance substab_substitution_list : substable (list substitution) (option (list substitution))  :=
    Substable subst_substitution_list.

  Lemma subst_substitution_list_Some: forall sbst sbst_list sbst_list',
    subst sbst sbst_list = Some sbst_list' ->
    (forall ctx, 
      eval (upd_subst ctx sbst) sbst_list <->  
      eval ctx sbst_list') /\
    (forall x', In x' (vars sbst_list') -> 
      In x' ((vars (sbst_object sbst)) ++ (vars sbst_list))) /\
    ~In (sbst_var sbst) (vars sbst_list').
  Proof with try tauto.
    induction sbst_list; repeat intro; simpl in *.
    inv H. simpl. split. intro. tauto. tauto. (* rewrite <- subst_object_upd. rewrite subst_object_id. rewrite upd_context_eq. tauto. tauto. *)
    revert H. case_eq (subst_substitution sbst a); intros; disc.
    destruct u. spec IHsbst_list sbst_list' H0. destruct IHsbst_list. split. intro ctx. spec H1 ctx.
    rewrite <- H1. firstorder; eapply subst_substitution_valid; eauto.
    destruct H2. split; auto. intros. spec H2 x' H4.
    apply in_app_or in H2. apply in_or_app. destruct H2; auto. right. simpl. rewrite in_app_iff; auto.
    revert H0. case_eq (subst_substitution_list sbst sbst_list); disc; intros.
    apply subst_substitution_equiv in H. destruct H. 
    inv H1. simpl. spec IHsbst_list l H0. destruct IHsbst_list.
    split. intro ctx. rewrite H. rewrite <- H1. firstorder.
    destruct H3. split. intros. 
    assert (In x' ((vars s0)++(vars l))) by (simpl;tauto).
    rewrite in_app_iff in H6. destruct H6.
    destruct H2. spec H2 x' H6. simpl. simpl in *. repeat rewrite in_app_iff in *.
    simpl in *. rewrite in_app_iff...
    spec H3 x' H6. simpl in *. repeat rewrite in_app_iff in *.
    simpl in *. rewrite in_app_iff...
    destruct H2. intro. simpl in *. rewrite in_app_iff in *...
  Qed.

  Lemma subst_substitution_list_None: forall sbst sbst_list,
    subst sbst sbst_list = None ->
    forall ctx, ~eval (upd_subst ctx sbst) sbst_list.
  Proof.
    induction sbst_list. intros. inv H.
    simpl. case_eq (subst_substitution sbst a); disc; intro.
    repeat intro.
    apply subst_substitution_unsat with (ctx := ctx) in H. tauto.
    destruct u. repeat intro. destruct H1.
    eapply IHsbst_list; eauto.
    case_eq (subst_substitution sbst a); disc.
    case_eq (subst_substitution_list sbst sbst_list); disc.
    repeat intro. inv H1. destruct H3.
    eapply IHsbst_list; eauto.
  Qed.

  Lemma subst_substitution_list_length: forall sbst sbst_list sbst_list',
    subst sbst sbst_list = Some sbst_list' -> length sbst_list >= length sbst_list'.
  Proof.
    induction sbst_list; simpl; intros. 
    inv H; auto.
    revert H; case_eq (subst_substitution sbst a); disc; intro.
    destruct u; intros.
    spec IHsbst_list sbst_list' H0. omega.
    case_eq (subst_substitution_list sbst sbst_list); disc; intros.
    inv H1.
    spec IHsbst_list l H. simpl. omega.
  Qed.

  Import Share.

  Definition simpl_equation (eqn : equation) : 
    result equation (unit + (substitution + (substitution * substitution))) :=
    match eqn with 
      (* 3 constants *)
      | (Cobject c1, Cobject c2, Cobject c3) => 
         match add c1 c2 with 
          | None => Absurd 
          | Some c3' => if eq_dec c3 c3' then Simpler (inl tt) else Absurd
(* A bug! | Some c3' => if eq_dec c3 c3' then Absurd else Simpler (inl tt) *)
         end
      (* 2 constants, 3 cases, can always simplify *)
      | (Cobject c1, Cobject c2, Vobject v3) =>
         match add c1 c2 with
          | None => Absurd
          | Some c3 => Simpler (inr (inl (mkCsubstitution v3 c3)))
         end
      | (Cobject c1, Vobject v2, Cobject c3) =>
         match sub c3 c1 with
          | None => Absurd
          | Some c2 => Simpler (inr (inl (mkCsubstitution v2 c2)))
         end
      | (Vobject v1, Cobject c2, Cobject c3) =>
         match sub c3 c2 with
          | None => Absurd
          | Some c1 => Simpler (inr (inl (mkCsubstitution v1 c1)))
         end
      (* 1 constant, can simplify in a few special cases *)
      | (Cobject c1, Vobject v2, Vobject v3) =>
         if eq_dec c1 Share.bot then 
           match eq_dec v2 v3 with
            | left _ => Simpler (inl tt)
            | right pf => Simpler (inr (inl (mkVsubstitution v2 v3 pf)))
           end
(*           if eq_dec v2 v3 then Simpler (inl tt) else Simpler (inr (inl (v2, Vobject v3))) *)
         else if eq_dec c1 Share.top then
           Simpler (inr (inr ((mkCsubstitution v2 Share.bot), (mkCsubstitution v3 Share.top))))
         else Same eqn
      | (Vobject v1, Cobject c2, Vobject v3) =>
         if eq_dec c2 Share.bot then 
           match eq_dec v1 v3 with
            | left _ => Simpler (inl tt)
            | right pf => Simpler (inr (inl (mkVsubstitution v1 v3 pf)))
           end
(*           if eq_dec v1 v3 then Simpler (inl tt) else Simpler (inr (inl (v1, Vobject v3))) *)
         else if eq_dec c2 Share.top then
           Simpler (inr (inr ((mkCsubstitution v1 Share.bot), (mkCsubstitution v3 Share.top))))
         else Same eqn
      | (Vobject v1, Vobject v2, Cobject c3) =>
         if eq_dec c3 Share.bot then
           if eq_dec v1 v2 then Simpler (inr (inl (mkCsubstitution v1 Share.bot)))
           else Simpler (inr (inr ((mkCsubstitution v1 Share.bot), (mkCsubstitution v2 Share.bot))))
         else if eq_dec v1 v2 then
           Absurd (* v1 = v2 but c3 <> bot *)
         else Same eqn
      (* no constants, can simplify in a few special cases *)
      | (Vobject v1, Vobject v2, Vobject v3) =>
        if eq_dec v1 v3 then
          Simpler (inr (inl (mkCsubstitution v2 Share.bot)))
        else if eq_dec v2 v3 then
          Simpler (inr (inl (mkCsubstitution v1 Share.bot)))
        else if eq_dec v1 v2 then
          Simpler (inr (inr ((mkCsubstitution v1 Share.bot), (mkCsubstitution v3 Share.bot))))
        else
          Same eqn
  end.

  Lemma simpl_equation_equiv: forall eqn eqn',
    simpl_equation eqn = Same eqn' -> 
    equiv_eval eqn eqn' /\
    forall x, In x (vars eqn') -> In x (vars eqn).
  Proof with try (split; try apply equiv_refl; auto).
    intros [[fp1 fp2] fp3] [[fp4 fp5] fp6] ?.
    icase fp1; icase fp2; icase fp3; simpl in H; revert H.
    case (eq_dec v v1). intros; disc.
    case (eq_dec v0 v1). intros; disc.
    case (eq_dec v v0); intros; disc.
    inv H...
    case (eq_dec s0 bot).
    case (eq_dec v v0); disc.
    case (eq_dec v v0); intros; disc.
    inv H... 
    case (eq_dec s0 bot). case (eq_dec v v0); intros; disc.
    case (eq_dec s0 top); intros; disc.
    inv H...
    case (sub s1 s0); intros; disc.
    case (eq_dec s0 bot). case (eq_dec v v0); intros; disc.
    case (eq_dec s0 top); intros; disc.
    inv H...
    case (sub s1 s0); intros; disc.
    case (add s0 s1); intros; disc.
    case (add s0 s1); intro; disc.
    case (eq_dec s2 c); intros; disc.
  Qed.

  Lemma bot_join : forall t, join bot t t.
  Proof with try tauto.
   intros.
   generalize (bot_correct' t0);intro.
   destruct H as [t1 H].
   generalize (bot_identity _ _ H);intro.
   subst...
  Qed.

  Lemma join_top : forall t1 t2, join top t1 t2 -> t1 = bot /\ t2 = top.
  Proof with try tauto.
   intros.
   destruct H.
   rewrite glb_commute in H.
   rewrite glb_top in H.
   rewrite lub_commute in H0.
   rewrite lub_top in H0.
   subst...
  Qed.

  Lemma simpl_equation_reduce1: forall eqn eq,
    simpl_equation eqn = Simpler (inr (inl eq)) ->
      (forall ctx, eval ctx eqn <-> eval ctx eq) /\
      (forall x, In x (vars eq) -> In x (vars eqn)).
  Proof.
    intros [[fp1 fp2] fp3] [fp4 fp5] ?.
    icase fp1; icase fp2; icase fp3; simpl in H; revert H.
    case (eq_dec v v1). intros.
    inv H. simpl. split.
    split; intro.
    apply join_comm in H. apply unit_identity in H.
    apply identity_share_bot in H. trivial.
    rewrite H. apply join_comm. apply bot_join.
    intros. destruct H; contr; auto.
    case (eq_dec v0 v1). intros.
    inv H. simpl. split.
    split; intro.
    apply unit_identity in H. apply identity_share_bot in H. trivial.
    rewrite H. apply bot_join.
    intros. destruct H; contr; auto.
    case (eq_dec v v0); disc.
    case (eq_dec s0 bot); disc.
    case (eq_dec v v0); disc.
    intros. inv H. simpl. split.
    split; intro.
    generalize (split_identity _ _ H bot_identity); intro.
    apply identity_share_bot in H0. trivial.
    rewrite H. apply bot_join.
    intros. destruct H; contr; auto.
    case (eq_dec s0 bot).
    case (eq_dec v v0); disc; intros.
    case (eq_dec v v0); disc; intros.
    case (eq_dec s0 bot).
    case (eq_dec v v0); disc; intros.
    inv H. simpl. split.
    split; intro.
    apply (bot_identity _ _ (join_comm H)).
    rewrite H. apply join_comm. apply bot_join.
    intros. destruct H; contr; auto.
    case (eq_dec s0 top); disc.
    case_eq (sub s1 s0); disc; intros.
    inv H0. simpl. split; auto.
    rewrite sub_join in H.
    split; intro.
    generalize (join_canc (join_comm H) H0). auto.
    subst c. auto.
    case (eq_dec s0 bot). case (eq_dec v v0); disc; intros.
    inv H. simpl. split.
    split; intro.
    apply (bot_identity _ _ H).
    rewrite H. apply bot_join.
    intros. destruct H; auto.
    case (eq_dec s0 top); disc.
    case_eq (sub s1 s0); disc; intros.
    inv H0. simpl. split; auto.
    rewrite sub_join in H.
    split; intro. 
    apply (@join_canc _ _ _ (ctx v) c s0 s1). 
    apply join_comm;trivial.
    apply join_comm;trivial.
    subst; auto.
    case_eq (add s0 s1); disc; intros.
    inv H0. simpl. split; auto.
    rewrite add_join in H.
    split; intro.
    eapply join_eq; eauto.
    subst; eauto.
    case_eq (add s0 s1); disc; intro.
    case (eq_dec s2 c); disc.
  Qed.

  Lemma simpl_equation_reduce2: forall eqn eq1 eq2,
    simpl_equation eqn = Simpler (inr (inr (eq1, eq2))) ->
      (forall ctx, eval ctx eqn <-> eval ctx eq1 /\ eval ctx eq2) /\
      (forall x, In x ((vars eq1) ++ (vars eq2)) -> In x (vars eqn)).
  Proof.
    intros [[fp1 fp2] fp3] [fp4 fp5] [fp6 fp7] ?.
    icase fp1; icase fp2; icase fp3; simpl in H; revert H.
    case (eq_dec v v1); disc.
    case (eq_dec v0 v1); disc.
    case (eq_dec v v0); disc.
    intros. subst v0. inv H. simpl. split; [| firstorder].
    split; intro.
    generalize (@join_self Share.t _ _ _ _ H); intro.
    rewrite <- H0 in *.
    apply unit_identity in H. apply identity_share_bot in H. tauto.
    destruct H. rewrite H, H0. apply bot_join.
    case (eq_dec s0 bot); disc.
    case (eq_dec v v0); disc.
    intros.
    inv H. simpl. split; [| firstorder].
    split; intro.
    generalize (split_identity _ _ H bot_identity); intro.
    generalize (split_identity _ _ (join_comm H) bot_identity); intro.
    split; apply identity_share_bot; trivial.
    destruct H. rewrite H, H0. apply bot_join.
    case (eq_dec v v0); disc.
    case (eq_dec v v0); disc.
    case (eq_dec s0 bot); disc.
    case (eq_dec s0 top); disc; intros.
    inv H; simpl. split; [| firstorder].
    split; intro.
    apply join_comm, join_top in H. trivial.
    destruct H.
    rewrite H0 in H. apply nontrivial in H; contr.
    case (eq_dec s0 bot); disc.
    case (eq_dec s0 top); disc; intros.
    inv H. simpl. split; [| firstorder].
    split; intro.
    apply join_comm, join_top in H; trivial.
    destruct H.
    rewrite H, H0. apply bot_join.
    case (sub s1 s0); disc.
    case (eq_dec s0 bot). case (eq_dec v v0); disc. case (eq_dec s0 top); disc; intros.
    inv H. simpl. split; [| firstorder].
    split; intro.
    apply join_top in H; trivial.
    destruct H; rewrite H, H0. apply join_comm. apply bot_join.
    case (sub s1 s0); disc.
    case (add s0 s1); disc.
    case (add s0 s1); disc; intro.
    case (eq_dec s2 c); disc.
  Qed.

  Lemma simpl_equation_valid: forall eqn,
    simpl_equation eqn = Simpler (inl tt) ->
    valid eqn.
  Proof.
    intros [[fp1 fp2] fp3] ?.
    icase fp1; icase fp2; icase fp3; simpl in H; revert H.
    case (eq_dec v v1); disc. case (eq_dec v0 v1); disc. case (eq_dec v v0); disc.
    case (eq_dec s0 bot); disc. case (eq_dec v v0); disc. case (eq_dec v v0); disc.
    case (eq_dec s0 bot).
    case (eq_dec v v0); disc; intros.
    subst. intro. simpl. apply join_comm. apply bot_join.
    case (eq_dec s0 top); disc.
    case (sub s1 s0); disc.
    case (eq_dec s0 bot).
    case (eq_dec v v0); disc; intros.
    subst. intro. simpl. apply bot_join.
    case (eq_dec s0 top); disc.
    case (sub s1 s0); disc.
    case (add s0 s1); disc.
    case_eq (add s0 s1); disc; intro.
    case (eq_dec s2 c); disc ; intros.
    subst s2.
    rewrite add_join in H. intro. simpl. trivial.
  Qed.

  Lemma simpl_equation_unsat: forall eqn,
    simpl_equation eqn = Absurd ->
    ~SAT eqn.
  Proof.
    intros [[fp1 fp2] fp3] ?.
    icase fp1; icase fp2; icase fp3; simpl in H; revert H.
    case (eq_dec v v1); disc. case (eq_dec v0 v1); disc. case (eq_dec v v0); disc.
    case (eq_dec s0 bot); disc. case (eq_dec v v0); disc.
    case (eq_dec v v0); disc; intros.
    intro. destruct H0. subst v0. simpl in H0.
    generalize (@join_self _ _ _ _ _ H0). intro. rewrite H1 in H0.
    apply unit_identity in H0. apply identity_share_bot in H0. contr.
    case (eq_dec s0 bot).
    case (eq_dec v v0); disc.
    case_eq (eq_dec s0 top); disc.
    case_eq (sub s1 s0); disc; intros.
    intro. destruct H1. simpl in H1.
    apply join_comm in H1.
    rewrite <- sub_join in H1. rewrite H in H1; disc.
    case (eq_dec s0 bot). case (eq_dec v v0); disc. case (eq_dec s0 top); disc.
    case_eq (sub s1 s0); disc; intros.
    intros [? ?]. simpl in H1.
    rewrite <- sub_join in H1. rewrite H in H1; disc.
    case_eq (add s0 s1); disc; intros.
    intros [? ?]. simpl in H1.
    rewrite <- add_join in H1. rewrite H in H1; disc.
    case_eq (add s0 s1); intro.
    case (eq_dec s2 c); disc; intros.
    intros [? ?]. simpl in H1.
    rewrite <- add_join in H1. rewrite H in H1. inv H1. apply n; trivial.
    intros ? [? ?]. simpl in H1.
    rewrite <- add_join in H1. rewrite H in H1. inv H1.
  Qed.

  Definition subst_equation (sbst : substitution) (eqn : equation) :
    result equation (unit + (substitution + (substitution * substitution))) :=
    match eqn with (fp1, fp2, fp3) => 
     simpl_equation (subst sbst fp1, subst sbst fp2, subst sbst fp3) 
    end.
  Instance substable_equation : substable equation (result equation (unit + (substitution + (substitution * substitution)))):=
   Substable subst_equation.

  Lemma subst_equation_equiv: forall sbst (eqn eqn' :equation),
    subst sbst eqn = Same eqn' ->
      (forall ctx, eval ctx eqn' <-> eval (upd_subst ctx sbst) eqn) /\
      (forall x', In x' (vars eqn') -> In x' ((vars (sbst_object sbst)) ++ (vars eqn))) /\
      ~In (sbst_var sbst) (vars eqn').
  Proof.
    intros.
    change subst with subst_equation in H.
    unfold subst_equation in H.
    change subst with subst_object in *. 
    destruct eqn as [[? ?] ].
    destruct sbst. destruct x.
    apply simpl_equation_equiv in H.
    destruct H. split.
    intro ctx. spec H ctx.
    rewrite <- H. unfold eval,eval_equation.
    do 3 rewrite <- subst_object_upd. tauto.
    remember (subst_object (exist _ (v, o2) n) o). symmetry in Heqo3.
    apply subst_object_vars in Heqo3. destruct Heqo3.
    remember (subst_object (exist _ (v, o2) n) o0). symmetry in Heqo4.
    apply subst_object_vars in Heqo4. destruct Heqo4.
    remember (subst_object (exist _ (v, o2) n) o1). symmetry in Heqo5.
    apply subst_object_vars in Heqo5. destruct Heqo5.
    unfold sbst_var in *. simpl in *.
    split.
    intros. spec H0 x' H7.
    apply in_app_or in H0. destruct H0.
    spec H1 x' H0. rewrite app_assoc.
    apply in_or_app. icase H1. subst x'. contr.
    apply in_app_or in H0. destruct H0.
    spec H3 x' H0.
    apply in_or_app. destruct H3. subst x'. contr.
    apply in_app_or in H3. destruct H3; auto. right. apply in_or_app. 
    right. apply in_or_app; auto.
    spec H5 x' H0. destruct H5. subst x'. contr.
    apply in_or_app. apply in_app_or in H5. destruct H5; auto.
    right.
    apply in_or_app. right. apply in_or_app; auto.
    intro.
    spec H0 v H7.
    apply in_app_or in H0. icase H0.
    apply in_app_or in H0. icase H0.
    trivial. trivial. trivial.
  Qed.

  Lemma subst_equation_reduce1: forall sbst eqn eq1,
    subst sbst eqn = Simpler (inr (inl eq1)) ->
      (forall ctx, eval ctx eq1 <-> eval (upd_subst ctx sbst) eqn) /\
      (forall x', In x' (vars eq1) -> In x' ((vars (sbst_object sbst)) ++ (vars eqn))) /\
      ~In (sbst_var sbst) (vars eq1).
  Proof.
    intros.
    change subst with subst_equation in *.
    unfold subst_equation in H.
    change subst with subst_object in *. 
    destruct sbst as [[? ?] ?]. destruct eqn as [[? ?] ?].
    apply simpl_equation_reduce1 in H. destruct H. split.
    intro ctx. spec H ctx.
    rewrite <- H. unfold eval,eval_equation.
    do 3 rewrite <- subst_object_upd. tauto.
    remember (subst_object (exist _ (v, o) n) o0). symmetry in Heqo3.
    apply subst_object_vars in Heqo3. destruct Heqo3.
    remember (subst_object (exist _ (v, o) n) o1). symmetry in Heqo4.
    apply subst_object_vars in Heqo4. destruct Heqo4.
    remember (subst_object (exist _ (v, o) n) o2). symmetry in Heqo5.
    apply subst_object_vars in Heqo5. destruct Heqo5.
    unfold sbst_var in *. simpl in *.
    split. intros.
    spec H0 x' H7.
    apply in_app_or in H0. destruct H0.
    spec H1 x' H0. destruct H1. subst x'. contr.
    rewrite app_assoc. apply in_or_app; auto.
    apply in_app_or in H0. destruct H0.
    spec H3 x' H0. destruct H3. subst x'. contr.
    apply in_app_or in H3. apply in_or_app; destruct H3; auto.
    right. apply in_or_app. right. apply in_or_app; auto.
    spec H5 x' H0. destruct H5. subst x'. contr.
    apply in_app_or in H5. apply in_or_app; destruct H5; auto.
    right. apply in_or_app. right. apply in_or_app; auto.
    intro.
    spec H0 v H7.
    apply in_app_or in H0. destruct H0. contr.
    apply in_app_or in H0; firstorder. 
    trivial. trivial. trivial.
  Qed.

  Lemma subst_equation_reduce2: forall sbst eqn sbst' sbst'',
    subst sbst eqn = Simpler (inr (inr (sbst', sbst''))) ->
      (forall ctx, eval ctx sbst' /\ eval ctx sbst'' <-> 
                   eval (upd_subst ctx sbst) eqn) /\
      (forall x', In x' ((vars sbst') ++ (vars sbst'')) -> 
                  In x' ((vars (sbst_object sbst)) ++ (vars eqn))) /\
      ~In (sbst_var sbst) ((vars sbst') ++ (vars sbst'')).
  Proof.
    intros.
    change subst with subst_equation in *.
    unfold subst_equation in H.
    change subst with subst_object in *. 
    destruct sbst as [[? ?] ?]. destruct eqn as [[? ?] ?].
    apply simpl_equation_reduce2 in H. destruct H. split.
    intro ctx. spec H ctx.
    rewrite <- H. unfold eval,eval_equation.
    do 3 rewrite <- subst_object_upd. tauto.
    remember (subst_object (exist _ (v, o) n) o0). symmetry in Heqo3.
    apply subst_object_vars in Heqo3. destruct Heqo3.
    remember (subst_object (exist _ (v, o) n) o1). symmetry in Heqo4.
    apply subst_object_vars in Heqo4. destruct Heqo4.
    remember (subst_object (exist _ (v, o) n) o2). symmetry in Heqo5.
    apply subst_object_vars in Heqo5. destruct Heqo5.
    unfold sbst_var in *. simpl in *.
    split. intros.
    spec H0 x' H7.
    apply in_app_or in H0. destruct H0.
    spec H1 x' H0. destruct H1. subst x'; contr.
    rewrite app_assoc. apply in_or_app; auto.
    apply in_app_or in H0. destruct H0.
    spec H3 x' H0. destruct H3. subst x'; contr.
    apply in_app_or in H3. apply in_or_app.
    destruct H3; auto. right. apply in_or_app. right. apply in_or_app; auto.
    spec H5 x' H0. destruct H5. subst x'. contr.
    apply in_app_or in H5. apply in_or_app.
    destruct H5; auto. right. apply in_or_app. right. apply in_or_app; auto.
    intro.
    spec H0 v H7.
    apply in_app_or in H0. destruct H0; contr.
    apply in_app_or in H0. destruct H0; contr.
    trivial. trivial. trivial.
  Qed.

  Lemma subst_equation_valid: forall sbst eqn,
    subst sbst eqn = Simpler (inl tt) ->
    forall ctx, eval (upd_subst ctx sbst) eqn.
  Proof.
    intros.
    change subst with subst_equation in *.
    unfold subst_equation in H.
    change subst with subst_object in *. 
    destruct eqn as [[? ?] ].
    apply simpl_equation_valid in H. spec H ctx.
    unfold eval,eval_equation in *. do 3 rewrite <- subst_object_upd. trivial. 
  Qed.

  Lemma subst_equation_unsat: forall sbst eqn,
    subst sbst eqn = Absurd ->
    forall ctx, ~eval (upd_subst ctx sbst) eqn.
  Proof.
    intros.
    change subst with subst_equation in *.
    unfold subst_equation in H.
    change subst with subst_object in *. 
    destruct eqn as [[? ?] ?].
    apply simpl_equation_unsat in H.
    intro. apply H. exists ctx.
    unfold eval,eval_equation in *. do 3 rewrite <- subst_object_upd in H0. trivial.
  Qed.
  
End Share_internal_system.

Module Bool_internal_system (sv : SV) 
 (Import es : EQUATION_SYSTEM sv with Definition s := bool)
 (Import esf : BOOL_ES_FEATURES sv es).

  Definition substitution : Type :=
    {p : (var * object)%type | snd p <> Vobject (fst p)}.
  Definition sbst_var (sbst : substitution) : var := fst (projT1 sbst).
  Definition sbst_object (sbst : substitution) : object := snd (projT1 sbst).
  Program Definition mkCsubstitution (x : var) (sh : s) : substitution :=
    (x, Cobject sh).
  Next Obligation. disc. Defined.
  Program Definition mkVsubstitution (x : var) (y : var) (pf : x <> y) : substitution :=
    (x, Vobject y).
  Next Obligation. unfold fst, snd. intro. apply pf. inv H. trivial. Defined.
  
  Instance dec_eq_substitution : EqDec substitution.
  Proof.
    repeat intro. destruct a. destruct a'.
    destruct x. destruct x0.
    case (eq_dec v v0). case (eq_dec o o0).
    left. subst. apply exist_ext. trivial.
    right. intro. inv H. apply n1. trivial.
    right. intro. inv H. apply n1. trivial.
  Qed.

  Record equation_system : Type := Equation_system {
    eqs_substitutions : list substitution;
    eqs_equations     : list equation
  }.

 Program Definition eql2subst (eql : equality) : result substitution unit:=
  match eql with
  |(Vobject v, obj)
  |(obj, Vobject v)=> match eq_dec obj (Vobject v) with
                      |left _ => Simpler tt
                      |right _ => Same (v,obj)
                      end
  |(Cobject c1, Cobject c2) => match eq_dec c1 c2 with
                               |left _ => Simpler tt
                               |right _ => Absurd
                               end
  end.
  Next Obligation. intro. inv H. Defined.
  
 Fixpoint eql2subst_list (l : list equality) : option (list (substitution)) :=
  match l with
  |nil => Some nil
  |eql::l' => match eql2subst eql with
              |Same subst' => match eql2subst_list l' with 
                                    |Some l'' => Some (subst'::l'')
                                    |None => None
                                    end
              |Simpler tt => eql2subst_list l'
              |Absurd => None
              end
  end.

  Definition subst2eql (subst : substitution) : equality :=
   let (v,obj) := projT1 subst in (Vobject v,obj).
  Definition subst2eql_list := fun l =>
   fold_right (fun sbst l' => (subst2eql sbst)::l') nil l.

  Definition nzvar2subst (v : var) : substitution := 
   mkCsubstitution v true.
  Definition nzvar2subst_list (l : list var) : list substitution :=
   map nzvar2subst l.

  Definition wrapped_ses:= fun (ses : sat_equation_system) =>
   let l1 := sat_nzvars ses in
   let l2 := sat_equalities ses in
   let l3 := sat_equations ses in
    match eql2subst_list l2 with
    |None => None
    |Some l2' => Some (Equation_system ((nzvar2subst_list l1)++l2') l3)
    end.

  Definition unwrapped_ses:= fun ses =>
   let l1 := eqs_substitutions ses in
   let l2 := eqs_equations ses in
    Sat_equation_system nil (subst2eql_list l1) l2.

  Lemma equiv_equation_comm: forall (fp1 fp2 fp3 : object),
    equiv_eval (fp1, fp2, fp3) (fp2, fp1, fp3).
  Proof with try tauto.
    repeat intro.
    simpl. 
    icase (get_obj_val rho fp1);
    icase (get_obj_val rho fp2);
    icase (get_obj_val rho fp3)...
  Qed.

  Class substable (A : Type) (B : Type) : Type := Substable 
   {subst: substitution -> A -> B}.
  Implicit Arguments Substable [A B].

  Definition eval_substitution (ctx : context) (subst : substitution) : Prop :=
    match subst with exist (x, fp) pf => ctx x = get ctx fp end.
  Instance evalable_substitution : evalable context substitution :=
    Evalable eval_substitution.
  Definition vars_subst (subst : substitution) : list var :=
   (sbst_var subst) :: (vars (sbst_object subst)).
  Instance varsable_subst : varsable substitution var :=
   Varsable vars_subst.
  Definition eval_equation_system (ctx : context) (eqs : equation_system) : Prop :=
     ctx |= (eqs_substitutions eqs) /\ ctx |= (eqs_equations eqs).
  Instance evalable_equation_system : evalable context equation_system :=
    Evalable eval_equation_system.

  Lemma eql2subst_Simpler: forall eql,
   eql2subst eql = Simpler tt ->
   valid eql.
  Proof with try tauto.
   repeat intro.
   destruct eql as [obj1 obj2].
   icase obj1;icase obj2.
   compute in H.
   destruct (sv.t_eq_dec v0 v);subst;simpl...
   inv H. simpl in H.
   destruct (eq_dec s0 s1);subst;simpl;inv H...
  Qed.

  Lemma eql2subst_Absurd: forall eql,
   eql2subst eql = Absurd ->
   forall rho, ~rho|=eql.
  Proof with try tauto.
   repeat intro.
   destruct eql as [obj1 obj2].
   icase obj1;icase obj2;compute in H.
   destruct (sv.t_eq_dec v0 v);subst;simpl;inv H...
   destruct (s_eq_dec s0 s1);inv H.
   compute in H0...
  Qed.

  Lemma eql2subst_Same: forall eql subst,
    eql2subst eql = Same subst ->
    equiv_eval eql subst.
  Proof with try tauto.
   repeat intro.
   destruct eql as [obj1 obj2].
   icase obj1;icase obj2;compute in H;
   try destruct (sv.t_eq_dec v0 v);subst;simpl;inv H...
   compute. split;intros;subst...
   destruct (s_eq_dec s0 s1);inv H1.
  Qed.

  Lemma eql2subst_list_None: forall l,
   eql2subst_list l = None -> forall rho, ~rho |= l.
  Proof with try tauto.
   induction l;repeat intro;inv H.
   destruct H0.
   remember (eql2subst a). symmetry in Heqr.
   destruct r;inv H2.
   apply eql2subst_Absurd with (rho:=rho) in Heqr...
   icase u. spec IHl H3 rho...
   remember (eql2subst_list l).
   symmetry in Heqo. icase o.
   spec IHl... spec IHl rho...
  Qed.

  Lemma eql2subst_list_Some: forall l l',
   eql2subst_list l = Some l' -> equiv_eval l l'.
  Proof with try tauto.
   induction l;repeat intro;inv H.
   simpl...
   remember (eql2subst a). symmetry in Heqr.
   destruct r;inv H1. icase u.
   apply eql2subst_Simpler in Heqr...
   spec Heqr rho. spec IHl l' H0 rho. simpl in *...
   remember (eql2subst_list l).
   symmetry in Heqo. icase o.
   inv H0. spec IHl l0. spec IHl...
   apply eql2subst_Same in Heqr.
   spec IHl rho. spec Heqr rho. simpl in *...
  Qed.

  Lemma subst2eql_eval: forall sbst,
   equiv_eval sbst (subst2eql sbst).
  Proof with try tauto.
   repeat intro.
   destruct sbst as [[? ?] ?].
   icase o;compute...
  Qed.

  Lemma subst2eql_list_eval: forall l,
   equiv_eval l (subst2eql_list l).
  Proof with try tauto.
   induction l;repeat intro;simpl...
   spec IHl rho.
   generalize (subst2eql_eval a rho);simpl;intro...
  Qed.

  Lemma nzvar2subst_eval: forall v,
   equiv_eval v (nzvar2subst v).
  Proof with try tauto.
   repeat intro.
   simpl... icase (rho v);
   split;repeat intro;disc...
  Qed.

  Lemma nzvar2subst_list_eval: forall l,
   equiv_eval l (nzvar2subst_list l).
  Proof with try tauto.
   induction l;repeat intro;simpl...
   spec IHl rho.
   generalize (nzvar2subst_eval a rho);simpl;intro...
  Qed.

  Lemma wrapped_ses_None: forall ses,
   wrapped_ses ses = None -> forall rho, ~rho|=ses.
  Proof with try tauto.
   intros.
   destruct ses as [l1 l2 l3].
   unfold wrapped_ses in H. simpl in H.
   remember (eql2subst_list l2).
   symmetry in Heqo. icase o;inv H.
   apply eql2subst_list_None with (rho:=rho) in Heqo.
   intro;apply Heqo. simpl in *.
   unfold eval_sat_equation_system in *;simpl in *...
  Qed.

  Lemma wrapped_ses_Some: forall ses ses',
   wrapped_ses ses = Some ses' -> equiv_eval ses ses'.
  Proof with try tauto.
   intros.
   destruct ses as [l1 l2 l3].
   unfold wrapped_ses in H. simpl in H.
   remember (eql2subst_list l2).
   symmetry in Heqo. icase o;inv H.
   apply eql2subst_list_Some in Heqo.
   repeat intro; simpl in *;spec Heqo rho;
   unfold eval_sat_equation_system,eval_equation_system in *;simpl in *...
   rewrite Heqo. 
   change (eval_list rho (nzvar2subst_list l1 ++ l)) with (rho |= (nzvar2subst_list l1 ++ l)).
   rewrite eval_list_app.
   generalize (nzvar2subst_list_eval l1 rho);intro.
   rewrite H...
  Qed.

  Lemma unwrapped_ses_eval: forall ses,
   equiv_eval ses (unwrapped_ses ses).
  Proof with try tauto.
   repeat intro.
   destruct ses as [l1 l2].
   generalize (subst2eql_list_eval l1 rho);simpl;intro.
   unfold eval_equation_system,eval_sat_equation_system;simpl...
  Qed.

  Definition subst_object (sbst : substitution) (fp' : object) : object :=
    match sbst, fp' with
     | _, Cobject c => Cobject c
     | exist (x, fp) _, Vobject v => if eq_dec x v then fp else Vobject v
    end.
  Instance substable_object : substable object object :=
   Substable subst_object.

  Lemma eval_subst_correct: forall (sbst : substitution) ctx,
   ctx |= sbst ->
   ctx (sbst_var sbst) = get ctx (sbst_object sbst).
  Proof.
   intros.
   destruct sbst as [[? ?] ?]. icase o.
  Qed.
 
  Lemma subst_object_id: forall sbst,
    subst sbst (sbst_object sbst) = (sbst_object sbst).
  Proof.
    destruct sbst; auto. simpl. destruct x. unfold sbst_object. simpl. 
    destruct o; auto. case (eq_dec v v0); auto.
  Qed.

  Definition upd_subst (ctx : context) (sbst : substitution) : context :=
    upd ctx (sbst_var sbst) (get ctx (sbst_object sbst)).
   
  Lemma subst_object_upd: forall sbst fp' ctx,
    get ctx (subst sbst fp') = get (upd_subst ctx sbst) fp'.
  Proof with try tauto.
    intros. destruct sbst. simpl. destruct x. destruct fp'; auto.
    unfold upd_subst, upd, sbst_var. simpl. case (eq_dec v v0); simpl...
  Qed.

  Lemma subst_object_vars: forall sbst fp' fp'',
    (sbst_object sbst <> Vobject (sbst_var sbst)) ->
    subst sbst fp' = fp'' ->
    (forall x', In x' (vars fp'') -> 
       In x' ((vars sbst) ++ (vars fp'))) /\
       ~In (sbst_var sbst) (vars fp'').
  Proof.
    repeat intro. destruct sbst. destruct x.
    icase fp'; icase fp''; unfold fst,snd in n; simpl in *.
    Focus 2.  split. intros. contradiction H1. auto.
    Focus 2. split. intros. contradiction H1. auto.
    split. intros. destruct H1. Focus 2. contradiction H1.
    subst. destruct (eq_dec v v0);subst. right. simpl. left;trivial.
    injection H0; intro;subst. right. apply in_app_iff;right. apply in_eq.
    destruct (eq_dec v v0). 
    subst. unfold sbst_object,sbst_var in *. simpl in *.
    apply neg_false. split. intros. destruct H0;trivial.
    Focus 2. auto. subst. Focus 2.
    injection H0; intro;subst.
    revert H. unfold sbst_object,sbst_var. simpl. intro.
    apply neg_false. split;auto. intro. destruct H1;subst. 
    auto. trivial.
    contradiction H. trivial.
  Qed.

  Definition subst_substitution (sbst sbst' : substitution) : result substitution unit :=
    match sbst, sbst' with
      exist (x, o) _, exist (x', o') _ =>
        if eq_dec x x' then
          match o, o' with
           | Cobject c1, Cobject c2 => if eq_dec c1 c2 then Simpler tt else Absurd
           | Cobject c1, Vobject v2 => Same (mkCsubstitution v2 c1)
           | Vobject v1, Cobject c2 => Same (mkCsubstitution v1 c2)
           | Vobject v1, Vobject v2 =>
             match eq_dec v1 v2 with
              | left _ => Simpler tt
              | right pf => Same (mkVsubstitution v1 v2 pf)
             end
          end
        else match subst sbst o' with
          | Cobject c2' => Same (mkCsubstitution x' c2')
          | Vobject v2' => 
            match eq_dec x' v2' with
             | left _ => Simpler tt
             | right pf => Same (mkVsubstitution x' v2' pf)
            end
        end
    end.
 Instance substable_substitution : substable substitution (result substitution unit) :=
  Substable subst_substitution.

  Lemma subst_substitution_equiv: forall sbst sbst' sbst'',
    subst sbst sbst' = Same sbst'' ->
      (forall ctx, eval ctx sbst'' <-> eval (upd_subst ctx sbst) sbst') /\
      (forall x, In x (vars sbst'') -> In x ((vars (sbst_object sbst)) ++ (vars sbst'))) /\
      ~In (sbst_var sbst) (vars sbst'').
  Proof with try tauto.
    intros.
    icase sbst. icase sbst'. icase sbst''. icase x. icase x0. icase x1. unfold upd_subst, sbst_var in *. simpl in *.
    revert H.
    case (eq_dec v v0); simpl. destruct o; destruct o0; simpl.
    case (eq_dec v2 v3); disc; intros. inv H. simpl. split; intros.
    rewrite upd_eq. split; intros.
    rewrite H. rewrite upd_eq'. trivial.
    rewrite upd_neq in H; auto.
    intro. apply n0. rewrite H0. trivial.
    split; intros. tauto.
    intro. icase H. apply n. inv H...
    icase H. congr.
    intros. inv H. simpl.
    split; intros. rewrite upd_eq. split; trivial.
    split; intros. icase H.
    intro. icase H. unfold sbst_var in *;simpl in *. congr.
    intros. inv H. simpl.
    split; intros. rewrite upd_eq.
    split; intro. rewrite <- H. rewrite upd_eq'. trivial.
    rewrite H. rewrite upd_neq; trivial. congr.
    split; intros. icase H. intro. icase H. unfold sbst_var in *;simpl in *. congr.
    case (eq_dec s0 s1); disc.
    icase o0. case (eq_dec v v2).
    icase o. case (eq_dec v0 v3); disc. simpl. intros.
    inv H. split; intros.
    rewrite upd_eq.
    rewrite upd_neq; auto. tauto.
    split; intros. icase H. simpl in H. icase H. simpl.
    intro. icase H; congr. icase H; congr.
    simpl. intros. inv H.
    split; intros. rewrite upd_eq. rewrite upd_neq; auto. tauto.
    split; intros. icase H. intro. icase H.
    case (eq_dec v0 v2); disc. simpl. intros.
    inv H. unfold sbst_object. simpl.
    split; intros. rewrite upd_neq; auto. rewrite upd_neq; auto. tauto.
    split; intros. icase o. simpl. tauto.
    intro. icase H. icase H.
    unfold sbst_object. simpl.
    split; intros. inv H. rewrite upd_neq; auto. tauto.
    inv H. simpl. split; intros. icase o. icase H. simpl. tauto.
    intro. icase H.
  Qed.

  Lemma subst_substitution_valid: forall sbst sbst',
    subst sbst sbst' = Simpler tt ->
    forall ctx, eval (upd_subst ctx sbst) sbst'.
  Proof.
    intros.
    icase sbst. icase sbst'. icase x. icase x0. unfold subst_substitution, upd_subst, sbst_var in *. simpl in *.
    revert H. case (eq_dec v v0); disc. icase o. icase o0. case (eq_dec v1 v2); disc. simpl. intros. subst.
    rewrite upd_eq. rewrite upd_eq'. trivial.
    icase o0. case (eq_dec s0 s1); disc. simpl. intros. subst. rewrite upd_eq. trivial.
    icase o0. case (eq_dec v v1). icase o. case (eq_dec v0 v2); disc. simpl. intros. subst. rewrite upd_eq, upd_eq'. trivial.
    case (eq_dec v0 v1); disc. simpl. intros. subst. unfold sbst_object. simpl. trivial.
  Qed.

  Lemma subst_substitution_unsat: forall sbst sbst',
    subst_substitution sbst sbst' = Absurd ->
    forall ctx, ~eval (upd_subst ctx sbst) sbst'.
  Proof.
    intros.
    icase sbst. icase sbst'. icase x. icase x0. unfold subst_substitution, upd_subst, sbst_var in *. simpl in *.
    revert H. case (eq_dec v v0); disc. icase o. icase o0. case (eq_dec v1 v2); disc.
    icase o0. case (eq_dec s0 s1); disc. intros. subst. unfold sbst_object. simpl. rewrite upd_eq. congr.
    icase o0. case (eq_dec v v1). icase o. case (eq_dec v0 v2); disc.
    case (eq_dec v0 v1); disc.
  Qed.

  Implicit Arguments inl [A B].
  Implicit Arguments inr [A B].

  Fixpoint subst_substitution_list (sbst : substitution) (sbst_list : list substitution) : option (list substitution) :=
    match sbst_list with
     | nil => Some nil
     | sbst1::sbst_list' => 
       match subst sbst sbst1 with
        | Absurd => None
        | Simpler tt => subst_substitution_list sbst sbst_list'
        | Same sbst1' => 
          match subst_substitution_list sbst sbst_list' with
           | None => None
           | Some sbst_list'' => Some (sbst1'::sbst_list'')
          end
       end
    end.
  Instance substab_substitution_list : substable (list substitution) (option (list substitution))  :=
    Substable subst_substitution_list.

  Lemma subst_substitution_list_Some: forall sbst sbst_list sbst_list',
    subst sbst sbst_list = Some sbst_list' ->
    (forall ctx, 
      eval (upd_subst ctx sbst) sbst_list <->  
      eval ctx sbst_list') /\
    (forall x', In x' (vars sbst_list') -> 
      In x' ((vars (sbst_object sbst)) ++ (vars sbst_list))) /\
    ~In (sbst_var sbst) (vars sbst_list').
  Proof with try tauto.
    induction sbst_list; repeat intro; simpl in *.
    inv H. simpl. split. intro. tauto. tauto. (* rewrite <- subst_object_upd. rewrite subst_object_id. rewrite upd_context_eq. tauto. tauto. *)
    revert H. case_eq (subst_substitution sbst a); intros; disc.
    destruct u. spec IHsbst_list sbst_list' H0. destruct IHsbst_list. split. intro ctx. spec H1 ctx.
    rewrite <- H1. firstorder; eapply subst_substitution_valid; eauto.
    destruct H2. split; auto. intros. spec H2 x' H4.
    apply in_app_or in H2. apply in_or_app. destruct H2; auto. right. simpl. rewrite in_app_iff; auto.
    revert H0. case_eq (subst_substitution_list sbst sbst_list); disc; intros.
    apply subst_substitution_equiv in H. destruct H. 
    inv H1. simpl. spec IHsbst_list l H0. destruct IHsbst_list.
    split. intro ctx. rewrite H. rewrite <- H1. firstorder.
    destruct H3. split. intros. 
    assert (In x' ((vars s0)++(vars l))) by (simpl;tauto).
    rewrite in_app_iff in H6. destruct H6.
    destruct H2. spec H2 x' H6. simpl. simpl in *. repeat rewrite in_app_iff in *.
    simpl in *. rewrite in_app_iff...
    spec H3 x' H6. simpl in *. repeat rewrite in_app_iff in *.
    simpl in *. rewrite in_app_iff...
    destruct H2. intro. simpl in *. rewrite in_app_iff in *...
  Qed.

  Lemma subst_substitution_list_None: forall sbst sbst_list,
    subst sbst sbst_list = None ->
    forall ctx, ~eval (upd_subst ctx sbst) sbst_list.
  Proof.
    induction sbst_list. intros. inv H.
    simpl. case_eq (subst_substitution sbst a); disc; intro.
    repeat intro.
    apply subst_substitution_unsat with (ctx := ctx) in H. tauto.
    destruct u. repeat intro. destruct H1.
    eapply IHsbst_list; eauto.
    case_eq (subst_substitution sbst a); disc.
    case_eq (subst_substitution_list sbst sbst_list); disc.
    repeat intro. inv H1. destruct H3.
    eapply IHsbst_list; eauto.
  Qed.

  Lemma subst_substitution_list_length: forall sbst sbst_list sbst_list',
    subst sbst sbst_list = Some sbst_list' -> length sbst_list >= length sbst_list'.
  Proof.
    induction sbst_list; simpl; intros. 
    inv H; auto.
    revert H; case_eq (subst_substitution sbst a); disc; intro.
    destruct u; intros.
    spec IHsbst_list sbst_list' H0. omega.
    case_eq (subst_substitution_list sbst sbst_list); disc; intros.
    inv H1.
    spec IHsbst_list l H. simpl. omega.
  Qed.

  Definition bool_add := fun (b1 b2 : bool) =>
   if b1 then if b2 then None else Some true
   else Some b2.
  Definition bool_sub := fun (b1 b2 : bool) =>
   if b2 then if b1 then Some false else None
   else Some b1.

  Definition simpl_equation (eqn : equation) : 
    result equation (unit + (substitution + (substitution * substitution))) :=
    match eqn with 
      (* 3 constants *)
      | (Cobject c1, Cobject c2, Cobject c3) => 
         match bool_add c1 c2 with
         |Some b => if bool_dec b c3 then Simpler (inl tt) else Absurd
         |None   => Absurd
         end
      (* 2 constants, 3 cases, can always simplify *)
      | (Cobject c1, Cobject c2, Vobject v3) =>
         match bool_add c1 c2 with
          | None => Absurd
          | Some c3 => Simpler (inr (inl (mkCsubstitution v3 c3)))
         end
      | (Cobject c1, Vobject v2, Cobject c3) 
      | (Vobject v2, Cobject c1, Cobject c3)=>
         match bool_sub c3 c1 with
          | None => Absurd
          | Some c2 => Simpler (inr (inl (mkCsubstitution v2 c2)))
         end
      (* 1 constant, can simplify in a few special cases *)
      | (Cobject c1, Vobject v2, Vobject v3) 
      | (Vobject v2, Cobject c1, Vobject v3)=>
         if (negb c1) then 
           match eq_dec v2 v3 with
            | left _ => Simpler (inl tt)
            | right pf => Simpler (inr (inl (mkVsubstitution v2 v3 pf)))
           end
(*           if eq_dec v2 v3 then Simpler (inl tt) else Simpler (inr (inl (v2, Vobject v3))) *)
         else
           Simpler (inr (inr ((mkCsubstitution v2 false), (mkCsubstitution v3 true))))
      | (Vobject v1, Vobject v2, Cobject c3) =>
         if (negb c3) then
           if eq_dec v1 v2 then Simpler (inr (inl (mkCsubstitution v1 false)))
           else Simpler (inr (inr ((mkCsubstitution v1 false), (mkCsubstitution v2 false))))
         else if eq_dec v1 v2 then
           Absurd (* v1 = v2 but c3 <> bot *)
         else Same eqn
      (* no constants, can simplify in a few special cases *)
      | (Vobject v1, Vobject v2, Vobject v3) =>
        if eq_dec v1 v3 then
          Simpler (inr (inl (mkCsubstitution v2 false)))
        else if eq_dec v2 v3 then
          Simpler (inr (inl (mkCsubstitution v1 false)))
        else if eq_dec v1 v2 then
          Simpler (inr (inr ((mkCsubstitution v1 false), (mkCsubstitution v3 false))))
        else
          Same eqn
  end.

  Lemma simpl_equation_equiv: forall eqn eqn',
    simpl_equation eqn = Same eqn' -> 
    equiv_eval eqn eqn' /\
    forall x, In x (vars eqn') -> In x (vars eqn).
  Proof with try (split; try apply equiv_refl; auto).
    intros [[fp1 fp2] fp3] [[fp4 fp5] fp6] ?.
    icase fp1; icase fp2; icase fp3; simpl in H; revert H.
    case (eq_dec v v1). intros; disc.
    case (eq_dec v0 v1). intros; disc.
    case (eq_dec v v0); intros; disc.
    inv H...
    case (negb s0).
    case (eq_dec v v0); disc.
    case (eq_dec v v0); intros; disc.
    inv H... 
    case (negb s0). case (eq_dec v v0); intros; disc.
    case s0;disc.
    case (bool_sub s1 s0); intros; disc.
    case (negb s0). case (eq_dec v v0); intros; disc.
    case s0; intros; disc.
    case (bool_sub s1 s0); intros; disc.
    case (bool_add s0 s1); intros; disc.
    case (bool_add s0 s1); intro; disc.
    case (bool_dec b s2); intros; disc.
  Qed.

  Lemma simpl_equation_reduce1: forall eqn eq,
    simpl_equation eqn = Simpler (inr (inl eq)) ->
      (forall ctx, eval ctx eqn <-> eval ctx eq) /\
      (forall x, In x (vars eq) -> In x (vars eqn)).
  Proof with try tauto.
    intros [[fp1 fp2] fp3] [fp4 fp5] ?.
    icase fp1; icase fp2; icase fp3; simpl in H; revert H.
    case (eq_dec v v1). intros.
    inv H. simpl. split.
    split; intro. icase (ctx v1);icase (ctx v0);compute in H...
    rewrite H. icase (ctx v1);compute...
    intros. destruct H; contr; auto.
    case (eq_dec v0 v1). intros.
    inv H. simpl. split.
    split; intro. icase (ctx v1);icase (ctx v);compute in H...
    rewrite H. icase (ctx v1);compute...
    intros. destruct H; contr; auto.
    case (eq_dec v v0); disc.
    case_eq (negb s0);disc...
    case (eq_dec v v0); disc.
    intros. inv H0. simpl. split. icase s0;inv H...
    intros;icase (ctx v0);compute...
    intros. destruct H0; contr; auto.
    intro. icase s0;inv H. 
    case (eq_dec v v0); disc; intros.
    case_eq (negb s0); intro;icase s0;inv H.
    case (eq_dec v v0); disc; intros.
    inv H. simpl. split.
    split; intro. icase (ctx v);icase (ctx v0);compute in H...
    inv H. icase (ctx v);compute...
    intros. destruct H; contr; auto.
    case_eq (bool_sub s1 s0); disc; intros.
    inv H0. simpl. split; auto.
    intros;icase b;icase s0;icase s1;inv H;icase (ctx v);compute...
    case_eq (negb s0); intro; icase s0;inv H.
    case (eq_dec v v0); disc; intros.
    inv H. simpl. split.
    intros. icase (ctx v);icase (ctx v0);compute...
    intros. destruct H; auto.
    case_eq (bool_sub s1 s0); disc; intros.
    inv H0. simpl. split; auto.
    intros. icase b;icase s0;icase s1;inv H;icase (ctx v);compute...
    case_eq (bool_add s0 s1); disc; intros.
    inv H0. simpl. split; auto.
    intros. icase b;icase s0;icase s1;inv H;icase (ctx v);compute;firstorder.
    case_eq (bool_add s0 s1); disc; intro.
    case (bool_dec b s2); disc.
  Qed.

  Lemma simpl_equation_reduce2: forall eqn eq1 eq2,
    simpl_equation eqn = Simpler (inr (inr (eq1, eq2))) ->
      (forall ctx, eval ctx eqn <-> eval ctx eq1 /\ eval ctx eq2) /\
      (forall x, In x ((vars eq1) ++ (vars eq2)) -> In x (vars eqn)).
  Proof with try tauto.
    intros [[fp1 fp2] fp3] [fp4 fp5] [fp6 fp7] ?.
    icase fp1; icase fp2; icase fp3; simpl in H; revert H.
    case (eq_dec v v1); disc.
    case (eq_dec v0 v1); disc.
    case (eq_dec v v0); disc.
    intros. subst v0. inv H. simpl. split; [| firstorder].
    intros. icase (ctx v);icase (ctx v1);compute;firstorder.
    case_eq (negb s0); icase s0; intro;inv H... 
    case (eq_dec v v0); disc...
    intros. inv H. simpl. split;intros...
    icase (ctx v);icase (ctx v0);compute...
    case (eq_dec v v0); disc.
    case_eq (negb s0); disc;intro;icase s0;inv H...
    case (eq_dec v v0);disc...
    intros. inv H. simpl. split;intros...
    icase (ctx v);icase (ctx v0);compute;firstorder.
    case (bool_sub s1 s0); disc.
    case_eq (negb s0);intro;icase s0;inv H. 
    case (eq_dec v v0); disc.
    intros. inv H. simpl. split;intros...
    icase (ctx v);icase (ctx v0);compute;firstorder...
    case (bool_sub s1 s0); disc.
    case (bool_add s0 s1); disc.
    case (bool_add s0 s1); disc; intro.
    case (bool_dec b s2); disc.
  Qed.

  Lemma simpl_equation_valid: forall eqn,
    simpl_equation eqn = Simpler (inl tt) ->
    valid eqn.
  Proof with try tauto.
    intros [[fp1 fp2] fp3] ?.
    icase fp1; icase fp2; icase fp3; simpl in H; revert H.
    case (eq_dec v v1); disc. case (eq_dec v0 v1); disc. case (eq_dec v v0); disc.
    case_eq (negb s0);intro;icase s0;inv H.
    case (eq_dec v v0); disc. case (eq_dec v v0); disc.
    case_eq (negb s0);intro;icase s0;inv H.
    case (eq_dec v v0); disc; intros.
    subst. intro. simpl. icase (rho v0);compute;firstorder.
    case (bool_sub s1 s0); disc.
    case_eq (negb s0);intro;icase s0;inv H.
    case (eq_dec v v0); disc; intros.
    subst. intro. simpl. icase (rho v0);compute...
    case (bool_sub s1 s0); disc.
    case (bool_add s0 s1); disc.
    case_eq (bool_add s0 s1); disc; intro.
    case (bool_dec b s2); disc ; intros.
    subst s2. icase b;inv H0;
    intro;simpl;icase s0;icase s1;inv H;compute...
  Qed.

  Lemma simpl_equation_unsat: forall eqn,
    simpl_equation eqn = Absurd ->
    ~SAT eqn.
  Proof with try tauto.
    intros [[fp1 fp2] fp3] ?.
    icase fp1; icase fp2; icase fp3; simpl in H; revert H.
    case (eq_dec v v1); disc. case (eq_dec v0 v1); disc. case (eq_dec v v0); disc.
    case_eq (negb s0);intro;icase s0;inv H.
    case (eq_dec v v0); disc.
    case (eq_dec v v0); disc; intros.
    intro. destruct H0. subst v0. simpl in H0. icase (x v);compute in H0;firstorder.
    case_eq (negb s0);intro;icase s0;inv H.
    case (eq_dec v v0); disc.
    case_eq (bool_sub s1 s0); disc; intros.
    intro. destruct H1. simpl in H1.
    icase s0;icase s1;inv H;icase (x v);compute in H1;firstorder.
    case_eq (negb s0);intro;icase s0;inv H. case (eq_dec v v0); disc. 
    case_eq (bool_sub s1 s0); disc; intros.
    intros [? ?]. simpl in H1.
    icase s0;icase s1;inv H;icase (x v); compute in H1;firstorder.
    case_eq (bool_add s0 s1); disc; intros.
    intros [? ?]. simpl in H1.
    icase s0;icase s1;inv H;icase (x v); compute in H1;firstorder.
    case_eq (bool_add s0 s1); intro.
    case (bool_dec b s2); disc; intros.
    intros [? ?]. simpl in H1.
    icase s0;icase s1;icase b;inv H;icase s2;compute in H1;firstorder.
    intros ? [? ?]. simpl in H1.
    icase s0;icase s1;inv H;icase s2;compute in H1;firstorder.
  Qed.

  Definition subst_equation (sbst : substitution) (eqn : equation) :
    result equation (unit + (substitution + (substitution * substitution))) :=
    match eqn with (fp1, fp2, fp3) => 
     simpl_equation (subst sbst fp1, subst sbst fp2, subst sbst fp3) 
    end.
  Instance substable_equation : substable equation (result equation (unit + (substitution + (substitution * substitution)))):=
   Substable subst_equation.

  Lemma subst_equation_equiv: forall sbst (eqn eqn' :equation),
    subst sbst eqn = Same eqn' ->
      (forall ctx, eval ctx eqn' <-> eval (upd_subst ctx sbst) eqn) /\
      (forall x', In x' (vars eqn') -> In x' ((vars (sbst_object sbst)) ++ (vars eqn))) /\
      ~In (sbst_var sbst) (vars eqn').
  Proof.
    intros.
    change subst with subst_equation in H.
    unfold subst_equation in H.
    change subst with subst_object in *. 
    destruct eqn as [[? ?] ].
    destruct sbst. destruct x.
    apply simpl_equation_equiv in H.
    destruct H. split.
    intro ctx. spec H ctx.
    rewrite <- H. unfold eval,eval_equation.
    do 3 rewrite <- subst_object_upd. tauto.
    remember (subst_object (exist _ (v, o2) n) o). symmetry in Heqo3.
    apply subst_object_vars in Heqo3. destruct Heqo3.
    remember (subst_object (exist _ (v, o2) n) o0). symmetry in Heqo4.
    apply subst_object_vars in Heqo4. destruct Heqo4.
    remember (subst_object (exist _ (v, o2) n) o1). symmetry in Heqo5.
    apply subst_object_vars in Heqo5. destruct Heqo5.
    unfold sbst_var in *. simpl in *.
    split.
    intros. spec H0 x' H7.
    apply in_app_or in H0. destruct H0.
    spec H1 x' H0. rewrite app_assoc.
    apply in_or_app. icase H1. subst x'. contr.
    apply in_app_or in H0. destruct H0.
    spec H3 x' H0.
    apply in_or_app. destruct H3. subst x'. contr.
    apply in_app_or in H3. destruct H3; auto. right. apply in_or_app. 
    right. apply in_or_app; auto.
    spec H5 x' H0. destruct H5. subst x'. contr.
    apply in_or_app. apply in_app_or in H5. destruct H5; auto.
    right.
    apply in_or_app. right. apply in_or_app; auto.
    intro.
    spec H0 v H7.
    apply in_app_or in H0. icase H0.
    apply in_app_or in H0. icase H0.
    trivial. trivial. trivial.
  Qed.

  Lemma subst_equation_reduce1: forall sbst eqn eq1,
    subst sbst eqn = Simpler (inr (inl eq1)) ->
      (forall ctx, eval ctx eq1 <-> eval (upd_subst ctx sbst) eqn) /\
      (forall x', In x' (vars eq1) -> In x' ((vars (sbst_object sbst)) ++ (vars eqn))) /\
      ~In (sbst_var sbst) (vars eq1).
  Proof.
    intros.
    change subst with subst_equation in *.
    unfold subst_equation in H.
    change subst with subst_object in *. 
    destruct sbst as [[? ?] ?]. destruct eqn as [[? ?] ?].
    apply simpl_equation_reduce1 in H. destruct H. split.
    intro ctx. spec H ctx.
    rewrite <- H. unfold eval,eval_equation.
    do 3 rewrite <- subst_object_upd. tauto.
    remember (subst_object (exist _ (v, o) n) o0). symmetry in Heqo3.
    apply subst_object_vars in Heqo3. destruct Heqo3.
    remember (subst_object (exist _ (v, o) n) o1). symmetry in Heqo4.
    apply subst_object_vars in Heqo4. destruct Heqo4.
    remember (subst_object (exist _ (v, o) n) o2). symmetry in Heqo5.
    apply subst_object_vars in Heqo5. destruct Heqo5.
    unfold sbst_var in *. simpl in *.
    split. intros.
    spec H0 x' H7.
    apply in_app_or in H0. destruct H0.
    spec H1 x' H0. destruct H1. subst x'. contr.
    rewrite app_assoc. apply in_or_app; auto.
    apply in_app_or in H0. destruct H0.
    spec H3 x' H0. destruct H3. subst x'. contr.
    apply in_app_or in H3. apply in_or_app; destruct H3; auto.
    right. apply in_or_app. right. apply in_or_app; auto.
    spec H5 x' H0. destruct H5. subst x'. contr.
    apply in_app_or in H5. apply in_or_app; destruct H5; auto.
    right. apply in_or_app. right. apply in_or_app; auto.
    intro.
    spec H0 v H7.
    apply in_app_or in H0. destruct H0. contr.
    apply in_app_or in H0; firstorder. 
    trivial. trivial. trivial.
  Qed.

  Lemma subst_equation_reduce2: forall sbst eqn sbst' sbst'',
    subst sbst eqn = Simpler (inr (inr (sbst', sbst''))) ->
      (forall ctx, eval ctx sbst' /\ eval ctx sbst'' <-> 
                   eval (upd_subst ctx sbst) eqn) /\
      (forall x', In x' ((vars sbst') ++ (vars sbst'')) -> 
                  In x' ((vars (sbst_object sbst)) ++ (vars eqn))) /\
      ~In (sbst_var sbst) ((vars sbst') ++ (vars sbst'')).
  Proof.
    intros.
    change subst with subst_equation in *.
    unfold subst_equation in H.
    change subst with subst_object in *. 
    destruct sbst as [[? ?] ?]. destruct eqn as [[? ?] ?].
    apply simpl_equation_reduce2 in H. destruct H. split.
    intro ctx. spec H ctx.
    rewrite <- H. unfold eval,eval_equation.
    do 3 rewrite <- subst_object_upd. tauto.
    remember (subst_object (exist _ (v, o) n) o0). symmetry in Heqo3.
    apply subst_object_vars in Heqo3. destruct Heqo3.
    remember (subst_object (exist _ (v, o) n) o1). symmetry in Heqo4.
    apply subst_object_vars in Heqo4. destruct Heqo4.
    remember (subst_object (exist _ (v, o) n) o2). symmetry in Heqo5.
    apply subst_object_vars in Heqo5. destruct Heqo5.
    unfold sbst_var in *. simpl in *.
    split. intros.
    spec H0 x' H7.
    apply in_app_or in H0. destruct H0.
    spec H1 x' H0. destruct H1. subst x'; contr.
    rewrite app_assoc. apply in_or_app; auto.
    apply in_app_or in H0. destruct H0.
    spec H3 x' H0. destruct H3. subst x'; contr.
    apply in_app_or in H3. apply in_or_app.
    destruct H3; auto. right. apply in_or_app. right. apply in_or_app; auto.
    spec H5 x' H0. destruct H5. subst x'. contr.
    apply in_app_or in H5. apply in_or_app.
    destruct H5; auto. right. apply in_or_app. right. apply in_or_app; auto.
    intro.
    spec H0 v H7.
    apply in_app_or in H0. destruct H0; contr.
    apply in_app_or in H0. destruct H0; contr.
    trivial. trivial. trivial.
  Qed.

  Lemma subst_equation_valid: forall sbst eqn,
    subst sbst eqn = Simpler (inl tt) ->
    forall ctx, eval (upd_subst ctx sbst) eqn.
  Proof.
    intros.
    change subst with subst_equation in *.
    unfold subst_equation in H.
    change subst with subst_object in *. 
    destruct eqn as [[? ?] ].
    apply simpl_equation_valid in H. spec H ctx.
    unfold eval,eval_equation in *. do 3 rewrite <- subst_object_upd. trivial. 
  Qed.

  Lemma subst_equation_unsat: forall sbst eqn,
    subst sbst eqn = Absurd ->
    forall ctx, ~eval (upd_subst ctx sbst) eqn.
  Proof.
    intros.
    change subst with subst_equation in *.
    unfold subst_equation in H.
    change subst with subst_object in *. 
    destruct eqn as [[? ?] ?].
    apply simpl_equation_unsat in H.
    intro. apply H. exists ctx.
    unfold eval,eval_equation in *. do 3 rewrite <- subst_object_upd in H0. trivial.
  Qed.
  
End Bool_internal_system.

*)

(*
Module Type EQUATION_SYSTEM_FEATURES (Import es : EQUATION_SYSTEM).
  (*EVAL*)
  Definition context := var -> share.
  Parameter eval_equality : evalable context equality.
  Parameter eval_equation : evalable context equation.
  Parameter eval_nzvars : evalable context var.
  Definition eval_sat_equation_system (ctx : context) (ses : sat_equation_system) : Prop :=
    ctx |= (sat_equalities ses) /\ 
    ctx |= (sat_equations ses) /\
    ctx |= (sat_nzvars ses).
  Instance evalable_sat_equation_system : evalable context sat_equation_system :=
    Evalable eval_sat_equation_system.
  Definition ies2ses := 
  fun (ies : impl_equation_system) => 
  Sat_equation_system (impl_nzvars ies) (impl_equalities ies) (impl_equations ies).

  Definition eval_impl_equation_system (ctx : context) (ies : impl_equation_system) : Prop:=
   e_eval ctx (impl_exvars ies) (ies2ses ies).
  Instance evalable_impl_equation : evalable context impl_equation_system :=
   Evalable eval_impl_equation_system.

  (*HEIGHT*)
  Parameter equality_height : heightable equality.
  Parameter equation_height : heightable equation.
  
  Definition ses_h := fun (ses : sat_equation_system) =>
   max (|sat_equalities ses|) (|sat_equations ses|).
  Definition ses_h_zero: is_height_zero_spec ses_h.
  Proof with tauto.
  repeat intro.
  destruct a.
  unfold ses_h;simpl.
  destruct (is_height_zero sat_equalities0); try simpl in e.
  destruct (is_height_zero sat_equations0); try simpl in e0.
  rewrite e;rewrite e0. left...
  right. intro. apply n.
  rewrite max_zero in H...
  right. intro. apply n.
  rewrite max_zero in H...
  Defined.
  Instance ses_height : heightable sat_equation_system :=
  Heightable ses_h ses_h_zero.
  Definition ies_h := fun (ies : impl_equation_system) =>
   max (|impl_equalities ies|) (|impl_equations ies|).
  Definition ies_h_zero: is_height_zero_spec ies_h.
  Proof with tauto.
  repeat intro.
  destruct a.
  unfold ies_h;simpl.
  destruct (is_height_zero impl_equalities0); try simpl in e.
  destruct (is_height_zero impl_equations0); try simpl in e0.
  rewrite e;rewrite e0. left...
  right. intro. apply n.
  rewrite max_zero in H...
  right. intro. apply n.
  rewrite max_zero in H...
  Defined.
  Instance ies_height : heightable impl_equation_system :=
  Heightable ies_h ies_h_zero.

  (*CHEIGHT*)
  Parameter var_cheight : cheightable context var.
  Parameter equality_cheight : cheightable context equality.
  Parameter equation_cheight : cheightable context equation.

  Instance ses_cheight : cheightable context sat_equation_system.
  constructor. intros ctx ses.
  destruct ses as [a b c].
  apply (max (cheight ctx a) (max (cheight ctx b) (cheight ctx b))).
  Defined.

  Instance ies_cheight : cheightable context impl_equation_system.
  constructor. intros ctx ies.
  destruct ies as [a b c d].
  apply (max (cheight ctx b) (max (cheight ctx c) (cheight ctx d))).
  Defined.

  (*VARSABLE*)
  Parameter equality_vars : varsable equality var.
  Parameter equation_vars : varsable equation var.
  
  Instance ses_vars : varsable sat_equation_system var.
  constructor. repeat intro.
  destruct X as [a b c].
  apply (a++(vars b)++(vars c)).
  Defined.
  
  Instance ies_vars : varsable impl_equation_system var.
  constructor. repeat intro.
  destruct X as [a b c d].
  apply (a++b++(vars c)++(vars d)).
  Defined.
End EQUATION_SYSTEM_FEATURES.
*)
(*
Module equation_system_features (Import sv : SV).
 
  (*EVAL*)
  Definition context := var -> share.
  Instance eval_equality : evalable context equality.
  constructor. repeat intro.
  destruct X0.
  apply (get X o = get X o0).
  Defined.
  Instance eval_equation : evalable context equation.
  constructor. repeat intro.
  destruct X0 as [[? ?] ?]. apply (join (get X o) (get X o0) (get X o1)).
  Defined.
  Instance eval_nzvars : evalable context var.
  constructor. repeat intro.
  apply (X X0 <> emptyshare).
  Defined.

  Definition eval_sat_equation_system (ctx : context) (ses : sat_equation_system) : Prop :=
    ctx |= (sat_equalities ses) /\ 
    ctx |= (sat_equations ses) /\
    ctx |= (sat_nzvars ses).
  Instance evalable_sat_equation_system : evalable context sat_equation_system :=
    Evalable eval_sat_equation_system.

  Definition ies2ses := 
  fun (ies : impl_equation_system) => 
  Sat_equation_system (impl_nzvars ies) (impl_equalities ies) (impl_equations ies).

  Definition eval_impl_equation_system (ctx : context) (ies : impl_equation_system) : Prop:=
   e_eval ctx (impl_exvars ies) (ies2ses ies).
  Instance evalable_impl_equation : evalable context impl_equation_system :=
   Evalable eval_impl_equation_system.

  (*HEIGHT*)

  Definition equality_h := fun (eql : equality) => 
   let (o1,o2) := eql in max (|o1|) (|o2|).
  Definition equality_h_zero: is_height_zero_spec equality_h.
  Proof with tauto.
  repeat intro.
  destruct a. simpl.
  destruct (is_height_zero o).
  destruct (is_height_zero o0).
  left. rewrite max_zero...
  right. rewrite max_zero...
  right. rewrite max_zero...
  Defined.
  Instance equality_height : heightable equality :=
   Heightable equality_h equality_h_zero.
  Definition equation_h := fun (eqn : equation) => 
   match eqn with (o1,o2,o3) => max (|o1|) (max (|o2|)(|o3|)) end.
  Definition equation_h_zero: is_height_zero_spec equation_h.
  Proof with tauto.
  repeat intro.
  destruct a as [[? ?] ?]. simpl.
  destruct (is_height_zero o).
  destruct (is_height_zero o0).
  destruct (is_height_zero o1).
  left. repeat rewrite max_zero...
  right. repeat rewrite max_zero...
  right. repeat rewrite max_zero...
  right. repeat rewrite max_zero...
  Defined.
  Instance equation_height : heightable equation :=
   Heightable equation_h equation_h_zero.
  
  Definition ses_h := fun (ses : sat_equation_system) =>
   max (|sat_equalities ses|) (|sat_equations ses|).
  Definition ses_h_zero: is_height_zero_spec ses_h.
  Proof with tauto.
  repeat intro.
  destruct a.
  unfold ses_h;simpl.
  destruct (is_height_zero sat_equalities0); try simpl in e.
  destruct (is_height_zero sat_equations0); try simpl in e0.
  rewrite e;rewrite e0. left...
  right. intro. apply n.
  rewrite max_zero in H...
  right. intro. apply n.
  rewrite max_zero in H...
  Defined.
  Instance ses_height : heightable sat_equation_system :=
  Heightable ses_h ses_h_zero.
  Definition ies_h := fun (ies : impl_equation_system) =>
   max (|impl_equalities ies|) (|impl_equations ies|).
  Definition ies_h_zero: is_height_zero_spec ies_h.
  Proof with tauto.
  repeat intro.
  destruct a.
  unfold ies_h;simpl.
  destruct (is_height_zero impl_equalities0); try simpl in e.
  destruct (is_height_zero impl_equations0); try simpl in e0.
  rewrite e;rewrite e0. left...
  right. intro. apply n.
  rewrite max_zero in H...
  right. intro. apply n.
  rewrite max_zero in H...
  Defined.
  Instance ies_height : heightable impl_equation_system :=
  Heightable ies_h ies_h_zero.

  (*CHEIGHT*)
  Instance var_cheight : cheightable context var.
  constructor. repeat intro. apply (|X X0|).
  Defined.
  Instance equality_cheight : cheightable context equality.
  constructor. repeat intro. destruct X0. 
  apply (max (cheight X o) (cheight X o0)).
  Defined.
  Instance equation_cheight : cheightable context equation.
  constructor. repeat intro. destruct X0 as [[? ?] ?].
  apply (max (cheight X o) (max (cheight X o0)(cheight X o1))).
  Defined.

  Instance ses_cheight : cheightable context sat_equation_system.
  constructor. intros ctx ses.
  destruct ses as [a b c].
  apply (max (cheight ctx a) (max (cheight ctx b) (cheight ctx b))).
  Defined.

  Instance ies_cheight : cheightable context impl_equation_system.
  constructor. intros ctx ies.
  destruct ies as [a b c d].
  apply (max (cheight ctx b) (max (cheight ctx c) (cheight ctx d))).
  Defined.

  (*VARSABLE*)
  Instance equality_vars : varsable equality var.
  constructor. repeat intro. destruct X.
  apply ((vars o)++(vars o0)).
  Defined.
  Instance equation_vars : varsable equation var.
  constructor. repeat intro. destruct X as [[? ?] ?].
  apply ((vars o)++(vars o0)++(vars o1)).
  Defined.
  
  Instance ses_vars : varsable sat_equation_system var.
  constructor. repeat intro.
  destruct X as [a b c].
  apply (a++(vars b)++(vars c)).
  Defined.
  
  Instance ies_vars : varsable impl_equation_system var.
  constructor. repeat intro.
  destruct X as [a b c d].
  apply (a++b++(vars c)++(vars d)).
  Defined.

End equation_system_features.
*)
(*

Module Type INTERNAL_EQUATION_SYSTEM.

  Parameter var : Type.
  Axiom var_eq_dec : EqDec var. 
  Existing Instance var_eq_dec.
  Parameter equality : Type.
  Axiom equality_eq_dec : EqDec equality.
  Existing Instance equality_eq_dec.
  Parameter equation : Type.
  Axiom equation_eq_dec : EqDec equation.
  Existing Instance equation_eq_dec.
  Definition context := var -> share.
  Parameter eval_equality : evalable context equality.
  Existing Instance eval_equality.
  Parameter eval_equation : evalable context equation.
  Existing Instance eval_equation.
  Parameter eval_nzvars : evalable context var.
  Existing Instance eval_nzvars.

  Record sat_equation_system : Type := Sat_equation_system {
    sat_nzvars        : list var;
    sat_equalities    : list equality;
    sat_equations     : list equation
  }.
  Record impl_equation_system : Type := Impl_equation_system {
    impl_nzvars     : list var;
    impl_exvars     : list var;
    impl_equalities : list equality;
    impl_equations  : list equation
  }.

  Definition eval_sat_equation_system (ctx : context) (ses : sat_equation_system) : Prop :=
    ctx |= (sat_equalities ses) /\ 
    ctx |= (sat_equations ses) /\
    ctx |= (sat_nzvars ses).
  Instance evalable_sat_equation_system : evalable context sat_equation_system :=
    Evalable eval_sat_equation_system.

  Definition ies2ses := 
  fun (ies : impl_equation_system) => 
  Sat_equation_system (impl_nzvars ies) (impl_equalities ies) (impl_equations ies).

  Definition eval_impl_equation_system (ctx : context) (ies : impl_equation_system) : Prop:=
   e_eval ctx (impl_exvars ies) (ies2ses ies).
  Instance evalable_impl_equation : evalable context impl_equation_system :=
   Evalable eval_impl_equation_system.

  Parameter cheight : context -> 
  


(* This is a modified version used internally to the solver in a way that reduces some cases *)


  Definition ies2ses := 
  fun (ies : impl_equation_system) => 
  Sat_equation_system (impl_nzvars ies) (impl_equalities ies) (impl_equations ies).

  Definition eval_impl_equation_system (ctx : context) (ies : impl_equation_system) : Prop:=
   e_eval ctx (impl_exvars ies) (ies2ses ies).

  Declare Module sv : SV.

  Definition var : Type := sv.t.
  Definition context : Type := var -> share.
  Instance cheightable_var : cheightable context var :=
    Cheightable (fun ctx v => height (ctx v)).

  (* Objects *)
  Inductive object : Type :=
    | Vobject : var -> object
    | Cobject : share -> object.

  Axiom dec_eq_object : EqDec object.
  Existing Instance dec_eq_object.

  Definition height_object (o : object) : nat :=
    match o with
     | Cobject c => height c
     | Vobject v => 0
    end.
  Axiom is_height_zero_object : is_height_zero_spec height_object. 
  Instance heightable_object : heightable object :=
    Heightable height_object is_height_zero_object.

  Definition cheight_object (ctx : context) (o : object) : nat :=
    match o with
    | Cobject c => 0
    | Vobject v => height (ctx v)
    end.
  Instance cheightable_object : cheightable context object :=
   Cheightable cheight_object.

  Definition get_object (ctx : context) (so : object) : share :=
    match so with
     | Cobject c => c
     | Vobject v => ctx v
    end.
  Instance getable_object : getable context object share :=
    Getable get_object.
  
  Definition vars_obj (obj : object) : list var :=
    match obj with
     | Cobject c => nil
     | Vobject v' => v' :: nil
   end.
  Instance varsable_obj : varsable object var :=
    Varsable vars_obj.
  (* End Objects *)
  
  (* Substitutions *)
  Definition substitution : Type :=
    {p : (var * object)%type | snd p <> Vobject (fst p)}.
  Definition sbst_var (sbst : substitution) : var := fst (projT1 sbst).
  Definition sbst_object (sbst : substitution) : object := snd (projT1 sbst).
  Program Definition mkCsubstitution (x : var) (sh : share) : substitution :=
    (x, Cobject sh).
  (*Next Obligation. disc. Qed.*)
  Program Definition mkVsubstitution (x : var) (y : var) (pf : x <> y) : substitution :=
    (x, Vobject y).
  (*Next Obligation. unfold fst, snd. intro. apply pf. inv H. trivial. Qed.*)
  
  Axiom dec_eq_substitution : EqDec substitution.
  Existing Instance dec_eq_substitution.

  Definition eval_substitution (ctx : context) (subst : substitution) : Prop :=
    match subst with exist (x, fp) pf => ctx x = get ctx fp end.
  Instance evalable_substitution : evalable context substitution :=
    Evalable eval_substitution.
  Definition height_substitution (s : substitution) : nat :=
    height (sbst_object s).
  
  Definition vars_subst (subst : substitution) : list var :=
   (sbst_var subst) :: (vars (sbst_object subst)).
  Instance varsable_subst : varsable substitution var :=
   Varsable vars_subst.

  Axiom is_height_zero_substitution : is_height_zero_spec height_substitution.
  Instance heightable_substitution : heightable substitution :=
    Heightable height_substitution is_height_zero_substitution.

  Definition cheight_substitution (ctx : context) (s : substitution) : nat :=
   max (cheight ctx ( Vobject (sbst_var s))) (cheight ctx (sbst_object s)).
  Instance cheightable_substitution : cheightable context substitution :=
    Cheightable cheight_substitution.
  
  Axiom proper_substitution: proper var share substitution.
  Existing Instance proper_substitution.
    
(* Not sure if these belong here or not... *)
  Definition upd_context (ctx : context) (sbst : substitution) : context :=
    upd ctx (sbst_var sbst) (get ctx (sbst_object sbst)).
  Axiom upd_context_eq: forall ctx sbst, 
    upd_context ctx sbst (sbst_var sbst) = get ctx (sbst_object sbst).
  Axiom upd_context_equiv: forall ctx sbst,
    ctx (sbst_var sbst) = get ctx (sbst_object sbst) ->
    upd_context ctx sbst = ctx.
  Definition upd_context_list (ctx : context) (subst_list : list substitution) : context :=
    fold_right (fun vfp ctx' => upd_context ctx' vfp) ctx subst_list.
  Axiom upd_context_list_equiv: forall ctx subst_list,
    eval_list ctx subst_list ->
    upd_context_list ctx subst_list = ctx.
(* End not sure *)

  (* Equations *)
  Definition equation : Type := 
    (object * object * object)%type.

  Definition vars_eqn (eqn :equation) : list var :=
   match eqn with (obj1,obj2,obj3) => (vars obj1) ++ (vars obj2) ++ (vars obj3) end.
  Instance varsable_eqn : varsable equation var :=
   Varsable vars_eqn.

  Definition height_equation (eqn : equation) : nat :=
    match eqn with (o1, o2, o3) =>
      max (height o1) (max (height o2) (height o3))
    end.
  Axiom is_height_zero_equation : is_height_zero_spec height_equation.
  Instance heightable_equation : heightable equation :=
    Heightable height_equation is_height_zero_equation.
  Definition cheight_equation (ctx : context)(eqn :equation) : nat :=
   match eqn with (o1,o2,o3) =>
    max (cheight ctx o1) (max (cheight ctx o2) (cheight ctx o3))
   end.
  Instance cheightable_equation : cheightable context equation :=
   Cheightable cheight_equation.
  Definition eval_equation (ctx : context) (eqn : equation) : Prop :=
    match eqn with (fp1, fp2, fp3) => 
      join (get ctx fp1) (get ctx fp2) (get ctx fp3) 
    end.
  Instance evalable_equation : evalable context equation :=
    Evalable eval_equation.
  Axiom proper_equation: proper var share equation.
  Existing Instance proper_equation.

  Record equation_system : Type := Equation_system {
    eqs_substitutions : list substitution;
    eqs_equations     : list equation
  }.
  Definition height_equation_system (eqs : equation_system) : nat :=
    max (height (eqs_substitutions eqs)) (height (eqs_equations eqs)).
  Axiom is_height_zero_equation_system : is_height_zero_spec height_equation_system.
  Instance heightable_equation_system : heightable equation_system :=
    Heightable height_equation_system is_height_zero_equation_system.
  Definition cheight_equation_system (ctx : context) (eqs : equation_system) : nat :=
    max (cheight ctx (eqs_substitutions eqs)) (cheight ctx (eqs_equations eqs)).
  Instance cheightable_equation_system : cheightable context equation_system :=
    Cheightable cheight_equation_system.  
  Definition eval_equation_system (ctx : context) (eqs : equation_system) : Prop :=
    eval ctx (eqs_substitutions eqs) /\ eval ctx (eqs_equations eqs).
  Instance evalable_equation_system : evalable context equation_system :=
    Evalable eval_equation_system.
  Definition vars_es (es : equation_system) : list var :=
    vars (eqs_substitutions es) ++ vars (eqs_equations es).
  Instance varsable_es : varsable equation_system var :=
   Varsable vars_es.  
  Axiom proper_equation_system: proper var share equation_system.
  Existing Instance proper_equation_system.

  Record top_level : Type := Top_level {
    tl_equation_system : equation_system;
    tl_exists           : list var;
    tl_nonzeros         : list var
  }.

  Definition height_top_level (tleqs : top_level) : nat :=
    height (tl_equation_system tleqs).
  Axiom is_height_zero_top_level : is_height_zero_spec height_top_level.
  Instance heightable_top_level : heightable top_level :=
    Heightable height_top_level is_height_zero_top_level.
  Definition cheight_top_level (ctx : context)(tleqs : top_level) : nat :=
    max (cheight ctx (tl_equation_system tleqs)) (cheight ctx (tl_nonzeros tleqs)).
  Instance cheightable_top_level : cheightable context top_level :=
    Cheightable cheight_top_level.
  Definition eval_var_nz (ctx : context) (v : var) : Prop :=
   ctx v <> bot.
  Instance evalable_var_nz : evalable context var := Evalable eval_var_nz.
  Definition eval_top_level (ctx : context) (tleqs : top_level) : Prop :=
    exists ctx',
      [(tl_exists tleqs) => ctx'] ctx |= (tl_equation_system tleqs) /\
      [(tl_exists tleqs) => ctx'] ctx |= (tl_nonzeros tleqs).
  Instance evalable_top_level : evalable context top_level :=
    Evalable eval_top_level.

  Record top_es : Type := Top_es {
    tes_equation_system : equation_system;
    tes_exists          : list var
  }.
  Definition height_top_es (tes : top_es) : nat :=
    height (tes_equation_system tes).
  Axiom is_height_zero_top_es : is_height_zero_spec height_top_es.
  Instance heightable_top_es : heightable top_es :=
    Heightable height_top_es is_height_zero_top_es.
  Definition cheight_top_es (ctx : context)(tes : top_es) : nat :=
    cheight ctx (tes_equation_system tes).
  Instance cheightable_top_es : cheightable context top_es :=
    Cheightable cheight_top_es.
  Definition eval_top_es (ctx : context) (tes : top_es) : Prop :=
    exists ctx',
      [(tes_exists tes) => ctx'] ctx |= (tes_equation_system tes).
  Instance evalable_top_es : evalable context top_es :=
    Evalable eval_top_es.

  Definition tl2tes (tl : top_level) : top_es := 
   Top_es (tl_equation_system tl) (tl_exists tl).

  Definition eval_top_level_bounded (ctx : context) (btleqs : (top_level*nat)) : Prop :=
   exists ctx',
      match btleqs with (tleqs,n) =>
      cheight ctx' tleqs <= n /\
      [(tl_exists tleqs) => ctx'] ctx |= (tl_equation_system tleqs) /\
      [(tl_exists tleqs) => ctx'] ctx |= (tl_nonzeros tleqs)
      end.
  Instance evalable_top_level_bounded : evalable context (top_level*nat) :=
    Evalable eval_top_level_bounded.

(*

  Record ntop_level : Type := NTop_level {
    ntl_tl : top_level;
    ntl_nonzeros : list var
  }.

  Definition height_ntop_level (ntleqs : ntop_level) : nat :=
    height (ntl_tl ntleqs).
  Axiom is_height_zero_ntop_level : is_height_zero_spec height_ntop_level.
  Instance heightable_ntop_level : heightable ntop_level :=
    Heightable height_ntop_level is_height_zero_ntop_level.
  Definition cheight_ntop_level (ctx : context)(ntleqs : ntop_level) : nat :=
    max (cheight ctx (ntl_tl ntleqs)) (cheight ctx (ntl_nonzeros ntleqs)).
  Instance cheightable_ntop_level : cheightable context ntop_level :=
    Cheightable cheight_ntop_level.  
  Definition eval_nonzeros (ctx : context)(nl : list var) : Prop :=
    fold_right (fun (v : var)(P : Prop)  => P /\ ~(ctx v = bot)) True nl.
  Instance evalable_nonzeros : evalable context (list var) :=
    Evalable eval_nonzeros.
  Definition eval_ntop_level (ctx : context) (ntleqs : ntop_level) : Prop :=
    eval ctx (ntl_tl ntleqs) /\ eval ctx (ntl_nonzeros ntleqs).
  Instance evalable_ntop_level : evalable context ntop_level :=
    Evalable eval_ntop_level.
*)
End INTERNAL_EQUATION_SYSTEM.

Module Internal_Equation_System (sv' : SV)
  : INTERNAL_EQUATION_SYSTEM with Module sv := sv'.

  Module sv := sv'.

  Definition var : Type := sv.t.
  Definition context : Type := var -> share.
  Instance cheightable_var : cheightable context var :=
    Cheightable (fun ctx v => height (ctx v)).

  (* Objects *)
  Inductive object : Type :=
    | Vobject : var -> object
    | Cobject : share -> object.

  Instance dec_eq_object : EqDec object.
    unfold EqDec.
    destruct a; destruct a'.
    destruct (eq_dec v v0). left. f_equal. trivial.
    right. intro. inv H. apply n. trivial.
    right. disc.
    right. disc.
    destruct (eq_dec s s0). left. f_equal. trivial.
    right. intro. inv H. apply n. trivial.
  Defined.

  Definition height_object (o : object) : nat :=
    match o with
     | Cobject c => height c
     | Vobject v => 0
    end.
  Lemma is_height_zero_object : is_height_zero_spec height_object.
  Proof.
    hnf.
    destruct a. left. trivial. 
    simpl. case (is_height_zero s); [left | right]; trivial.
  Qed.
  Instance heightable_object : heightable object :=
    Heightable height_object is_height_zero_object.

  Definition cheight_object (ctx : context) (o : object) : nat :=
    match o with
    | Cobject c => 0
    | Vobject v => height (ctx v)
    end.
  Instance cheightable_object : cheightable context object :=
   Cheightable cheight_object.

  Definition get_object (ctx : context) (so : object) : share :=
    match so with
     | Cobject c => c
     | Vobject v => ctx v
    end.
  Instance getable_object : getable context object share :=
    Getable get_object.
  
  Definition vars_obj (obj : object) : list var :=
    match obj with
     | Cobject c => nil
     | Vobject v' => v' :: nil
   end.
  Instance varsable_obj : varsable object var :=
    Varsable vars_obj.
  
  Definition substitute_object (x y : var) (obj : object) : object :=
    match obj with
     | Cobject c => Cobject c
     | Vobject v => Vobject (if eq_dec x v then y else v) 
    end.
  Lemma substitute_object_height: forall x y o,
    height o = height (substitute_object x y o).
  Proof. intros. icase o. Qed.
  Lemma substitute_object_vars: forall x y o,
    fresh y o -> fresh x (substitute_object x y o).
  Proof.
    intros. icase o. 
    unfold substitute_object. case eq_dec; intro.
    subst v. intro. apply H. icase H0. left. auto.
    intro. icase H0.
  Qed.
  Lemma substitute_object_fresh: forall rho x y obj,
    fresh y obj -> get rho obj = get (upd rho y (rho x)) (substitute_object x y obj).
  Proof.
    intros. icase obj. simpl.
    unfold upd. case (eq_dec x v).
    intros. subst x. case eq_dec; auto.
    intro. exfalso; auto.
    case eq_dec; auto. intros.
    exfalso. apply H. left. auto.
  Qed.
  Lemma substitute_object_change_unused: forall x obj,
    fresh x obj ->
    forall rho v,
    get rho obj = get (upd rho x v) obj.
  Proof.
    intros. icase obj. simpl.
    rewrite upd_neq; auto.
    intro. subst.
    apply H. left. trivial.
  Qed.
  
  (* Substitutions *)
  Definition substitution : Type :=
    {p : (var * object)%type | snd p <> Vobject (fst p)}.
  Definition sbst_var (sbst : substitution) : var := fst (projT1 sbst).
  Definition sbst_object (sbst : substitution) : object := snd (projT1 sbst).
  Program Definition mkCsubstitution (x : var) (sh : share) : substitution :=
    (x, Cobject sh).
  (*Next Obligation. disc. Qed.*)
  Program Definition mkVsubstitution (x : var) (y : var) (pf : x <> y) : substitution :=
    (x, Vobject y).
  (*Next Obligation. unfold fst, snd. intro. apply pf. inv H. trivial. Qed.*)
  
  Instance dec_eq_substitution : EqDec substitution.
  Proof.
    repeat intro. destruct a. destruct a'.
    destruct x. destruct x0.
    case (eq_dec v v0). case (eq_dec o o0).
    left. subst. apply exist_ext. trivial.
    right. intro. inv H. apply n1. trivial.
    right. intro. inv H. apply n1. trivial.
  Qed.

  Definition eval_substitution (ctx : context) (subst : substitution) : Prop :=
    match subst with exist (x, fp) pf => ctx x = get ctx fp end.
  Instance evalable_substitution : evalable context substitution :=
    Evalable eval_substitution.
  Definition height_substitution (s : substitution) : nat :=
    height (sbst_object s).
  
  Definition vars_subst (subst : substitution) : list var :=
   (sbst_var subst) :: (vars (sbst_object subst)).
  Instance varsable_subst : varsable substitution var :=
   Varsable vars_subst.

  Lemma is_height_zero_substitution : is_height_zero_spec height_substitution.
  Proof.
    hnf.
    destruct a. destruct x. unfold height_substitution, sbst_object. simpl projT1. unfold snd.
    apply is_height_zero.
  Qed.
  Instance heightable_substitution : heightable substitution :=
    Heightable height_substitution is_height_zero_substitution.

  Definition cheight_substitution (ctx : context) (s : substitution) : nat :=
   max (cheight ctx ( Vobject (sbst_var s))) (cheight ctx (sbst_object s)).
  Instance cheightable_substitution : cheightable context substitution :=
    Cheightable cheight_substitution.

  (* Since we don't need to do this computationally, we can
     be slow and do extra comparisions. *)
  (* There might be a more elegant way to do this with 
     substitute_object, but it doesn't really matter. *)
  Definition substitute_substitution (v1 v2 : var) (s : substitution) : substitution :=
    match s with
     | exist (v, Cobject c) _ => 
         if eq_dec v v1 then mkCsubstitution v2 c else s
     | exist (v, Vobject v') _ => 
         let vx := if eq_dec v v1 then v2 else v in
         let vy := if eq_dec v' v1 then v2 else v' in
         match eq_dec vx vy with
          | left _ => s (* v2 was not fresh! *)
          | right pf => mkVsubstitution vx vy pf
         end
    end.
  Instance proper_substitution: proper var share substitution.
  Proof.
    apply Proper with substitute_substitution.
    (* prop 1 *)
    destruct c; auto. simpl. destruct x.
    icase o; case eq_dec; auto.
    (* prop 2 *)
    repeat intro.
    destruct obj. destruct x0. destruct o. red in H. unfold IN in *. simpl in *.
    unfold sbst_var in H; simpl in H.
    revert H0. case eq_dec; case eq_dec; case eq_dec; unfold sbst_var, sbst_object; simpl; intros; subst; try tauto.
    destruct H0. auto. destruct H0; auto.
    destruct H0. auto. destruct H0; auto.
    red in H. unfold IN in *. simpl in *. unfold sbst_var, sbst_object, fst, snd in *.
    revert H0. case eq_dec; simpl in *; intros.
    subst v. apply H. left. symmetry. icase H0.
    icase H0.
    (* prop 3 *)
    intros. destruct obj. destruct x0. 
    unfold fresh, IN in H. simpl in H. unfold sbst_var, sbst_object in H. simpl in H, n.
    assert (v <> y /\ ~In y (vars_obj o)) by tauto. clear H. destruct H0.
    destruct o; simpl.
    case eq_dec; case eq_dec; case eq_dec; simpl; intros; subst; try tauto;
    try rewrite upd_eq; try rewrite upd_neq; auto; try tauto.
    simpl in H0. destruct H0. auto.
    simpl in H0. 
    rewrite upd_neq; auto. tauto.
    case eq_dec; simpl; intros; subst.
    rewrite upd_eq. tauto.
    rewrite upd_neq; auto. tauto.
    (* prop 4 *)
    intros. red.
    destruct obj; icase x0; simpl in *.
    unfold fresh, IN in H. simpl in H. unfold sbst_var, sbst_object in H. simpl in H.
    assert (v0 <> x /\ ~In x (vars_obj o)) by tauto. clear H. destruct H0.
    rewrite upd_neq; auto.
    icase o; simpl.
    rewrite upd_neq. tauto. intro. apply H0. simpl. auto.
    tauto.
  Qed.

  Definition upd_context (ctx : context) (sbst : substitution) : context :=
    upd ctx (sbst_var sbst) (get ctx (sbst_object sbst)).
  Lemma upd_context_eq: forall ctx sbst, 
    upd_context ctx sbst (sbst_var sbst) = get ctx (sbst_object sbst).
  Proof.
    unfold upd_context. intros. rewrite upd_eq. trivial.
  Qed.
  Lemma upd_context_equiv: forall ctx sbst,
    ctx (sbst_var sbst) = get ctx (sbst_object sbst) ->
    upd_context ctx sbst = ctx.
  Proof.
    unfold upd_context, upd. intros.
    extensionality a'.
    case (eq_dec (sbst_var sbst) a'); intros. subst a'. rewrite H; trivial.
    trivial.
  Qed.

  Definition upd_context_list (ctx : context) (subst_list : list substitution) : context :=
    fold_right (fun vfp ctx' => upd_context ctx' vfp) ctx subst_list.
  Lemma upd_context_list_equiv: forall ctx (subst_list : list substitution),
    eval_list ctx subst_list ->
    upd_context_list ctx subst_list = ctx. 
  Proof.
    induction subst_list; simpl. trivial.
    destruct a. simpl. intros. destruct H.
    rewrite IHsubst_list; auto. destruct x.
    apply upd_context_equiv; auto.
  Qed.

  (* Equations *)
  Definition equation : Type := 
    (object * object * object)%type.

  Definition vars_eqn (eqn :equation) : list var :=
   match eqn with (obj1,obj2,obj3) => (vars obj1) ++ (vars obj2) ++ (vars obj3) end.
  Instance varsable_eqn : varsable equation var :=
   Varsable vars_eqn.

  (* Unfold fresh componentwise *)
  Lemma unfold_fresh_equation: forall v o1 o2 o3,
    fresh v (o1,o2,o3) <-> (fresh v o1 /\ fresh v o2 /\ fresh v o3).
  Proof.
    split; intros.
    unfold fresh, IN in *. simpl in *.
    split. intro. apply H. 
    apply in_or_app. auto.
    split; intro; apply H; apply in_or_app; right; apply in_or_app; auto.
    destruct H as [? [? ?]].
    intro. hnf in H2. simpl in H2.
    apply in_app_or in H2. icase H2.
    apply in_app_or in H2. icase H2.
  Qed.

  Definition height_equation (eqn : equation) : nat := 
    match eqn with (o1, o2, o3) =>
      max (height o1) (max (height o2) (height o3))
    end.
  Lemma is_height_zero_equation : is_height_zero_spec height_equation.
  Proof.
    hnf.
    destruct a as [[? ?] ?].
    unfold height_equation.
    case (is_height_zero o); intro.
    case (is_height_zero o0); intro.
    case (is_height_zero o1); intro.
    left. rewrite e, e0, e1. trivial.
    right. rewrite e, e0. simpl. trivial.
    right. rewrite e. icase (height o0); icase (height o1).
    right. icase (height o). icase (height o0); icase (height o1).
  Qed.
  Instance heightable_equation : heightable equation :=
    Heightable height_equation is_height_zero_equation.

  Definition cheight_equation (ctx : context)(eqn :equation) : nat :=
   match eqn with (o1,o2,o3) =>
    max (cheight ctx o1) (max (cheight ctx o2) (cheight ctx o3))
   end.
  Instance cheightable_equation : cheightable context equation :=
   Cheightable cheight_equation.

  Definition eval_equation (ctx : context) (eqn : equation) : Prop :=
    match eqn with (fp1, fp2, fp3) => 
      join (get ctx fp1) (get ctx fp2) (get ctx fp3) 
    end.
  Instance evalable_equation : evalable context equation :=
    Evalable eval_equation.
  
  Definition substitute_equation (v1 v2 : var) (e : equation) : equation :=
    match e with (o1, o2, o3) =>
      (substitute_object v1 v2 o1, substitute_object v1 v2 o2, substitute_object v1 v2 o3)
    end.
  Instance proper_equation: proper var share equation.
  Proof.
    apply Proper with substitute_equation.
    destruct c as [[? ?] ?]. simpl.
    do 3 rewrite <- substitute_object_height. trivial.
    destruct obj as [[? ?] ?]. simpl. intro.
    rewrite unfold_fresh_equation in *.
    destruct H as [? [? ?]].
    split. apply substitute_object_vars; auto.
    split; apply substitute_object_vars; auto.
    destruct obj as [[? ?] ?]. simpl. intro.
    rewrite unfold_fresh_equation in H. destruct H as [? [? ?]].
    do 3 (rewrite <- substitute_object_fresh; auto). tauto.
    destruct obj as [[? ?] ?]. simpl. intro.
    rewrite unfold_fresh_equation in H. destruct H as [? [? ?]].
    unfold cequiv. simpl. intros.
    do 3 (rewrite <- substitute_object_change_unused; auto). tauto.
  Qed.
    
  (* Equation Systems *)
  Record equation_system : Type := Equation_system {
    eqs_substitutions : list substitution;
    eqs_equations     : list equation
  }.

  Definition height_equation_system (eqs : equation_system) : nat :=
    max (height (eqs_substitutions eqs)) (height (eqs_equations eqs)).
  Lemma is_height_zero_equation_system : is_height_zero_spec height_equation_system.
  Proof.
    hnf.
    destruct a.
    case (is_height_zero eqs_substitutions0).
    case (is_height_zero eqs_equations0).
    left. unfold height_equation_system, eqs_substitutions, eqs_equations. rewrite e, e0. trivial.
    right. unfold height_equation_system, eqs_substitutions, eqs_equations. rewrite e. icase (height eqs_equations0).
    right. unfold height_equation_system, eqs_substitutions, eqs_equations. icase (height eqs_substitutions0); icase (height eqs_equations0).
  Qed.
  Instance heightable_equation_system : heightable equation_system :=
    Heightable height_equation_system is_height_zero_equation_system.

  Definition cheight_equation_system (ctx : context) (eqs : equation_system) : nat :=
    max (cheight ctx (eqs_substitutions eqs)) (cheight ctx (eqs_equations eqs)).
  Instance cheightable_equation_system : cheightable context equation_system :=
    Cheightable cheight_equation_system.  

  Definition eval_equation_system (ctx : context) (eqs : equation_system) : Prop :=
    eval ctx (eqs_substitutions eqs) /\ eval ctx (eqs_equations eqs).
  Instance evalable_equation_system : evalable context equation_system :=
    Evalable eval_equation_system.

  Definition vars_es (es : equation_system) : list var :=
    vars (eqs_substitutions es) ++ vars (eqs_equations es).
  Instance varsable_es : varsable equation_system var :=
   Varsable vars_es.
  Lemma unfold_fresh_equation_system: forall v sbsts eqns,
    fresh v (Equation_system sbsts eqns) <-> (fresh v sbsts /\ fresh v eqns).
  Proof.
    intros. unfold fresh, IN. simpl. unfold vars_es. simpl.
    split; repeat intro.
    split; intro; apply H; apply in_or_app; auto.
    apply in_app_or in H0. destruct H. icase H0.
  Qed.  

  Definition substitute_equation_system (v1 v2 : var) (eqs : equation_system) : equation_system :=
    match eqs with Equation_system sbsts eqns =>
      Equation_system (substitute v1 v2 sbsts) (substitute v1 v2 eqns)
    end.
  Instance proper_equation_system: proper var share equation_system.
  Proof.
    apply Proper with substitute_equation_system.
    destruct c. simpl height.
    unfold height_equation_system, eqs_substitutions, eqs_equations, substitute_equation_system.
    do 2 rewrite <- substitute_height. trivial.
    intros. destruct obj. unfold substitute_equation_system.
    rewrite unfold_fresh_equation_system in *. 
    destruct H. split; apply substitute_vars; auto.
    intros. destruct obj. unfold substitute_equation_system.
    rewrite unfold_fresh_equation_system in H. destruct H.
    simpl eval. unfold eval_equation_system, eqs_equations, eqs_substitutions.
    do 2 (rewrite <- (substitute_fresh rho); auto). tauto.
    intros. destruct obj. unfold substitute_equation_system.
    rewrite unfold_fresh_equation_system in H. destruct H.
    unfold cequiv. simpl eval. unfold eval_equation_system, eqs_equations, eqs_substitutions.
    generalize (change_unused _ _ H rho v) (change_unused _ _ H0 rho v). unfold cequiv. intros.
    rewrite H1, H2. tauto.
  Qed.

  (* Top level systems, with existentials (and maybe someday nonzeros) *)
  Record top_level : Type := Top_level {
    tl_equation_system  : equation_system;
    tl_exists           : list var;
    tl_nonzeros         : list var
  }.

  Definition height_top_level (tleqs : top_level) : nat :=
    height (tl_equation_system tleqs).
  Lemma is_height_zero_top_level : is_height_zero_spec height_top_level.
  Proof.
    hnf.
    intros.
    apply is_height_zero_equation_system.
  Qed.
  Instance heightable_top_level : heightable top_level :=
    Heightable height_top_level is_height_zero_top_level.

  Definition cheight_top_level (ctx : context)(tleqs : top_level) : nat :=
    max (cheight ctx (tl_equation_system tleqs)) (cheight ctx (tl_nonzeros tleqs)).
  Instance cheightable_top_level : cheightable context top_level :=
    Cheightable cheight_top_level.

  Definition eval_var_nz (ctx : context) (v : var) : Prop :=
   ctx v <> bot.
  Instance evalable_var_nz : evalable context var := Evalable eval_var_nz.

  Definition eval_top_level (ctx : context) (tleqs : top_level) : Prop :=
    exists ctx',
      [(tl_exists tleqs) => ctx'] ctx |= (tl_equation_system tleqs) /\
      [(tl_exists tleqs) => ctx'] ctx |= (tl_nonzeros tleqs).
  Instance evalable_top_level : evalable context top_level :=
    Evalable eval_top_level.

  Record top_es : Type := Top_es {
    tes_equation_system : equation_system;
    tes_exists          : list var
  }.
  Definition height_top_es (tes : top_es) : nat :=
    height (tes_equation_system tes).
  Lemma is_height_zero_top_es : is_height_zero_spec height_top_es.
  Proof.
   hnf.
   intros.
   apply is_height_zero_equation_system.
  Qed.
  Instance heightable_top_es : heightable top_es :=
    Heightable height_top_es is_height_zero_top_es.
  Definition cheight_top_es (ctx : context)(tes : top_es) : nat :=
    cheight ctx (tes_equation_system tes).
  Instance cheightable_top_es : cheightable context top_es :=
    Cheightable cheight_top_es.
  Definition eval_top_es (ctx : context) (tes : top_es) : Prop :=
    exists ctx',
      [(tes_exists tes) => ctx'] ctx |= (tes_equation_system tes).
  Instance evalable_top_es : evalable context top_es :=
    Evalable eval_top_es.

  Definition tl2tes (tl : top_level) : top_es := 
   Top_es (tl_equation_system tl) (tl_exists tl).

  Definition eval_top_level_bounded (ctx : context) (btleqs : (top_level*nat)) : Prop :=
   exists ctx',
      match btleqs with (tleqs,n) =>
      cheight ctx' tleqs <= n /\
      [(tl_exists tleqs) => ctx'] ctx |= (tl_equation_system tleqs) /\
      [(tl_exists tleqs) => ctx'] ctx |= (tl_nonzeros tleqs)
      end.
  Instance evalable_top_level_bounded : evalable context (top_level*nat) :=
    Evalable eval_top_level_bounded.
     

(*
  Instance evalable_top_level : evalable context top_level :=
    Evalable eval_top_level.

  Record ntop_level : Type := NTop_level {
    ntl_tl : top_level;
    ntl_nonzeros : list var
  }.

  Definition height_ntop_level (ntleqs : ntop_level) : nat :=
    height (ntl_tl ntleqs).
  Lemma is_height_zero_ntop_level : is_height_zero_spec height_ntop_level.
  Proof.
   hnf.
   intros.
   apply is_height_zero_top_level.
  Qed.
  Instance heightable_ntop_level : heightable ntop_level :=
    Heightable height_ntop_level is_height_zero_ntop_level.
  Definition cheight_ntop_level (ctx : context)(ntleqs : ntop_level) : nat :=
    max (cheight ctx (ntl_tl ntleqs)) (cheight ctx (ntl_nonzeros ntleqs)).
  Instance cheightable_ntop_level : cheightable context ntop_level :=
    Cheightable cheight_ntop_level.  
  Definition eval_nonzeros (ctx : context)(nl : list var) : Prop :=
    fold_right (fun (v : var)(P : Prop)  => P /\ ~(ctx v = bot)) True nl.
  Instance evalable_nonzeros : evalable context (list var) :=
    Evalable eval_nonzeros.
  Definition eval_ntop_level (ctx : context) (ntleqs : ntop_level) : Prop :=
    eval ctx (ntl_tl ntleqs) /\ eval ctx (ntl_nonzeros ntleqs).
  Instance evalable_ntop_level : evalable context ntop_level :=
    Evalable eval_ntop_level.
*)
End Internal_Equation_System.
*)