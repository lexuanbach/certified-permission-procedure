Require Import msl.msl_standard.
Require Import share_dec_base.
Require Import share_equation_system.
Require Import base_properties.
Require Import share_dec_interface.

Module Interpreter (sv : SV)
                   (Import es : EQUATION_SYSTEM sv with Module dom := Bool_Domain)
                   (Import bf : BOOL_FORMULA sv) <: INTERPRETER sv es bf.

 
 Module sys_features := System_Features sv es.
 Import sys_features.

 Class B2F (A B : Type):= Interpret {
  interpret : A -> B
 }.
 Implicit Arguments Interpret [A B].

 Definition v_int := fun (v : var) => varF v.
 Instance b2f_v : B2F _ _ := Interpret v_int.
 Definition b_int := fun b => valF b.
 Instance b2f_b : B2F _ _ := Interpret b_int.
 Definition obj_int := fun (obj : object) => 
  match obj with 
  |Vobject v => varF v 
  |Cobject c => valF c
  end.
 Instance b2f_obj : B2F _ _ := Interpret obj_int.
 Definition eql_int := fun (eql : equality) => 
  let (obj1,obj2) := eql in
  match (obj1,obj2) with
  |(Cobject c1, Cobject c2) => if bool_dec c1 c2 then valF true else valF false
  |(Vobject v, Cobject c)
  |(Cobject c, Vobject v) => if c then varF v else negF (varF v)
  |_ => orF (andF (interpret obj1) (interpret obj2)) 
            (andF (negF (interpret obj1)) (negF (interpret obj2)))
  end.
 Instance b2f_eql : B2F _ _ := Interpret eql_int.

 Definition eqn_int := fun (eqn : equation) =>
  match eqn with (obj1,obj2,obj3) =>
  match (obj1,obj2,obj3) with
  |(Cobject c1,Cobject c2, Cobject c3) => if c1 then valF (negb c2 && c3) else 
                                           if bool_dec c2 c3 then valF true else valF false  
  |(Vobject v1, Vobject v2, Cobject true) => orF (andF (varF v1) (negF (varF v2)))
                                                 (andF (varF v2) (negF (varF v1)))
  |(Vobject v1, Vobject v2, Cobject false) => andF (negF (varF v1)) (negF (varF v2))
  |(Vobject v1, Cobject true, Vobject v2) 
  |(Cobject true, Vobject v1, Vobject v2) => andF (negF (varF v1)) (varF v2)
  |(Vobject v1, Cobject false, Vobject v2) 
  |(Cobject false, Vobject v1, Vobject v2) => interpret (Vobject v1, Vobject v2)
  |(Vobject v, Cobject c1, Cobject c2)
  |(Cobject c1, Vobject v, Cobject c2) => if c1 then if c2 then negF (varF v) else valF false
                                          else interpret (Vobject v, Cobject c2)
  |(Cobject c1, Cobject c2, Vobject v) => if c1 then if c2 then valF false else varF v
                                          else interpret (Vobject v, Cobject c2)
  |_ => orF (andF (negF (interpret obj1)) (interpret (obj2,obj3)))
            (andF (interpret obj1) (andF (negF (interpret obj2)) (interpret obj3)))
  end
  end.
 Instance b2f_eqn : B2F _ _ := Interpret eqn_int.
 Definition list_int {A} `{@B2F A bF} :=
  fun (l : list A) => fold_right (fun a f => andF (interpret a) f) (valF true) l.
 Instance b2f_list {A} `{@B2F A bF} : B2F _ _:= Interpret list_int.

 Fixpoint fold_right_nodup {A B}(f : B -> A -> A) (a : A) (l : list B) `{EqDec B}:=
 match l with
 |nil => a
 |b::l' => match in_dec eq_dec b l' with
           |left _ => fold_right_nodup f a l'
           |right _ => f b (fold_right_nodup f a l')
           end
 
 end.

 Definition exF_quan := fun l f => fold_right_nodup exF f l.
 Definition allF_quan := fun l f => fold_right_nodup allF f l.
 
 Definition ses_int := fun (ses : sat_equation_system) =>
  let f1    := interpret (sat_nzvars ses) in
  let f2    := interpret (sat_equalities ses) in
  let f3    := interpret (sat_equations ses) in
   andF f1 (andF f2 f3).
 Instance b2f_ses : B2F _ _ := Interpret ses_int.

 Definition ies_int := fun (ies : impl_equation_system) =>
  let f1    := interpret (impl_nzvars ies) in
  let f2    := interpret (impl_equalities ies) in
  let f3    := interpret (impl_equations ies) in
   exF_quan (impl_exvars ies) (andF f1 (andF f2 f3)).
 Instance b2f_ies : B2F _ _ := Interpret ies_int.

 Definition is_int := fun (is : impl_system) =>
  let (ies1,ies2) := is in
  let f1 := interpret (ies1) in
  let f2 := interpret (ies2) in
   implF f1 f2.
 Instance b2f_is : B2F _ _ := Interpret is_int.

 Definition vars_interpret_spec (A : Type) `{@B2F A bF} `{varsable A var}:= 
  forall a, sublist (vars (interpret a)) (vars a).
 Class vars_interpret_prop (A : Type) `{@B2F A bF} `{varsable A var} := Vars_interpret_prop {
  vars_int : vars_interpret_spec A
 }.

 Instance obj_int_vars : vars_interpret_prop object.
 Proof with try tauto.
  constructor.
  repeat intro. icase a...
 Qed.
 Instance var_vars : varsable var var.
 Proof.
  constructor. intro. apply (X::nil).
 Defined.
 Lemma vars_list_var: forall (l : list var),
  vars l = l.
 Proof with try tauto.
  induction l...
  simpl in *;congruence.
 Qed.
 Instance var_int_vars : vars_interpret_prop var.
 Proof with try tauto.
  constructor.
  repeat intro...
 Qed.
 Instance eql_int_vars : vars_interpret_prop equality.
 Proof with try tauto.
  constructor.
  repeat intro.
  destruct a as [obj1 obj2].
  icase obj1;icase obj2; try icase s0;try icase s1;simpl in *...
 Qed.
 Instance eqn_int_vars : vars_interpret_prop equation.
 Proof with try tauto.
  constructor.
  repeat intro.
  destruct a as [[obj1 obj2] obj3].
  icase obj1;icase obj2;icase obj3;
  try icase s0;try icase s1;try icase s2;simpl in *...
 Qed.
 Instance list_int_vars {A} `{vars_interpret_prop A} : vars_interpret_prop (list A).
 Proof with try tauto.
  constructor.
  induction a;repeat intro;
  simpl...
  repeat rewrite in_app_iff.
  generalize (vars_int a e);intro.
  simpl in H2. rewrite in_app_iff in H2.
  spec IHa e...
 Qed.

 Lemma exF_quan_vars: forall l f v,
  In v (vars (exF_quan l f)) <-> In v (l++vars f).
 Proof with try tauto.
  induction l;intros;unfold exF_quan in *.
  simpl... simpl.
  destruct (in_dec eq_dec a l);split;intros.
  apply IHl in H...
  destruct H;subst...
  apply IHl. rewrite in_app_iff...
  apply IHl... 
  simpl in H. destruct H;subst...
  apply IHl in H...
  destruct H;subst...
  simpl...
  rewrite in_app_iff in H...
  destruct H; simpl.
  right. apply IHl. rewrite in_app_iff...
  right. apply IHl. rewrite in_app_iff...
 Qed.

 Lemma allF_quan_vars: forall l f v,
  In v (vars (allF_quan l f)) <-> In v (l++vars f).
 Proof with try tauto.
  induction l;intros;unfold allF_quan in *.
  simpl... simpl.
  destruct (in_dec eq_dec a l);split;intros.
  apply IHl in H...
  destruct H;subst...
  apply IHl. rewrite in_app_iff...
  apply IHl... 
  simpl in H. destruct H;subst...
  apply IHl in H...
  destruct H;subst...
  simpl...
  rewrite in_app_iff in H...
  destruct H; simpl.
  right. apply IHl. rewrite in_app_iff...
  right. apply IHl. rewrite in_app_iff...
 Qed.

 Instance ses_int_vars : vars_interpret_prop sat_equation_system.
 Proof with try tauto.
  constructor.
  repeat intro.
  simpl in *.
  destruct a as [l1 l2 l3];simpl in *.
  repeat rewrite in_app_iff in *.
  generalize (vars_int l1 e);intro.
  generalize (vars_int l2 e);intro.  
  generalize (vars_int l3 e);intro.
  assert (vars l1 = l1) by apply vars_list_var.
  simpl in *. unfold es.var,var in *. 
  rewrite H3 in H0...
 Qed.

 Instance ies_int_vars : vars_interpret_prop impl_equation_system.
 Proof with try tauto.
  constructor.
  repeat intro.
  simpl in *.
  unfold ies_int in H;simpl in H.
  rewrite exF_quan_vars in H.
  destruct a as [l1 l2 l3 l4];simpl in *.
  unfold ies_int in H;simpl in H.
  repeat rewrite in_app_iff in *.
  generalize (vars_int l2 e);intro.  
  generalize (vars_int l3 e);intro.
  generalize (vars_int l4 e);intro.
  assert (vars l2 = l2) by apply vars_list_var.
  unfold es.var,var in *.
  rewrite H3 in H0...
 Qed.
 
 Instance is_int_vars : vars_interpret_prop impl_system.
 Proof with try tauto.
  constructor.
  repeat intro.
  simpl in *.
  unfold is_int.
  destruct a as [ies1 ies2].
  simpl in *.
  repeat rewrite in_app_iff in *.
  generalize (vars_int ies1 e);intro.
  generalize (vars_int ies2 e);intro...
 Qed. 

 Definition beval_interpret_spec (A : Type) `{@B2F A bF} `{evalable context A}:=
  forall a rho, rho |= a <-> beval rho (interpret a) = true.

 Class beval_interpret_prop (A : Type) `{@B2F A bF} `{evalable context A} := Beval_interpret_prop {
  beval_int : beval_interpret_spec A
 }.

 Instance v_int_prop : beval_interpret_prop var.
 Proof with (try tauto;try congruence).
  constructor. repeat intro. simpl.
  icase (rho a); split;repeat intro;disc...
 Qed.

 Lemma obj_beval: forall rho obj,
  beval rho (interpret obj) = get rho obj.
 Proof with try tauto.
  intros. icase obj...
 Qed.
 
 Instance eql_int_prop : beval_interpret_prop equality.
 Proof with firstorder.
  constructor. repeat intro.
  destruct a as [obj1 obj2].
  icase obj1;icase obj2;
  try icase s0;try icase s1; simpl;
  try icase (rho v); try icase (rho v0); simpl...
 Qed.

 Instance eqn_int_prop : beval_interpret_prop equation.
 Proof with firstorder.
  constructor. repeat intro.
  destruct a as [[obj1 obj2] obj3].
  icase obj1;icase obj2;icase obj3;
  try icase s0;try icase s1;try icase s2; simpl;
  try icase (rho v); try icase (rho v0); try icase (rho v1);simpl...
 Qed. 

 Instance list_int_prop {A} `{beval_interpret_prop A} : beval_interpret_prop (list A).
 Proof with try tauto.
  constructor. induction a;intros.
  simpl...
  simpl.
  rewrite andb_true_iff.
  spec IHa rho.
  generalize (beval_int a rho);intro...
 Qed.

 Instance ses_int_prop : beval_interpret_prop sat_equation_system.
 Proof with try tauto.
  constructor. repeat intro.
  destruct a as [l1 l2 l3].
  simpl. unfold eval_sat_equation_system;simpl.
  repeat rewrite andb_true_iff.
  generalize (beval_int l1 rho);intro.
  generalize (beval_int l2 rho);intro.
  generalize (beval_int l3 rho);intro...
 Qed.

 (*To make life easier*)
 Lemma upd_id {A B} `{EqDec A}: forall (rho : A -> B) v b,
  rho v = b ->
  upd rho v b = rho.
 Proof with try tauto.
  repeat intro.
  subst. extensionality v'.
  destruct (eq_dec v v'). subst.
  apply upd_eq.
  apply upd_neq...
 Qed.

 Lemma upd_override_not_in {A B} `{EqDec A}: forall (rho rho': A -> B) v b l,
  ~In v l ->
  [l => upd rho' v b]rho = [l => rho']rho.
 Proof with try tauto.
  repeat intro.
  extensionality v'.
  destruct (in_dec eq_dec v' l).
  repeat rewrite override_in...
  rewrite upd_neq... intro;subst...
  repeat rewrite override_not_in...
 Qed.
 (*To make life easier*)

 Lemma exF_quan_beval: forall l f (rho:context),
  beval rho (exF_quan l f) = true <-> 
  exists rho', beval ([l => rho']rho) f = true.
 Proof with try tauto.
  induction l;intros;unfold exF_quan in *;simpl.
  split;intro. exists rho...
  destruct H...
  destruct (in_dec eq_dec a l).
  rewrite IHl.
  split;intros H; destruct H as [rho' H];exists rho'.
  rewrite upd_id... rewrite override_in...
  rewrite upd_id in H... rewrite override_in...
  simpl. rewrite orb_true_iff.
  generalize (IHl f (upd rho a true));intro.
  generalize (IHl f (upd rho a false));intro.
  split;intro.
  destruct H1.
  
  apply H in H1.
  destruct H1 as [rho' H1].
  exists (upd rho' a true).
  rewrite upd_eq.
  rewrite<- override_absorb_not_in...
  rewrite upd_override_not_in...

  apply H0 in H1.
  destruct H1 as [rho' H1].
  exists (upd rho' a false).
  rewrite upd_eq.
  rewrite<- override_absorb_not_in...
  rewrite upd_override_not_in...

  destruct H1 as [rho' H1].
  remember (rho' a) as b.
  symmetry in Heqb. destruct b.
  left. apply H. exists rho'.
  rewrite override_absorb_not_in...
  right. apply H0. exists rho'.
  rewrite override_absorb_not_in...
 Qed.

 Lemma allF_quan_beval: forall l f (rho:context),
  beval rho (allF_quan l f) = true <-> 
  forall rho', beval ([l => rho']rho) f = true.
 Proof with try tauto.
  induction l;intros;unfold allF_quan in *;simpl.
  split;intros...
  destruct (in_dec eq_dec a l).
  rewrite IHl.
  split;intros.
  rewrite upd_id...
  apply H...
  rewrite override_in...
  spec H rho'. rewrite upd_id in H...
  rewrite override_in...
  
  simpl.
  rewrite andb_true_iff.
  generalize (IHl f (upd rho a true));intro.
  generalize (IHl f (upd rho a false));intro.
  rewrite H. rewrite H0.
  split;intros.
  destruct H1 as [H1 H2].
  spec H1 rho'. spec H2 rho'.
  rewrite<- override_absorb_not_in...
  icase (rho' a).
  split;intros.
  spec H1 (upd rho' a true).
  rewrite<- override_absorb_not_in in H1...
  rewrite upd_eq in H1...
  rewrite upd_override_not_in in H1...
  spec H1 (upd rho' a false).
  rewrite<- override_absorb_not_in in H1...
  rewrite upd_eq in H1...
  rewrite upd_override_not_in in H1...  
 Qed.

 Instance ies_int_prop : beval_interpret_prop impl_equation_system.
 Proof with try tauto.
  constructor. repeat intro.
  simpl.
  unfold eval_impl_equation_system,ies_int,e_eval.
  rewrite exF_quan_beval.
  destruct a as [l1 l2 l3 l4];simpl.
  unfold eval_sat_equation_system,ies2ses;simpl.
  generalize (beval_int l2);intro.
  generalize (beval_int l3);intro.
  generalize (beval_int l4);intro...  
  split;intro H2;destruct H2 as [rho' H2];exists rho';
  spec H ([l1 =>rho']rho);
  spec H0 ([l1 =>rho']rho);
  spec H1 ([l1 =>rho']rho);
  repeat rewrite andb_true_iff in *...
 Qed.

 Lemma beval_implF_rewrite: forall rho f1 f2, 
  beval rho (implF f1 f2) = negb (beval rho f1)|| (beval rho f2).
 Proof.
  intros. simpl.
  icase (beval rho f1);icase (beval rho f2).
 Qed.

 Instance is_int_prop : beval_interpret_prop impl_system.
 Proof with try tauto.
  constructor. repeat intro.
  destruct a as [ies1 ies2].
  unfold interpret,b2f_is,is_int.
  generalize (beval_int ies1 rho);intro.
  generalize (beval_int ies2 rho);intro.
  rewrite beval_implF_rewrite.
  icase (beval rho (interpret ies1));
  icase (beval rho (interpret ies2));simpl;
  split;repeat intro...
  apply H0. apply H1. apply H...
 Qed.

 Lemma exF_quan_In: forall l bf v,
  In v l ->
  not_free v (exF_quan l bf).
 Proof with try tauto.
  induction l;intros;unfold exF_quan in *. inv H.
  simpl. 
  destruct (in_dec eq_dec a l).
  apply IHl... destruct H;subst...
  simpl. destruct (eq_dec v a)...
  destruct H;subst... apply IHl...
 Qed.

 Lemma exF_quan_In_iff: forall l bf v,
  not_free v (exF_quan l bf) <-> (In v l \/ not_free v bf).
 Proof with try tauto.
  induction l;intros;unfold exF_quan in *. simpl...
  simpl. destruct (in_dec eq_dec a l).
  rewrite IHl. split;intros...
  destruct H... destruct H;subst...
  simpl. destruct (eq_dec v a);subst...
  rewrite IHl. split;intros...
  destruct H... destruct H;subst...
 Qed.

 Lemma allF_quan_In: forall l bf v,
  In v l ->
  not_free v (allF_quan l bf).
 Proof with try tauto.
  induction l;intros;unfold allF_quan in *. inv H.
  simpl. 
  destruct (in_dec eq_dec a l).
  apply IHl... destruct H;subst...
  simpl. destruct (eq_dec v a)...
  destruct H;subst... apply IHl...
 Qed.

 Lemma allF_quan_In_iff: forall l bf v,
  not_free v (allF_quan l bf) <-> (In v l \/ not_free v bf).
 Proof with try tauto.
  induction l;intros;unfold allF_quan in *. simpl...
  simpl. destruct (in_dec eq_dec a l).
  rewrite IHl. split;intros...
  destruct H... destruct H;subst...
  simpl. destruct (eq_dec v a);subst...
  rewrite IHl. split;intros...
  destruct H... destruct H;subst...
 Qed.

 Definition is_free (v : var) (ies : impl_equation_system) : bool :=
   if in_dec eq_dec v (impl_exvars ies) then false else true.

 Lemma is_free_In: forall v ies,
  is_free v ies = true <-> ~In v (impl_exvars ies).
 Proof with try tauto.
  intros. unfold is_free.
  destruct (in_dec eq_dec v (impl_exvars ies))...
  split;intros;disc...
 Qed.

 Definition in_not_free_spec (A : Type) `{@B2F A bF}:= 
  forall a v, In v (vars (interpret a)) -> not_free v (interpret a) -> False .
 Class in_not_free_prop (A : Type) `{@B2F A bF} := In_not_free_prop {
  in_not_free : in_not_free_spec A
 }.

 Instance in_not_free_obj: in_not_free_prop object.
 Proof with try tauto.
  constructor. repeat intro.
  icase a... inv H; simpl in H0...
  destruct (eq_dec v v)...
 Qed.

 Instance in_not_free_eql: in_not_free_prop equality.
 Proof with try tauto.
  constructor. repeat intro.
  destruct a.
  icase o;icase o0;
  simpl in *;
  try destruct (eq_dec v v0);
  try destruct (eq_dec v v1);
  subst;
  try icase s0; 
  try icase s1;
  subst;simpl in *;firstorder;
  try destruct (@eq_dec var sv.t_eq_dec v0 v0)...
 Qed.

 Instance in_not_free_eqn: in_not_free_prop equation.
 Proof with try tauto.
  constructor. repeat intro.
  destruct a as [[? ?] ?].
  icase o;icase o0;icase o1;
  simpl in *;
  try destruct (eq_dec v v0);
  try destruct (eq_dec v v1);
  try destruct (eq_dec v v2);
  subst;
  try icase s0; 
  try icase s1;
  try icase s2;
  subst;simpl in *;firstorder;
  try destruct (@eq_dec var sv.t_eq_dec v0 v0);
  try destruct (@eq_dec var sv.t_eq_dec v1 v1);
  try destruct (@eq_dec var sv.t_eq_dec v2 v2)...
 Qed.

 Instance in_not_free_var: in_not_free_prop var.
 Proof with try tauto.
  constructor.
  repeat intro.
  inv H;simpl in *...
  destruct (eq_dec v v);subst...
 Qed.

 Instance in_not_free_list  {A} `{in_not_free_prop A} : in_not_free_prop (list A).
 Proof with try tauto.
  constructor.
  induction a;intros. inv H1.
  simpl in *. destruct H2.
  rewrite in_app_iff in H1.
  destruct H1.
  apply in_not_free in H2...
  apply IHa with (v:=v)...
 Qed.
  
 Lemma ies_is_free_equiv: forall v ies,
  In v (vars (interpret ies)) ->
  (is_free v ies = true <-> ~not_free v (interpret ies)).
 Proof with try tauto.
  intros.
  rewrite is_free_In.
  split;repeat intro.
  - apply H0. 
    destruct ies as [l1 l2 l3 l4].
    simpl in *. unfold ies_int in H;simpl in H.
    rewrite exF_quan_vars in H.
    rewrite in_app_iff in H.
    destruct H...
    unfold ies_int in H1;simpl in H1.
    rewrite exF_quan_In_iff in H1.
    destruct H1...
    inv H1. inv H3.
    simpl in H.
    repeat rewrite in_app_iff in H.
    destruct H. 
    generalize (in_not_free l2 v H H2)...
    destruct H.
    generalize (in_not_free l3 v H H1)...
    generalize (in_not_free l4 v H H4)...

  - apply H0.
    simpl. unfold ies_int.
    apply exF_quan_In...
 Qed.

 Require Import Classical.

 Lemma not_free_ies: forall v (ies : impl_equation_system),
  In v (vars (interpret ies)) ->
  (In v (impl_exvars ies) <-> not_free v (interpret ies)).
 Proof with try tauto.
  intros. apply ies_is_free_equiv in H.
  unfold is_free in *.
  unfold var,es.var in *.
  destruct (in_dec eq_dec v (impl_exvars ies))...
  split;intros...
  destruct (classic (not_free v (interpret ies)))...
  rewrite<- H in H1. inv H1.
 Qed.

End Interpreter.