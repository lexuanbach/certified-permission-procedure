Require Import msl.msl_standard.
Require Import share_dec_base.
Require Import base_properties.
Require Import share_equation_system.
Require Import share_dec_interface.
Require Import share_correctness_base.
Require Import share_correctness.
Require Import share_decompose_base.

Module Share2Bool (sv : SV)
                  (ses : EQUATION_SYSTEM sv with Module dom := Share_Domain)
                  (sesf : SYSTEM_FEATURES sv ses)
                  (bes : EQUATION_SYSTEM sv with Module dom := Bool_Domain)
                  (besf : SYSTEM_FEATURES sv bes) <:
                  SHARE_TO_BOOL sv ses sesf bes besf.

 Module DB := Decompose_Base sv ses sesf.
 Import DB.
 Import Share.

 Opaque tree_shares.Share.BAF.bot tree_shares.Share.BAF.top
 tree_shares.Share.BAF.glb tree_shares.Share.BAF.lub.

 Class S2B (A B : Type):= Transformation {
  transform : A -> B
 }.

 Implicit Arguments Transformation [A B].

 Definition sv2bv (sv : ses.var) : bes.var := sv.
 Instance Sv2bv : S2B _ _ := Transformation sv2bv.
 Definition ss2bs (sc : ses.s) : bes.s :=
  match eq_dec sc emptyshare with
  | left _  => false
  | right _ => true
  end.
 Instance Ss2bs : S2B _ _ := Transformation ss2bs. 

 Definition sobj2bobj (so : ses.object) : bes.object :=
  match so with
  | Vobject v => Vobject (transform v)
  | Cobject c => Cobject (transform c)
  end.
 Instance Sobj2bobj : S2B _ _ := Transformation sobj2bobj.
 
 Definition seql2beql (seql : ses.equality) : bes.equality :=
  let (obj1,obj2) := seql in (transform obj1,transform obj2).
 Instance Seql2beql : S2B _ _ := Transformation seql2beql.

 Definition seqn2beqn (seqn : ses.equation) : bes.equation :=
  let (pobj,obj) := seqn in (transform pobj,transform obj).
 Instance Seqn2beqn : S2B _ _ := Transformation seqn2beqn.

 Definition slist2blist {A B} `{@S2B A B} :=
  fun (l : list A) => fold_right (fun a lb => (transform a)::lb) nil l.
 Instance Slist2blist {A B} `{@S2B A B} : S2B _ _:= Transformation slist2blist.

 Definition sses2bses (sses : ses.sat_equation_system) : bes.sat_equation_system :=
  let lnzvars := transform (ses.sat_nzvars sses) in
  let leql    := transform (ses.sat_equalities sses) in
  let leqn    := transform (ses.sat_equations sses) in
   bes.Sat_equation_system lnzvars leql leqn.
 Instance Sses2bses : S2B _ _ := Transformation sses2bses.
  
 Definition sies2bies (sies : ses.impl_equation_system) : bes.impl_equation_system :=
  let lexvars := transform (ses.impl_exvars sies) in
  let lnzvars := transform (ses.impl_nzvars sies) in
  let leql    := transform (ses.impl_equalities sies) in
  let leqn    := transform (ses.impl_equations sies) in
   bes.Impl_equation_system lexvars lnzvars leql leqn.
 Instance Sies2bies : S2B _ _ := Transformation sies2bies.
 
 Definition sis2bis (sis : ses.impl_system) : bes.impl_system :=
  let (ies1,ies2) := sis in (transform ies1,transform ies2).
 Instance Sis2bis : S2B _ _ := Transformation sis2bis.

 Definition sctx2bctx (ctx : ses.context) : bes.context :=
  fun v => transform (ctx v).
 Instance Sctx2bctx : S2B _ _ := Transformation sctx2bctx.

 (*Some basic properties*)

 Lemma id_transform : forall (l : list ses.var),
  transform l = l.
 Proof with try tauto.
  induction l...
  simpl. simpl in IHl.
  rewrite IHl. f_equal.
 Qed.

 Lemma transform_replace_snzvars: forall ses l,
  besf.replace_snzvars (transform ses) l = transform (sesf.replace_snzvars ses l).
 Proof with try tauto.
  intros.
  destruct ses as [l1 l2 l3].
  simpl. unfold sses2bses;simpl.
  unfold besf.replace_snzvars;simpl.
  f_equal. symmetry.
  rewrite<- id_transform...
 Qed.
 
 Lemma transform_replace_inzvars: forall ies  l,
  besf.replace_inzvars (transform ies) l = transform (sesf.replace_inzvars ies l).
 Proof with try tauto.
  intros.
  destruct ies as [l1 l2 l3 l4].
  simpl. unfold sies2bies;simpl.
  unfold besf.replace_inzvars;simpl.
  f_equal. symmetry.
  rewrite<- id_transform...
 Qed.

 Lemma transform_replace_isnzvars: forall is  l1 l2,
  besf.replace_isnzvars (transform is) l1 l2 = transform (sesf.replace_isnzvars is l1 l2).
 Proof with try tauto.
  intros.
  destruct is as [ies1 ies2].
  simpl.
  f_equal; apply transform_replace_inzvars.
 Qed.

 Lemma fst_transform_is: forall (is : ses.impl_system),
  fst (transform is) = transform (fst is).
 Proof. intro. destruct is. tauto. Qed.

 Lemma snd_transform_is: forall (is : ses.impl_system),
  snd (transform is) = transform (snd is).
 Proof. intro. destruct is. tauto. Qed.

 Lemma transform_exvars: forall ies,
  bes.impl_exvars (transform ies) = ses.impl_exvars ies.
 Proof.
  intros. destruct ies as [l1 l2 l3 l4].
  simpl. apply id_transform.
 Qed.

 Lemma transform_ies2ses: forall ies,
  transform (ses.ies2ses ies) = bes.ies2ses (transform ies).
 Proof. 
  intros. destruct ies as [l1 l2 l3 l4]. tauto.
 Qed.

 Lemma transform_override: forall ctx ctx' l,
  transform ([l=>ctx']ctx) = [l=> transform ctx'] (transform ctx).
 Proof with try tauto.
  intros. extensionality v.
  destruct (in_dec eq_dec v l).
  rewrite override_in...
  simpl. unfold sctx2bctx.
  simpl. unfold ss2bs.
  rewrite override_in...
  rewrite override_not_in...
  simpl. unfold sctx2bctx.
  simpl. unfold ss2bs.
  rewrite override_not_in...
 Qed.

 (*End basic properties*)

 Definition transform_eval_spec (A B A' B' : Type) 
 `{evalable A B} `{evalable A' B'} 
 `{heightable B}
 `{varsable B ses.var} `{cheightable A (list ses.var)}
 `{@S2B A A'} `{@S2B B B'}:=
  forall (a : A) (b : B),
   |b| = 0 ->
   cheight a (vars b) = 0 ->
   (a |= b <-> (transform a) |= (transform b)).  

 Class transform_prop (A B A' B' : Type) 
 `{evalable A B} `{evalable A' B'} 
 `{heightable B}
 `{varsable B ses.var} `{cheightable A ses.var}
 `{@S2B A A'} `{@S2B B B'}:= Transform_eval {
  transform_eval : transform_eval_spec A B A' B'
 }.

 Instance list_transform_eval_correct {A B A' B'}
 `{transform_prop A B A' B'} : transform_prop A (list B) A' (list B').
 Proof with try tauto.
  constructor. induction b;intros. simpl...
  replace (|a0::b|) with (max (|a0|) (|b|)) in H7...
  rewrite max_zero in H7.
  destruct H7.
  assert (cheight a (vars (a0 :: b)) =  cheight a ((vars a0) ++ (vars b)))...
  rewrite H10 in H8. clear H10.
  rewrite cheight_app in H8.
  rewrite max_zero in H8.
  destruct H8.
  spec IHb H9 H10.
  generalize (transform_eval a a0 H7 H8);intro.
  simpl in *...
 Defined.

 Lemma obj_height_zero_eval: forall (obj : ses.object) ctx,
  |obj| = 0 ->
  cheight ctx (vars obj) = 0 ->
  get ctx obj = bot \/ get ctx obj = top.
 Proof with try tauto.
  intros.
  destruct obj; simpl in *.
  unfold list_cheight in H0. simpl in H0.
  rewrite Max.max_0_r in H0.
  apply height_zero_eq in H0...
  apply height_zero_eq in H...
 Qed.

 Lemma top_transform : transform top = true.
 Proof with try tauto.
  simpl. unfold ss2bs.
  case (eq_dec top emptyshare);intro...
  generalize nontrivial...
 Qed.

 Lemma bot_transform : transform bot = false.
 Proof with try tauto.
  simpl. unfold ss2bs.
  case (eq_dec bot emptyshare)...
 Qed.

 Lemma get_transform : forall (obj: ses.object) ctx,
  get (transform ctx) (transform obj) = transform (get ctx obj).
 Proof. intros. icase obj. Qed.

 Instance eql_transform_eval_correct : transform_prop ses.context ses.equality bes.context bes.equality.
 Proof with try tauto.
  constructor.
  repeat intro.
  destruct b as [obj1 obj2].
  rewrite height_eql_rewrite in H.
  rewrite max_zero in H. destruct H.
  replace (cheight a (vars (obj1, obj2))) with (cheight a (vars obj1 ++ vars obj2)) in H0...
  rewrite cheight_app in H0.
  rewrite max_zero in H0.
  destruct H0.
  generalize (obj_height_zero_eval _ _ H H0);intro.
  generalize (obj_height_zero_eval _ _ H1 H2);intro.
  generalize (top_transform);intro.
  generalize (bot_transform);intro.
  unfold eval,ses.eval_equality, bes.eval_equality.
  unfold transform at 1. unfold Seql2beql,seql2beql.
  repeat rewrite get_transform. unfold bes.s,ses.s,share in *. 
  split;intro. rewrite H7...
  icase H3;icase H4; unfold bes.dom.e,ses.dom.e,share in *; rewrite H3,H4 in H7; 
  try rewrite H5 in H7; try rewrite H6 in H7;
  try congruence...
 Defined.

 Instance eqn_transform_eval_correct : transform_prop ses.context ses.equation bes.context bes.equation.
 Proof with try tauto.
  constructor.
  repeat intro.
  destruct b as [[obj1 obj2] obj3].
  rewrite height_eqn_rewrite in H.
  rewrite height_eql_rewrite in H.
  repeat rewrite max_zero in H.
  destruct H as [[? ?] ?].
  replace (cheight a (vars (obj1, obj2,obj3))) with 
  (cheight a (vars obj1 ++ vars obj2 ++ vars obj3)) in H0...
  repeat rewrite cheight_app in H0.
  repeat rewrite max_zero in H0.
  destruct H0 as [? [? ?]].
  generalize (obj_height_zero_eval _ _ H H0);intro.
  generalize (obj_height_zero_eval _ _ H1 H3);intro.
  generalize (obj_height_zero_eval _ _ H2 H4);intro.
  generalize (top_transform);intro.
  generalize (bot_transform);intro.
  unfold eval,ses.eval_equation, bes.eval_equation.
  unfold transform at 1. unfold Seqn2beqn,seqn2beqn.
  unfold transform at 1. unfold Seql2beql,seql2beql.
  repeat rewrite get_transform. 
  generalize (nontrivial);intro.
  assert (true <> false /\ false <> true).
   split;intro H11;inv H11.
  unfold bes.s,ses.s,share in *.
  unfold bes.dom.e,ses.dom.e,share in *;
  icase H5;icase H6;icase H7;
  rewrite H5,H6,H7;
  try rewrite H8;try rewrite H9;compute;
  try repeat rewrite Share.glb_bot;
  try repeat rewrite Share.glb_top;
  try repeat rewrite Share.lub_bot;
  try repeat rewrite Share.lub_top...
  split;intros... destruct H12. rewrite H13 in H10...
 Defined.

 Opaque tree_shares.Share.canonTree_eq_dec .

 Instance var_transform_eval_correct : transform_prop ses.context ses.var bes.context bes.var.
 Proof with try tauto.
  constructor. repeat intro.
  simpl in *. unfold list_cheight in H0. simpl in H0.
  unfold emptyshare.
  rewrite Max.max_0_r in H0.
  apply height_zero_eq in H0.
  compute.
  case (tree_shares.Share.canonTree_eq_dec (a b) bot);intro...
  split;intros... inv H2.
 Defined.

 Instance ses_transform_eval_correct : 
 transform_prop ses.context ses.sat_equation_system bes.context bes.sat_equation_system.
 Proof with try tauto.
  constructor. repeat intro.
  destruct b as [l1 l2 l3].
  simpl in *.
  unfold sesf.ses_h in H;
  unfold ses.eval_sat_equation_system,bes.eval_sat_equation_system;
  simpl in *.
  rewrite max_zero in H. destruct H.
  replace (list_cheight a (l1 ++ vars_list l2 ++ vars_list l3)) with
  (cheight a (l1++vars l2++vars l3)) in H0...
  repeat rewrite cheight_app in H0.
  repeat rewrite max_zero in H0.
  destruct H0 as [? [? ?]].
  assert (|l1| = 0). clear.
   induction l1...
  assert (l1 = vars l1). clear.
   induction l1... simpl in *. rewrite<- IHl1...
  rewrite H5 in H0. clear H5.
  generalize (transform_eval a l1 H4 H0);intro.
  generalize (transform_eval a l2 H H2);intro.
  generalize (transform_eval a l3 H1 H3);intro...
 Qed.

 Definition transformB (rho : bes.context) : ses.context :=
  fun v => match rho v with
           | false => bot
           | true => top
           end.
 
 Lemma transformB_correct: forall rho,
  transform (transformB rho) = rho.
 Proof with try tauto.
  intros.
  extensionality v.
  compute.
  case (rho v).
  case (tree_shares.Share.canonTree_eq_dec top bot);intro...
  generalize (nontrivial);intro...
  case (tree_shares.Share.canonTree_eq_dec bot bot)...
 Qed.

 Lemma transformB_cheight: forall rho (l : list ses.var),
  cheight (transformB rho) l = 0.
 Proof with try tauto.
  intros.
  assert (le (cheight (transformB rho) l) 0).
   rewrite sesf.cheight_leq_rewrite.
   intros.
   assert (|transformB rho v| = 0).
    compute. case (rho v).
    apply height_top. apply height_bot.
   omega.
  omega.
 Qed.

 Lemma nSAT_transform_correct: forall (ses : ses.sat_equation_system),
  |ses| = 0 ->
  (sesf.nSAT ses <-> besf.nSAT (transform ses)).
 Proof with try tauto.
  intros.
  rewrite<- sesf.replace_snzvars_height with (l:=nil) in H.
  split;intro.
  apply nSAT_zero_eval in H0...
  destruct H0 as [rho [H0 H1]].
  exists (transform rho).
  rewrite transform_replace_snzvars.
  generalize (transform_eval rho (sesf.replace_snzvars ses nil) H H1);intro.
  apply H2...

  destruct H0 as [brho H0].
  generalize (transformB_cheight brho (vars (sesf.replace_snzvars ses nil)));intro.
  remember (transformB brho) as rho.
  apply f_apply with (f:= transform) in Heqrho.
  rewrite transformB_correct in Heqrho.
  exists rho.
  generalize (transform_eval rho (sesf.replace_snzvars ses nil) H H1);intro.
  rewrite Heqrho in H2. apply H2...
 Qed.

 Lemma sSAT_transform_correct: forall (ses : ses.sat_equation_system) v,
  |ses| = 0 ->
  (sesf.sSAT ses v <-> besf.sSAT (transform ses) v).
 Proof with try tauto.
  intros.
  rewrite<- sesf.replace_snzvars_height with (l:=v::nil) in H.
  split;intro.
  apply sSAT_zero_eval in H0...
  destruct H0 as [rho [H0 H1]].
  exists (transform rho).
  rewrite transform_replace_snzvars.
  generalize (transform_eval rho (sesf.replace_snzvars ses (v::nil)) H H1);intro.
  apply H2...

  destruct H0 as [brho H0].
  generalize (transformB_cheight brho (vars (sesf.replace_snzvars ses (v::nil))));intro.
  remember (transformB brho) as rho.
  apply f_apply with (f:= transform) in Heqrho.
  rewrite transformB_correct in Heqrho.
  exists rho.
  generalize (transform_eval rho (sesf.replace_snzvars ses (v::nil)) H H1);intro.
  rewrite Heqrho in H2. apply H2...
 Qed.

 Lemma cheight_zero: forall (ctx : ses.context) l,
  cheight ctx l = 0 <-> forall v, In v l -> |ctx v| = 0.
 Proof with try tauto.
  induction l;intros.
  simpl...
  rewrite sesf.cheight_rewrite.
  rewrite max_zero.
  split;intros.
  destruct H0;subst...
  apply IHl...
  split. apply H... left...
  apply IHl... intros. apply H. right...
 Qed.

 Lemma transform_ies_eval: forall (ies : ses.impl_equation_system) rho,
  cheight rho (vars ies) = 0 ->
  |ies| = 0 ->
  ((exists rho',cheight rho' (ses.impl_exvars ies) = 0 /\
    [ses.impl_exvars ies => rho']rho |= (ses.ies2ses ies)) <->
   ((transform rho) |= transform ies)).
 Proof with try tauto.
  intros. split;intro.
  destruct H1 as [rho' [H1 H2]].
  exists (transform rho').
  rewrite <- transform_override.
  rewrite<- transform_ies2ses.
  rewrite transform_exvars.
  apply transform_eval in H2...
  rewrite cheight_zero in *.
  intros.
  destruct (in_dec eq_dec v (ses.impl_exvars ies)).
  rewrite override_in... apply H1...
  rewrite override_not_in...
  apply H. clear -H3. destruct ies as [l1 l2 l3 l4];simpl in *.
  repeat rewrite in_app_iff in *...
  destruct H1 as [brho' H1].
  exists (transformB brho').
  split. apply transformB_cheight.
  remember (transformB brho') as rho'.
  copy Heqrho'.
  apply f_apply with (f:=transform) in Heqrho'.
  rewrite transformB_correct in Heqrho'.
  rewrite <- Heqrho' in H1.
  rewrite <-transform_override in H1.
  rewrite<- transform_ies2ses in H1.
  rewrite transform_exvars in H1.
  apply transform_eval...
  rewrite cheight_zero in *.
  intros. destruct (in_dec eq_dec v (ses.impl_exvars ies)).
  rewrite override_in... rewrite Heqrho'0.
  compute.
  case (brho' v). apply height_top. apply height_bot.
  rewrite override_not_in... apply H.
  clear -H2. destruct ies as [l1 l2 l3 l4].
  simpl in *. repeat rewrite in_app_iff in *...
 Qed.
  
 Lemma nIMPL_transform_correct: forall is,
  |is| = 0 ->
  (sesf.nIMPL is <-> besf.nIMPL (transform is)).
 Proof with try tauto.
  intros. rewrite nIMPL_zero_eval...
  destruct is as [ies1 ies2].
  rewrite<- sesf.replace_isnzvars_height with (l:=nil) (l':=nil)in H.
  unfold sesf.replace_isnzvars in H.
  rewrite height_is_rewrite in H.
  rewrite max_zero in H.
  destruct H.
  split;intro.
  intros brho H2.
  generalize (transformB_cheight brho (vars (sesf.replace_isnzvars (ies1,ies2) nil nil)));intro.
  remember (transformB brho) as rho.  
  apply f_equal with (f:= transform) in Heqrho.
  rewrite transformB_correct in Heqrho.
  rewrite sesf.vars_replace_isnzvars in *.
  rewrite cheight_app in H3.
  rewrite max_zero in H3.
  destruct H3.
  spec H1 rho.
  repeat detach H1...
  rewrite transform_ies_eval in H1... rewrite<- Heqrho...
  rewrite transform_ies_eval... rewrite<- Heqrho in H2...
  rewrite sesf.vars_replace_isnzvars.
  rewrite cheight_app. rewrite max_zero...
  intros rho H2 H3.
  rewrite sesf.vars_replace_isnzvars in H2.
  rewrite cheight_app in H2. rewrite max_zero in H2.
  destruct H2.
  rewrite transform_ies_eval in *...
  apply H1...
 Qed.

 Lemma zIMPL_transform_correct: forall is x,
  |is| = 0 ->
  (sesf.zIMPL is x <-> besf.zIMPL (transform is) x).
 Proof with try tauto.
  intros. rewrite zIMPL_zero_eval...
  destruct is as [ies1 ies2].
  rewrite<- sesf.replace_isnzvars_height with (l:=nil) (l':=x::nil)in H.
  unfold sesf.replace_isnzvars in H.
  rewrite height_is_rewrite in H.
  rewrite max_zero in H.
  destruct H.
  split;intro.
  intros brho H2.
  generalize (transformB_cheight brho (vars (sesf.replace_isnzvars (ies1,ies2) nil (x::nil))));intro.
  remember (transformB brho) as rho.  
  apply f_equal with (f:= transform) in Heqrho.
  rewrite transformB_correct in Heqrho.
  rewrite sesf.vars_replace_isnzvars in *.
  rewrite cheight_app in H3.
  rewrite max_zero in H3.
  destruct H3.
  spec H1 rho.
  repeat detach H1...
  rewrite transform_ies_eval in H1... rewrite<- Heqrho...
  rewrite transform_ies_eval... rewrite<- Heqrho in H2...
  rewrite sesf.vars_replace_isnzvars.
  rewrite cheight_app. rewrite max_zero...
  intros rho H2 H3.
  rewrite sesf.vars_replace_isnzvars in H2.
  rewrite cheight_app in H2. rewrite max_zero in H2.
  destruct H2.
  rewrite transform_ies_eval in *...
  apply H1...
 Qed.

 Lemma sIMPL_transform_correct: forall is x y,
  |is| = 0 ->
  sesf.nIMPL is ->
  (sesf.sIMPL is x y <-> besf.sIMPL (transform is) x y).
 Proof with try tauto.
  intros. rewrite sIMPL_zero_eval...
  destruct is as [ies1 ies2].
  rewrite<- sesf.replace_isnzvars_height with (l:=(x::nil)) (l':=y::nil)in H.
  unfold sesf.replace_isnzvars in H.
  rewrite height_is_rewrite in H.
  rewrite max_zero in H.
  destruct H.
  split;intro.
  intros brho H3.
  generalize (transformB_cheight brho (vars (sesf.replace_isnzvars (ies1,ies2) (x::nil) (y::nil))));intro.
  remember (transformB brho) as rho.  
  apply f_equal with (f:= transform) in Heqrho.
  rewrite transformB_correct in Heqrho.
  rewrite sesf.vars_replace_isnzvars in *.
  rewrite cheight_app in H4.
  rewrite max_zero in H4.
  destruct H4.
  spec H2 rho.
  repeat detach H2...
  rewrite transform_ies_eval in H2... rewrite<- Heqrho...
  rewrite transform_ies_eval... rewrite<- Heqrho in H3...
  rewrite sesf.vars_replace_isnzvars.
  rewrite cheight_app. rewrite max_zero...
  intros rho H3 H4.
  rewrite sesf.vars_replace_isnzvars in H3.
  rewrite cheight_app in H3. rewrite max_zero in H3.
  destruct H3.
  rewrite transform_ies_eval in *...
  apply H2...
 Qed.
 
End Share2Bool.

