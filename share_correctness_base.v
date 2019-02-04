Require Import msl.msl_standard.
Require Import share_dec_base.
Require Import base_properties.
Require Import share_equation_system.
Require Import share_dec_interface.
Require Import NPeano.

 Import Share.

Module Round_Average (sv : SV)
                     (Import es : EQUATION_SYSTEM sv with Module dom := Share_Domain)
                     (Import esf : SYSTEM_FEATURES sv es).

 Definition avg_ctx (ctxL ctxR : context) (h : nat) (l : list var) : context :=
  fun v => if in_dec eq_dec v l then
            match avg h (ctxL v) (ctxR v) with
            | None => emptyshare
            | Some s => s
            end
           else recompose (ctxL v ,ctxR v).

 Definition rL_ctx (ctx : context) (h : nat) (l : list var) : context :=
  fun v => if in_dec eq_dec v l then
            match roundL h (ctx v) with
            | None => emptyshare
            | Some s => s
            end
           else let (sL,sR) := decompose (ctx v) in sL.

 Definition rR_ctx (ctx : context) (h : nat) (l : list var) : context :=
  fun v => if in_dec eq_dec v l then
            match roundR h (ctx v) with
            | None => emptyshare
            | Some s => s
            end
           else let (sL,sR) := decompose (ctx v) in sR.

 Lemma avg_override: forall l l' n ctxL ctxL' ctxR ctxR',
  avg_ctx ([l => ctxL']ctxL) ([l => ctxR']ctxR) n l' = 
  [l => avg_ctx ctxL' ctxR' n l'] (avg_ctx ctxL ctxR n l').
 Proof with try tauto.
  intros.
  extensionality v.
  destruct (in_dec eq_dec v l).
  rewrite override_in...
  unfold avg_ctx.
  destruct (in_dec eq_dec v l').
  repeat rewrite override_in...
  repeat rewrite override_in...
  rewrite override_not_in...
  unfold avg_ctx.
  destruct (in_dec eq_dec v l').
  repeat rewrite override_not_in...
  repeat rewrite override_not_in...
 Qed.

 Lemma avg_ctx_in_var: forall l v h (ctxL ctxR : context),
  |ctxL v| < h ->
  |ctxR v| < h ->  
  In v l -> 
  avg h (ctxL v) (ctxR v) = Some (avg_ctx ctxL ctxR h l v). 
  Proof with auto.
   intros.
   unfold avg_ctx.
   icase (in_dec eq_dec v l).
   destruct (tree_avg_ex _ _ _ H H0).
   unfold s,share in *. unfold dom.e,share in *. rewrite H2...
  Qed.

 Lemma avg_ctx_not_in_var: forall (ctxL ctxR : context) n l v,
  ~In v l ->
  avg_ctx ctxL ctxR n l v = recompose (ctxL v, ctxR v).
 Proof.
  intros. unfold avg_ctx. icase (in_dec eq_dec v l).
 Qed.

 Lemma rL_ctx_override: forall ctx ctx' l' n l,
  rL_ctx ([l'=>ctx']ctx) n l = [l'=>(rL_ctx ctx' n l)](rL_ctx ctx n l).
 Proof with try tauto.
  intros.
  extensionality v.
  destruct (in_dec eq_dec v l').
  rewrite override_in...
  unfold rL_ctx.
  destruct (in_dec eq_dec v l);
  rewrite override_in...
  rewrite override_not_in...
  unfold rL_ctx.
  destruct (in_dec eq_dec v l);
  rewrite override_not_in...
 Qed.

 Lemma rR_ctx_override: forall ctx ctx' l' n l,
  rR_ctx ([l'=>ctx']ctx) n l = [l'=>(rR_ctx ctx' n l)](rR_ctx ctx n l).
  Proof with try tauto.
  intros.
  extensionality v.
  destruct (in_dec eq_dec v l').
  rewrite override_in...
  unfold rR_ctx.
  destruct (in_dec eq_dec v l);
  rewrite override_in...
  rewrite override_not_in...
  unfold rR_ctx.
  destruct (in_dec eq_dec v l);
  rewrite override_not_in...
 Qed.

 Lemma rL_ctx_in_var: forall (ctx : context) h l v,
  (|ctx v| <= S h)%nat ->
  In v l ->
  roundL (S h) (ctx v) = Some (rL_ctx ctx (S h) l v).
 Proof with try tauto.
  intros.
  unfold rL_ctx.
  icase (in_dec eq_dec v l).
  apply tree_round_left_Some in H.
  destruct H. unfold s,share in *.  unfold dom.e,share in *. rewrite H...
 Qed.

 Lemma rR_ctx_in_var: forall (ctx : context) h l v,
  (|ctx v| <= S h)%nat ->
  In v l ->
  roundR (S h) (ctx v) = Some (rR_ctx ctx (S h) l v).
 Proof with try tauto.
  intros.
  unfold rR_ctx.
  icase (in_dec eq_dec v l).
  apply tree_round_right_Some in H.
  destruct H. unfold s,share in *. unfold dom.e,share in *. rewrite H...
 Qed.

 Lemma rL_ctx_not_in_var: forall (ctx : context) n l v,
  ~In v l ->
  rL_ctx ctx n l v = fst (decompose (ctx v)).
 Proof.
  intros. unfold rL_ctx. icase (in_dec eq_dec v l).
 Qed.

 Lemma rR_ctx_not_in_var: forall (ctx : context) n l v,
  ~In v l ->
  rR_ctx ctx n l v = snd (decompose (ctx v)).
 Proof.
  intros. unfold rR_ctx. icase (in_dec eq_dec v l).
 Qed.

 Lemma rL_ctx_lt: forall v h ctx l,
  (|ctx v| <= S h)%nat ->
  In v l ->
  |rL_ctx ctx (S h) l v| < S h.
 Proof with try tauto.
  intros.
  unfold rL_ctx. icase (in_dec eq_dec v l).
  apply tree_round_left_Some in H.
  destruct H. unfold s,share in *. unfold dom.e,share in *. rewrite H.
  apply tree_round_left_height_compare in H...
 Qed.

 Lemma rR_ctx_lt: forall v h ctx l,
  (|ctx v| <= S h)%nat ->
  In v l ->
  |rR_ctx ctx (S h) l v| < S h.
 Proof with try tauto.
  intros.
  unfold rR_ctx. icase (in_dec eq_dec v l).
  apply tree_round_right_Some in H.
  destruct H. unfold s,share in *. unfold dom.e,share in *. rewrite H.
  apply tree_round_right_height_compare in H...
 Qed.

 Lemma avg_ctx_leq: forall v h ctxL ctxR l,
  |ctxL v| < S h -> |ctxR v| < S h -> In v l ->
  (|avg_ctx ctxL ctxR (S h) l v| <= S h)%nat.
 Proof with try tauto.
  intros.
  unfold avg_ctx. icase (in_dec eq_dec v l).
  destruct (tree_avg_ex _ _ _ H H0). 
  unfold s,share in *. unfold dom.e,share in *. rewrite H2.
  apply tree_avg_bound in H2...
 Qed.

 Lemma round_avg_ctx: forall ctx ctxL ctxR h l,
  (cheight ctx l <= S h)%nat ->
   rL_ctx ctx (S h) l = ctxL -> rR_ctx ctx (S h) l = ctxR ->
  avg_ctx ctxL ctxR (S h) l = ctx.
 Proof with try tauto.
  intros.
  rewrite cheight_leq_rewrite in H.
  extensionality v.
  destruct (in_dec eq_dec v l).
  spec H v i.
  assert (|rL_ctx ctx (S h) l v| < S h) by (apply rL_ctx_lt;tauto).
  assert (|rR_ctx ctx (S h) l v| < S h) by (apply rR_ctx_lt;tauto).
  generalize (avg_ctx_in_var _ _ _ _ _ H2 H3 i);intro.
  generalize (rL_ctx_in_var _ _ _ _ H i);intro.
  generalize (rR_ctx_in_var _ _ _ _ H i);intro.
  generalize (tree_avg_round2avg _ _ _ _ H5 H6);intro.
  rewrite H0 in *. rewrite H1 in *.
  unfold s,share in *. unfold dom.e,share in *. rewrite H7 in H4. inv H4...
  generalize (avg_ctx_not_in_var ctxL ctxR (S h) _ _ n);intro.
  generalize (rL_ctx_not_in_var ctx (S h) _ _ n);intro.
  generalize (rR_ctx_not_in_var ctx (S h) _ _ n);intro.
  rewrite H2. 
  rewrite H0 in H3. rewrite H1 in H4.
  rewrite H3,H4.
  rewrite<- recompose_decompose. unfold s,dom.e,share,t in *. 
  destruct (@decompose canonTree _ (ctx v))...
 Qed.

 Lemma avg_round_ctx: forall ctx ctxL ctxR h l,
  cheight ctxL l < S h->
  cheight ctxR l < S h->
  avg_ctx ctxL ctxR (S h) l = ctx ->
  rL_ctx ctx (S h) l = ctxL /\ rR_ctx ctx (S h) l = ctxR.
 Proof with try tauto.
  intros. 
  split;extensionality v.
  destruct (in_dec eq_dec v l).
  rewrite cheight_lt_rewrite in H.
  rewrite cheight_lt_rewrite in H0.
  spec H v i. spec H0 v i.
  generalize (avg_ctx_in_var _ _ _ _ _ H H0 i);intro.
  generalize (avg_ctx_leq _ _ _ _ l H H0 i);intro.
  generalize (rL_ctx_in_var _ _ _ _ H3 i);intro.
  destruct (tree_avg_avg2round _ _ _ _ H2) as [? _].
  unfold s,share in *. unfold dom.e,share in *. rewrite H4 in H5. inv H5...
  generalize (avg_ctx_not_in_var ctxL ctxR (S h) _ _ n);intro.
  generalize (rL_ctx_not_in_var ctx (S h) _ _ n);intro.
  rewrite H1 in H2. rewrite H3. rewrite H2.
  rewrite decompose_recompose...
  destruct (in_dec eq_dec v l).
  rewrite cheight_lt_rewrite in H.
  rewrite cheight_lt_rewrite in H0.
  spec H v i. spec H0 v i.
  generalize (avg_ctx_in_var _ _ _ _ _ H H0 i);intro.
  generalize (avg_ctx_leq _ _ _ _ l H H0 i);intro.
  generalize (rR_ctx_in_var _ _ _ _ H3 i);intro.
  destruct (tree_avg_avg2round _ _ _ _ H2) as [_ ?].
  unfold s,share in *. unfold dom.e,share in *. rewrite H4 in H5. inv H5...
  generalize (avg_ctx_not_in_var ctxL ctxR (S h) _ _ n);intro.
  generalize (rR_ctx_not_in_var ctx (S h) _ _ n);intro.
  rewrite H1 in H2. rewrite H3. rewrite H2.
  rewrite decompose_recompose...
 Qed.

 Lemma rL_ctx_iden: forall ctx l n v,
  In v l ->
  |ctx v| < n ->
  rL_ctx ctx n l v =  ctx v.
 Proof with try tauto.
  intros.
  unfold rL_ctx.
  destruct (in_dec eq_dec v l)...
  generalize (tree_round_left_identity _ _ H0);intro.
  unfold s,share in *.
  unfold dom.e,share in *. rewrite H1...
 Qed.

 Lemma rR_ctx_iden: forall ctx l n v,
  In v l ->
  |ctx v| < n ->
  rR_ctx ctx n l v =  ctx v.
 Proof with try tauto.
  intros.
  unfold rR_ctx.
  destruct (in_dec eq_dec v l)...
  generalize (tree_round_right_identity _ _ H0);intro.
  unfold s,share in *.
  unfold dom.e,share in *. rewrite H1...
 Qed.

 Lemma avg_ctx_iden: forall ctx n v l,
  In v l ->
  |ctx v| < n ->
  avg_ctx ctx ctx n l v = ctx v.
 Proof with try tauto.
  intros.
  unfold avg_ctx.
  destruct (in_dec eq_dec v l)...
  apply tree_avg_identity in H0. 
  unfold s,share in *.
  unfold dom.e,share in *. rewrite H0...
 Qed.

 Lemma rLR_avg_ctx: forall ctxL ctxR v l n,
  |ctxL v| < n ->
  |ctxR v| < n ->
  rL_ctx (avg_ctx ctxL ctxR n l) n l v = ctxL v /\
  rR_ctx (avg_ctx ctxL ctxR n l) n l v = ctxR v.
 Proof.
  intros.
  unfold avg_ctx,rL_ctx,rR_ctx.
  destruct (in_dec eq_dec v l).
  destruct (tree_avg_ex _ _ _ H H0).
  unfold s,share in *.
  unfold dom.e,share in *. rewrite H1.
  apply tree_avg_avg2round in H1.
  destruct H1.
  rewrite H1,H2. split;trivial.
  repeat rewrite decompose_recompose.
  split;trivial.
 Qed.

 Lemma avg_ctx_in_obj_eval: forall l obj h ctxL ctxR,
  sublist (vars obj) l ->
  |obj| < h ->
  cheight ctxL l < h ->
  cheight ctxR l < h ->  
  avg h (get ctxL obj) (get ctxR obj) = Some (get (avg_ctx ctxL ctxR h l) obj).
 Proof with auto.
  intros. icase h. omega.
  destruct obj.
  assert (In v l). apply H. left...
  apply avg_ctx_in_var with (l:=l)...
  rewrite cheight_lt_rewrite in H1. apply H1...
  rewrite cheight_lt_rewrite in H2. apply H2...
  apply tree_avg_identity. simpl in *...
 Qed.

End Round_Average.


Module SAT_Base (sv : SV)
                (Import es : EQUATION_SYSTEM sv with Module dom := Share_Domain)
                (Import esf : SYSTEM_FEATURES sv es).

 Module RA := Round_Average sv es esf.
 Import RA.

 Definition SAT_avg_ctx_eval_spec 
  (A : Type) `{heightable A} `{evalable context A} 
  `{varsable A var} `{cheightable context A}:=
  forall ctxL ctxR l n (a : A),
  sublist (vars a) l -> |a| < n -> 
  cheight ctxL l < n -> cheight ctxR l < n -> 
  ctxL |= a -> ctxR |= a -> 
  avg_ctx ctxL ctxR n l |= a.

 Class avg_ctx_SAT_prop (A : Type) 
  `{heightable A} `{evalable context A} 
  `{varsable A var} `{cheightable context A} := Avg_ctx_SAT_prop {
   SAT_avg_eval: SAT_avg_ctx_eval_spec A
 }.

 Instance SAT_avg_ctx_eql: avg_ctx_SAT_prop equality. 
 Proof with try tauto.
  constructor.
  repeat intro.
  destruct a as [o1 o2].
  simpl in H,H0,H1,H2.
  rewrite sublist_app_iff in H.
  rewrite Nat.max_lub_lt_iff in H0.
  destruct H. destruct H0.
  generalize (avg_ctx_in_obj_eval _ _ _ _ _ H H0 H1 H2);intro.
  generalize (avg_ctx_in_obj_eval _ _ _ _ _ H5 H6 H1 H2);intro.
  simpl in *.
  rewrite H3,H4 in H7.
  rewrite H7 in H8. inv H8...
 Qed.

 Instance SAT_avg_ctx_eqn: avg_ctx_SAT_prop equation.
 Proof with try tauto.
  constructor.
  repeat intro.
  destruct a as [[o1 o2] o3].
  simpl in H,H0.
  repeat rewrite sublist_app_iff in H.
  repeat rewrite Nat.max_lub_lt_iff in H0.
  destruct H as [? [? ?]].
  destruct H0 as [[? ?] ?].
  generalize (avg_ctx_in_obj_eval _ _ _ _ _ H H0 H1 H2);intro.
  generalize (avg_ctx_in_obj_eval _ _ _ _ _ H5 H7 H1 H2);intro.
  generalize (avg_ctx_in_obj_eval _ _ _ _ _ H6 H8 H1 H2);intro.
  simpl in *...
  eapply tree_avg_join.
  apply H9. apply H10. apply H11. apply H3. apply H4.
 Qed.

 Instance SAT_avg_ctx_var : avg_ctx_SAT_prop var.
 Proof with try tauto.
  constructor.
  repeat intro.
  unfold avg_ctx in H5.
  assert (In a l). apply H. left...
  icase (in_dec eq_dec a l).
  icase n. omega.
  rewrite cheight_lt_rewrite in H1.
  rewrite cheight_lt_rewrite in H2.
  spec H1 a i. spec H2 a i.
  destruct (tree_avg_ex _ _ _ H1 H2).
  unfold s,share in *. unfold dom.e,share in *. rewrite H7 in H5.
  generalize (tree_avg_nonzero _ _ _ _ H7);intro.
  apply H8...
 Qed.

 Instance SAT_avg_ctx_list {A} `{avg_ctx_SAT_prop A} : avg_ctx_SAT_prop (list A).
 Proof with try tauto.
  constructor.
  induction a;intros...
  simpl in H4. rewrite sublist_app_iff in H4.
  destruct H4.
  destruct H8. destruct H9.
  rewrite height_rewrite in H5.
  rewrite Nat.max_lub_lt_iff in H5.
  destruct H5.
  generalize (IHa H10 H13 H6 H7 H8 H9);intro.
  split...
  apply H3...
 Qed.
 
 Instance SAT_avg_ctx_ses: avg_ctx_SAT_prop sat_equation_system.
 Proof with try tauto.
  constructor.
  repeat intro.
  destruct a as [l1 l2 l3].
  simpl in *.
  repeat rewrite sublist_app_iff in H. destruct H as [? [? ?]].
  unfold ses_h in H0. simpl in H0.
  rewrite Nat.max_lub_lt_iff in H0.
  destruct H0.
  unfold eval_sat_equation_system in *. simpl in *.
  destruct H3 as [? [? ?]].
  destruct H4 as [? [? ?]].
  split.
  generalize (SAT_avg_eval ctxL ctxR l n l2 H5 H0 H1 H2 H3 H4);intro.
  apply H12.
  split.
  generalize (SAT_avg_eval ctxL ctxR l n l3 H6 H7 H1 H2 H8 H10);intro.
  apply H12.
  assert (|l1| = 0). clear. induction l1...
  assert (|l1| < n) by omega.
  assert (l1 = vars l1).
   clear. induction l1... simpl. f_equal...
  rewrite H14 in H.
  generalize (SAT_avg_eval ctxL ctxR l n l1 H H13 H1 H2 H9 H11);intro.
  apply H15.
 Qed.

 Lemma SAT_nzvars_correct1: forall l ses,
  l <> nil ->
  (forall v, In v l -> sSAT ses v) ->
  SAT (replace_snzvars ses l).
 Proof with try tauto.
  induction l;intros...
  destruct (list_eq_dec eq_dec l nil). subst.
  apply H0. left...
  spec IHl ses n.
  destruct IHl.
  intros. apply H0. right...
  spec H0 a. destruct H0. left...
  remember (replace_snzvars ses (a::l)) as ses'.
  remember (S (max (max (cheight x0 (vars ses'))(cheight x (vars ses'))) (|replace_snzvars ses' nil|))) as h.
  exists (avg_ctx x x0 h (vars ses')).
  rewrite replace_snzvars_nil_eval.
  rewrite replace_snzvars_nil_eval in H0,H1.
  destruct H0. destruct H1.
  rewrite replace_snzvars_reduce in H0.
  rewrite replace_snzvars_reduce in H1.
  rewrite Heqses'.
  rewrite replace_snzvars_reduce. rewrite<- Heqses'.
  assert (max (max (cheight x0 (vars ses')) (cheight x (vars ses'))) (|replace_snzvars ses' nil|) < h) by omega.
  repeat rewrite Nat.max_lub_lt_iff in H4.
  destruct H4 as [[? ?] ?].
  assert (sublist (vars (replace_snzvars ses' nil)) (vars ses')).
   clear. repeat intro...
   destruct ses' as [l1 l2 l3]. simpl in *.
   rewrite in_app_iff in H.
   repeat rewrite in_app_iff...
  assert (replace_snzvars ses nil = replace_snzvars ses' nil).
   rewrite Heqses'. rewrite replace_snzvars_reduce...
  rewrite H8 in H1,H0.
  split.
  generalize (SAT_avg_eval _ _ _ _ _ H7 H6 H5 H4 H1 H0);intro.
  rewrite H8. apply H9.
  assert (sat_nzvars ses' = a::l).
   rewrite Heqses'. rewrite replace_snzvars_correct...
  rewrite H9.
  rewrite replace_snzvars_correct in H2.
  rewrite replace_snzvars_correct in H3.
  assert (sublist (a::l) (vars ses')).
   clear -H9. destruct ses' as [l1 l2 l3].
   simpl in *. subst.
   repeat intro. repeat rewrite in_app_iff.
   left...
  assert (x0 |= a). destruct  H2...
  clear -H3 H4 H5 H10 H11.
  rewrite list_eval_rewrite in H3.
  rewrite list_eval_rewrite. intros.
  assert (In e (vars ses')) by (apply H10;tauto).
  unfold eval,eval_nzvars.
  icase h. omega.
  rewrite cheight_lt_rewrite in H4.
  rewrite cheight_lt_rewrite in H5.
  spec H4 e H0. spec H5 e H0.
  generalize (avg_ctx_in_var _ _ _ _ _ H5 H4 H0);intro.
  apply tree_avg_nonzero in H1.
  apply H1. destruct H. subst.
  right. apply H11. left. apply H3...
 Qed.

End SAT_Base.

Module IMPL_Base (sv : SV)
                 (Import es : EQUATION_SYSTEM sv with Module dom := Share_Domain)
                 (Import esf : SYSTEM_FEATURES sv es).

 Require Import Classical.
 Import ClassicalProps.
 Module SB := SAT_Base sv es esf.
 Import SB.
 Module RA := Round_Average sv es esf.
 Import RA.

 Definition equiv_ctx:= fun (l : list var) (ctx ctx' : context) =>
  forall v, In v l -> ctx v = ctx' v.

 Definition eval_equiv_spec (A : Type) `{varsable A var} `{evalable context A}:=
  forall (a : A) ctx ctx',
  equiv_ctx (vars a) ctx ctx' ->
  (ctx |= a <-> ctx' |= a).

 Class eval_equiv_prop (A : Type) `{varsable A var} `{evalable context A} := 
  Eval_equiv_prop {
   eval_equiv: eval_equiv_spec A
 }.

 Lemma equiv_ctx_app_iff : forall ctx ctx' l l',
  equiv_ctx (l++l') ctx ctx' <-> equiv_ctx l ctx ctx' /\ equiv_ctx l' ctx ctx'.
 Proof with try tauto.
  intros.
  unfold equiv_ctx.
  split;intros.
  split;intros; apply H;rewrite in_app_iff...
  rewrite in_app_iff in H0.
  destruct H. destruct H0.
  apply H... apply H1...
 Qed.

 Lemma eval_equiv_prop_obj: forall (obj:object) ctx ctx',
  equiv_ctx (vars obj) ctx ctx' ->
  get_obj_val ctx obj = get_obj_val ctx' obj.
 Proof.
  intros. icase obj. simpl.
  apply H. left. trivial.
 Qed.

 Instance eval_equiv_prop_var: eval_equiv_prop var.
 Proof.
 constructor. repeat intro.
 spec H a. detach H. simpl. rewrite H. tauto.
 left. trivial.
 Qed.

 Instance eval_equiv_prop_eql: eval_equiv_prop equality.
 Proof.
 constructor. repeat intro.
 destruct a as [o1 o2].
 simpl in *.
 rewrite equiv_ctx_app_iff in H.
 destruct H.
 generalize (eval_equiv_prop_obj _ _ _ H);intro.
 generalize (eval_equiv_prop_obj _ _ _ H0);intro.
 unfold s in *.
 rewrite H1. rewrite H2. tauto.
 Qed.

 Instance eval_equiv_prop_eqn: eval_equiv_prop equation.
 Proof.
 constructor. repeat intro.
 destruct a as [[o1 o2] o3].
 simpl in H. repeat rewrite equiv_ctx_app_iff in H.
 destruct H as [? [? ?]].
 generalize (eval_equiv_prop_obj _ _ _ H);intro.
 generalize (eval_equiv_prop_obj _ _ _ H0);intro.
 generalize (eval_equiv_prop_obj _ _ _ H1);intro.
 simpl. unfold s in *.
 rewrite H2,H3,H4. tauto.
 Qed.

 Instance eval_equiv_prop_list {A} `{eval_equiv_prop A} : eval_equiv_prop (list A).
 Proof with try tauto.
 constructor. induction a;intros.
 simpl...
 simpl in H2. rewrite equiv_ctx_app_iff in H2.
 destruct H2.
 generalize (IHa _ _ H3);intro.
 generalize (eval_equiv _ _ _ H2);intro.
 simpl in *. tauto.
 Qed.

 Instance eval_equiv_prop_ses : eval_equiv_prop sat_equation_system.
 Proof with try tauto.
 constructor. repeat intro.
 destruct a as [l1 l2 l3].
 simpl in H. repeat rewrite equiv_ctx_app_iff in H.
 destruct H as [? [? ?]].
 assert (l1 = vars l1).
  clear.
  induction l1. simpl...
  simpl in *. rewrite<- IHl1...
 rewrite H2 in H.
 generalize (eval_equiv l1 _ _ H);intro.
 generalize (eval_equiv l2 _ _ H0);intro.
 generalize (eval_equiv l3 _ _ H1);intro.
 simpl in *. unfold eval_sat_equation_system;simpl...
 Qed.

 Definition neg_IMPL (is : impl_system) :=
  exists ctx, ctx |= fst is /\ ~ ctx |= snd is.
 Definition neg_sIMPL (is : impl_system) (x y : var) :=
  neg_IMPL (replace_isnzvars is (x::nil) (y::nil)).
 Definition neg_zIMPL (is : impl_system) (y : var) : Prop :=
  neg_IMPL (replace_isnzvars is nil (y::nil)).

 Definition sIMPL_Cond (is : impl_system): Prop :=
  forall y, In y (impl_nzvars (snd is)) ->
  exists x, In x (impl_nzvars (fst is)) /\ sIMPL is x y.
 Definition zIMPL_Cond (is : impl_system) : Prop :=
  forall y, In y (impl_nzvars (snd is)) -> zIMPL is y.
 Definition F (is : impl_system): Prop :=
  forall y, In y (impl_nzvars (snd is)) ->
  IMPL (replace_isnzvars is (impl_nzvars (fst is)) (y::nil)).
 Definition neg_sIMPL_Cond (is : impl_system): Prop :=
  exists y, In y (impl_nzvars (snd is)) /\
  (forall x, In x (impl_nzvars (fst is)) -> ~sIMPL is x y).

 Lemma neg_sIMPL_Cond_correct: forall is, 
  ~sIMPL_Cond is <-> neg_sIMPL_Cond is.
 Proof with try tauto.
  intro is. unfold sIMPL_Cond,neg_sIMPL_Cond.
  split;repeat intro.
  rewrite neg_forall in H.
  destruct H as [y H]. exists y.
  rewrite neg_impl in H.
  split... destruct H.
  rewrite neg_ex in H0...
  repeat intro. spec H0 x. apply H0...
  destruct H as [y [H H1]].
  destruct (H0 y H) as [x [H2 H3]].
  spec H1 x H2...
 Qed.

 Lemma neg_IMPL_correct: forall is, 
  ~IMPL is <-> neg_IMPL is.
 Proof.
  intros.
  unfold IMPL,neg_IMPL.
  split;repeat intro.
  rewrite neg_forall in H.
  destruct H as [ctx H]. exists ctx.
  rewrite<- neg_impl. apply H.
  destruct H as [ctx [H1 H2]].
  spec H0 ctx. apply H0 in H1. tauto.
 Qed.

 Lemma neg_sIMPL_correct: forall is x y, 
 (~sIMPL is x y) <-> neg_sIMPL is x y.
 Proof.
  intros.
  unfold sIMPL,neg_sIMPL.
  apply neg_IMPL_correct.
 Qed.

 Lemma neg_zIMPL_correct: forall is y,
  ~zIMPL is y <-> neg_zIMPL is y.
 Proof.
  intros.
  unfold zIMPL,neg_zIMPL,IMPL,neg_IMPL.
  split;repeat intro.
  rewrite neg_forall in H.
  destruct H as [ctx H]. exists ctx.
  rewrite<- neg_impl. apply H.
  destruct H as [ctx [H1 H2]].
  spec H0 ctx. apply H0 in H1. tauto.
 Qed.

 Definition IMPL_avg_ctx_eval_spec 
  (A : Type) `{heightable A} `{evalable context A} 
  `{varsable A var} `{cheightable context A}:=
  forall ctxL ctxR l n (a : A),
  sublist (vars a) l -> |a| < n -> 
  cheight ctxL l < n -> cheight ctxR l < n -> 
  avg_ctx ctxL ctxR n l |= a ->
  ctxL |= a /\ ctxR |= a.

 Class avg_ctx_IMPL_prop (A : Type) 
  `{heightable A} `{evalable context A} 
  `{varsable A var} `{cheightable context A} := Avg_ctx_IMPL_prop {
   IMPL_avg_eval: IMPL_avg_ctx_eval_spec A
 }.

 Instance IMPL_avg_ctx_eql: avg_ctx_IMPL_prop equality. 
 Proof with try tauto.
 constructor.
 repeat intro.
 destruct a as [o1 o2].
 simpl in H,H0,H1,H2.
 rewrite sublist_app_iff in H.
 rewrite Nat.max_lub_lt_iff in H0.
 destruct H. destruct H0.
 generalize (avg_ctx_in_obj_eval _ _ _ _ _ H H0 H1 H2);intro.
 generalize (avg_ctx_in_obj_eval _ _ _ _ _ H4 H5 H1 H2);intro.
 simpl in *.
 rewrite H3 in H6.
 apply tree_avg_avg2round in H6.
 apply tree_avg_avg2round in H7. 
 simpl in *. destruct H6. destruct H7.
 rewrite H6 in H7. rewrite H8 in H9.
 inv H7. inv H9...
 Qed.

 Instance IMPL_avg_ctx_eqn: avg_ctx_IMPL_prop equation.
 Proof with try tauto.
  constructor.
  repeat intro.
  destruct a as [[o1 o2] o3].
  simpl in H,H0.
  repeat rewrite sublist_app_iff in H.
  repeat rewrite Nat.max_lub_lt_iff in H0.
  destruct H as [? [? ?]].
  destruct H0 as [[? ?] ?].
  generalize (avg_ctx_in_obj_eval _ _ _ _ _ H H0 H1 H2);intro.
  generalize (avg_ctx_in_obj_eval _ _ _ _ _ H4 H6 H1 H2);intro.
  generalize (avg_ctx_in_obj_eval _ _ _ _ _ H5 H7 H1 H2);intro.
  apply tree_avg_avg2round in H8.
  apply tree_avg_avg2round in H9.
  apply tree_avg_avg2round in H10.
  destruct H8. destruct H9. destruct H10.
  generalize (tree_round_left_join _ _ _ _ _ _ _ H3 H8 H9 H10);intro.
  generalize (tree_round_right_join _ _ _ _ _ _ _ H3 H11 H12 H13);intro...
 Qed.

 Instance IMPL_avg_ctx_list {A} `{avg_ctx_IMPL_prop A} : avg_ctx_IMPL_prop (list A).
 Proof with try tauto.
  constructor.
  induction a;intros...
  simpl in H4. rewrite sublist_app_iff in H4.
  destruct H4. destruct H8.
  rewrite height_rewrite in H5.
  rewrite Nat.max_lub_lt_iff in H5.
  destruct H5.
  generalize (IHa H9 H11 H6 H7 H8);intro.
  split; split;
  try apply H3 with (ctxL:=ctxL)(ctxR:=ctxR)(l:=l)(n:=n)...
 Qed.

 Lemma IMPL_avg_ctx_list_var: forall L l l' ctxL ctxR n,
  ctxL |= l -> ctxR |= l' -> 
  sublist l L -> sublist l' L ->
  cheight ctxL L < n -> cheight ctxR L < n ->
  avg_ctx ctxL ctxR n L |= (l++l').
 Proof with try tauto.
  intros.
  rewrite list_eval_rewrite. intros.
  rewrite list_eval_rewrite in H.
  rewrite list_eval_rewrite in H0.
  icase n. omega.
  rewrite cheight_lt_rewrite in H3.
  rewrite cheight_lt_rewrite in H4.
  rewrite in_app_iff in H5.
  assert (In e L). destruct H5. apply H1... apply H2...
  spec H3 e H6. spec H4 e H6.
  simpl.
  rewrite tree_avg_nonzero with (sL:=ctxL e) (sR:=ctxR e) (n:=S n)...
  destruct H5. left. apply H... right. apply H0...
  apply avg_ctx_in_var... 
 Qed.
  
 Lemma IMPL_avg_ctx_ses: forall ctxL ctxR l n (ses : sat_equation_system),
  sublist (vars (replace_snzvars ses nil)) l -> 
  |(replace_snzvars ses nil)| < n -> 
  cheight ctxL l < n -> cheight ctxR l < n -> 
  avg_ctx ctxL ctxR n l |= (replace_snzvars ses nil) ->
  ctxL |= (replace_snzvars ses nil) /\ ctxR |= (replace_snzvars ses nil).
 Proof with try tauto.
  intros.
  destruct ses as [l1 l2 l3].
  simpl in *. unfold ses_h in H0. simpl in *.
  rewrite sublist_app_iff in H.
  rewrite Nat.max_lub_lt_iff in H0.
  destruct H3 as [? [? ?]]. simpl in *.
  destruct H. destruct H0.
  generalize (IMPL_avg_eval ctxL ctxR l n l2 H H0 H1 H2 H3);intro.
  generalize (IMPL_avg_eval ctxL ctxR l n l3 H6 H7 H1 H2 H4);intro.
  split; split...
 Qed.

 Lemma ses_single_nzvar: forall (ses : sat_equation_system) n ctx v l,
  sat_nzvars ses = v ::nil ->
  |ses| < n ->
  sublist (vars ses) l ->
  le (cheight ctx l) n ->
  ctx |= ses ->
  rL_ctx ctx n l |= ses \/ rR_ctx ctx n l |= ses.
 Proof with try tauto.
  intros.
  rewrite replace_snzvars_nil_eval in H3.
  rewrite H in H3.
  destruct H3.
  assert (ctx v <> emptyshare).
   destruct H4. apply H5. clear H4.
  remember (rL_ctx ctx n l) as ctxL.
  remember (rR_ctx ctx n l) as ctxR.
  symmetry in HeqctxL,HeqctxR.
  icase n. omega.
  generalize (round_avg_ctx _ _ _ _ _ H2 HeqctxL HeqctxR);intro.
  assert (In v l).
   apply H1. destruct ses as [l1 l2 l3]. simpl.
   simpl in H. rewrite H. rewrite in_app_iff.
   left. left. tauto.
  assert (ctxL v <> emptyshare \/ ctxR v <> emptyshare).
    rewrite<- tree_avg_nonzero. apply H5.
    rewrite cheight_leq_rewrite in H2. spec H2 v H6.
    generalize (rL_ctx_in_var _ _ _ _ H2 H6);intro.
    generalize (rR_ctx_in_var _ _ _ _ H2 H6);intro.
    generalize (rL_ctx_lt _ _ _ _ H2 H6);intro.
    generalize (rR_ctx_lt _ _ _ _ H2 H6);intro.
    rewrite HeqctxL in H7,H9.
    rewrite HeqctxR in H8,H10.
    generalize (avg_ctx_in_var _ _ _ _ _ H9 H10 H6);intro.
    rewrite H4 in H11.
    apply H11.
  rewrite <- H4 in H3.
  apply IMPL_avg_ctx_ses in H3... destruct H3.
  destruct H7.
  left. rewrite replace_snzvars_nil_eval.
  split... rewrite H. split... simpl...
  right. rewrite replace_snzvars_nil_eval.
  split... rewrite H. split... simpl...
  repeat intro. apply H1.
  destruct ses as [l1 l2 l3]. simpl;simpl in H8.
  rewrite in_app_iff. right...
  rewrite cheight_lt_rewrite.
  rewrite cheight_leq_rewrite in H2.
  intros. spec H2 v0 H8.
  rewrite <-HeqctxL. apply rL_ctx_lt...
  rewrite cheight_lt_rewrite.
  rewrite cheight_leq_rewrite in H2.
  intros. spec H2 v0 H8.
  rewrite <-HeqctxR. apply rR_ctx_lt...  
 Qed.

 Lemma override_eval_height: forall (ses:sat_equation_system) ctx ctx' l l' v,
  sat_nzvars ses = v::nil ->
  [l => ctx']ctx |= ses ->
  sublist l l' ->
  exists ctx'', (cheight ctx'' l' <= max (cheight ctx ((vars ses)++l')) (|ses|))%nat /\ 
  [l => ctx'']ctx |= ses.
 Proof with try tauto.
  do 6 intro.
  assert (exists m, le (cheight ctx' l') m). apply exists_le.
  destruct H as [m H].
  revert H. revert ctx'. induction m;intros.
  exists ctx'. split... omega.
  destruct (le_dec (cheight ctx' l') (max (cheight ctx ((vars ses)++l')) (|ses |))).
  exists ctx'. split...
  assert (max (cheight ctx ((vars ses)++l')) (|ses|) < cheight ctx' l') by omega.
  clear n. rewrite Nat.max_lub_lt_iff in H3. destruct H3.
  generalize (ses_single_nzvar _ _ ([l => ctx']ctx) _ ((vars ses)++l') H0 H4);intro.
  repeat detach H5... destruct H5.

  apply IHm with (rL_ctx ctx' (cheight ctx' l') (vars ses ++ l'))...
  rewrite cheight_leq_rewrite. intros.
  assert (le (|ctx' v0|) (cheight ctx' l')).
  eapply cheight_leq_rewrite. apply le_refl. tauto.
  icase (cheight ctx' l'). omega.
  generalize (rL_ctx_lt _ _ _ _ H7 H6);intro.
  generalize (rL_ctx_in_var _ _ _ _ H7 H6);intro.
  assert (In v0 (vars ses ++ l')).
   rewrite in_app_iff. right...
  generalize (rL_ctx_in_var _ _ _ _ H7 H10);intro.
  rewrite H9 in H11. inv H11. 
  simpl. rewrite <-H13. simpl in *;omega.
  rewrite rL_ctx_override in H5. 
  eapply eval_equiv. Focus 2. apply H5.
  repeat intro. 
  destruct (in_dec eq_dec v0 l).
  repeat rewrite override_in...
  repeat rewrite override_not_in...
  rewrite rL_ctx_iden...
  rewrite in_app_iff...
  icase (cheight ctx' l'). omega.
  rewrite cheight_lt_rewrite in H3. apply H3.
  rewrite in_app_iff...

  apply IHm with (rR_ctx ctx' (cheight ctx' l') (vars ses ++ l'))...
  rewrite cheight_leq_rewrite. intros.
  assert (le (|ctx' v0|) (cheight ctx' l')).
  eapply cheight_leq_rewrite. apply le_refl. tauto.
  icase (cheight ctx' l'). omega.
  generalize (rR_ctx_lt _ _ _ _ H7 H6);intro.
  generalize (rR_ctx_in_var _ _ _ _ H7 H6);intro.
  assert (In v0 (vars ses ++ l')).
   rewrite in_app_iff. right...
  generalize (rR_ctx_in_var _ _ _ _ H7 H10);intro.
  rewrite H9 in H11. inv H11. 
  simpl. rewrite <-H13. simpl in *;omega.
  rewrite rR_ctx_override in H5. 
  eapply eval_equiv. Focus 2. apply H5.
  repeat intro.
  destruct (in_dec eq_dec v0 l).
  repeat rewrite override_in...
  repeat rewrite override_not_in...
  rewrite rR_ctx_iden...
  rewrite in_app_iff...
  icase (cheight ctx' l'). omega.
  rewrite cheight_lt_rewrite in H3. apply H3.
  rewrite in_app_iff...

  rewrite cheight_leq_rewrite. intros.
  rewrite in_app_iff in H5. destruct H5.
  destruct (in_dec eq_dec v0 l).
  rewrite override_in...
  assert ((cheight ctx' l' <= cheight ctx' l')%nat) by omega.
  rewrite cheight_leq_rewrite in H6. apply H6.
  apply H2...
  rewrite override_not_in...
  icase (cheight ctx' l'). omega.
  rewrite cheight_lt_rewrite in H3.
  spec H3 v0. detach H3. omega.
  rewrite in_app_iff. left...
  destruct (in_dec eq_dec v0 l).
  rewrite override_in...
  eapply cheight_leq_rewrite...
  apply le_refl. tauto.
  rewrite override_not_in...
  icase (cheight ctx' l'). omega.
  rewrite cheight_lt_rewrite in H3.
  spec H3 v0. detach H3. omega.
  rewrite in_app_iff. right...
  repeat intro. rewrite in_app_iff. left...
 Qed.

 Lemma rLR_ctx_eval: forall (n : nat) ctx l (ses : sat_equation_system),
  sat_nzvars ses = nil ->
  ctx |= ses ->
  |ses| < n ->
  le (cheight ctx l) n ->
  sublist (vars ses) l ->
  rL_ctx ctx n l |= ses /\ rR_ctx ctx n l |= ses.
 Proof with try tauto.
  intros.
  assert (replace_snzvars ses nil = ses).
   rewrite<-H. rewrite replace_snzvars_id...
  rewrite<-H4 in *.
  icase n;try omega.
  remember (rL_ctx ctx (S n) l) as ctxL.
  remember (rR_ctx ctx (S n) l) as ctxR.
  symmetry in HeqctxL,HeqctxR.
  generalize (round_avg_ctx _ _ _ _ _ H2 HeqctxL HeqctxR);intro.
  rewrite <-H5 in H0.
  rewrite cheight_leq_rewrite in H2.
  apply IMPL_avg_ctx_ses with (l:=l)(n:=S n)...
  rewrite cheight_lt_rewrite. intros.
  subst ctxL. apply rL_ctx_lt... apply H2...
  rewrite cheight_lt_rewrite. intros.
  subst ctxR. apply rR_ctx_lt... apply H2...
 Qed.

 Lemma override_eval_height_2: forall (ses:sat_equation_system) ctx ctx' l l',
  sat_nzvars ses = nil ->
  [l => ctx']ctx |= ses ->
  sublist l l' ->
  exists ctx'', (cheight ctx'' l' <= max (cheight ctx ((vars ses)++l')) (|ses|))%nat /\ 
  [l => ctx'']ctx |= ses.
 Proof with try tauto.
  do 6 intro.
  assert (exists m, le (cheight ctx' l') m). apply exists_le.
  destruct H0 as [m H0].
  revert H0. revert ctx'. induction m;intros.
  exists ctx'. split... omega.
  destruct (le_dec (cheight ctx' l') (max (cheight ctx ((vars ses)++l')) (|ses |))).
  exists ctx'. split...
  assert (max (cheight ctx ((vars ses)++l')) (|ses|) < cheight ctx' l') by omega.
  clear n. rewrite Nat.max_lub_lt_iff in H3. destruct H3.
  assert (le (cheight ([l => ctx']ctx) (vars ses ++ l'))  (cheight ctx' l') ).
   rewrite cheight_leq_rewrite;intros.
   destruct (in_dec eq_dec v l).
   rewrite override_in...
   eapply cheight_leq_rewrite. apply le_refl. apply H2...
   rewrite override_not_in...
   icase (cheight ctx' l'). omega.
   rewrite cheight_lt_rewrite in H3.
   spec H3 v. detach H3... omega.
  assert (sublist (vars ses) (vars ses ++ l')).
   repeat intro. rewrite in_app_iff...
  destruct (rLR_ctx_eval _ _ _ _ H H1 H4 H5 H6) as [H7 _].
  apply IHm with (ctx':=rL_ctx ctx' (cheight ctx' l') (vars ses++l'))...
  rewrite cheight_leq_rewrite;intros.
  assert (le (|ctx' v|) (cheight ctx' l')).
  eapply cheight_leq_rewrite. apply le_refl. apply H8.
  icase (cheight ctx' l'). omega.
  apply rL_ctx_lt with (l:=vars ses ++l')in H9... omega.
  rewrite in_app_iff...
  rewrite rL_ctx_override in H7.
  eapply eval_equiv. Focus 2. apply H7.
  repeat intro.
  destruct (in_dec eq_dec v l).
  repeat rewrite override_in...
  repeat rewrite override_not_in...
  symmetry. apply rL_ctx_iden...
  rewrite in_app_iff...
  icase (cheight ctx' l'). omega.
  rewrite cheight_lt_rewrite in H3.
  spec H3 v. detach H3. omega.
  rewrite in_app_iff...
 Qed.

 Lemma IMPL_F_equiv: forall is,
 (impl_nzvars (snd is) <> nil) ->
 (IMPL is <-> F is).
 Proof with try tauto.
  intros.
  split. repeat intro.
  destruct is as [ies1 ies2].
  rewrite fst_replace_isnzvars in H2.
  rewrite snd_replace_isnzvars.
  spec H0 rho. apply H0 in H2.
  rewrite replace_inzvars_nil_eval in H2.
  rewrite replace_inzvars_nil_eval.
  destruct H2 as [ctx [H2 H3]].
  exists ctx. simpl in *.
  split... split...
  eapply list_eval_rewrite in H1. apply H1. apply H3.

  remember (impl_nzvars (snd is)) as l.
  revert Heql. revert is.
  induction l;intros. tauto.
  generalize (H0 a);intro.
  assert (In a (impl_nzvars (snd is))).
   rewrite<- Heql. left...
  spec H1 H2.
  destruct (list_eq_dec eq_dec l nil). subst. intros ctx H3.
  spec H0 a. detach H0.
  Focus 2. rewrite <-Heql. left...
  spec H0 ctx.
  rewrite replace_isnzvars_eval in H0.
  rewrite replace_inzvars_id in H0.
  spec H0 H3.
  rewrite Heql in H0.
  rewrite replace_inzvars_id in H0...
  spec IHl n (replace_isnzvars is (impl_nzvars (fst is)) l).
  detach IHl. detach IHl.
  intros ctx H3.
  spec H1 ctx. spec IHl ctx.
  rewrite replace_isnzvars_eval in H1,IHl.
  rewrite replace_inzvars_id in H1,IHl.
  spec H1 H3. spec IHl H3.
  destruct H1 as [ctx1 H1].
  destruct IHl as [ctx2 IHl].
  rewrite replace_inzvars_exvars in *.
  rewrite replace_inzvars_ies2ses in *.
  assert (exists n, max (|(snd is)|) 
  (max (cheight ([impl_exvars (snd is) => ctx1]ctx) (vars (snd is))) 
       (cheight ([impl_exvars (snd is) => ctx2]ctx) (vars (snd is)))) < n) by apply exist_lt.
  destruct H4 as [m H4].
  repeat rewrite Nat.max_lub_lt_iff in H4.
  destruct H4 as [? [? ?]].
  rewrite replace_snzvars_nil_eval in H1,IHl.
  rewrite replace_snzvars_reduce in *.
  rewrite replace_snzvars_correct in *.
  destruct H1 as [H7 H8].
  destruct IHl as [H9 H10].
  assert (sublist (vars (replace_snzvars (ies2ses (snd is)) nil)) (vars (snd is))).
   repeat intro. 
   destruct (snd is) as [l1 l2 l3 l4]. simpl in *.
   rewrite in_app_iff. right. rewrite in_app_iff...
  generalize (SAT_avg_eval _ _ _ _ _ H1 H4 H5 H6 H7 H9);intro H11.
  rewrite avg_override in H11.
  exists (avg_ctx ctx1 ctx2 m (vars (snd is))).
  rewrite replace_snzvars_nil_eval.
  split.
  eapply eval_equiv. Focus 2. apply H11.
  repeat intro.
  destruct (in_dec eq_dec v (impl_exvars (snd is))).
  repeat rewrite override_in...
  repeat rewrite override_not_in...
  symmetry. apply avg_ctx_iden.
  apply H1...
  icase m. omega.
  rewrite cheight_lt_rewrite in H5.
  spec H5 v. rewrite override_not_in in H5...
  apply H5. apply H1...
  
  (*Eval list*)
  assert (sat_nzvars (ies2ses (snd is)) = a ::l).
   clear - Heql. destruct (snd is) as [l1 l2 l3 l4].
   simpl in *. rewrite Heql...
  rewrite H12.
  assert (sublist (a::l) (vars (snd is))).
   clear - Heql. destruct (snd is) as [l1 l2 l3 l4].
  simpl in *. subst.
  repeat intro.
  rewrite in_app_iff. right. rewrite in_app_iff. left...
  generalize (IMPL_avg_ctx_list_var (vars (snd is)) _ _ _ _ m H8 H10);intro H14.
  repeat detach H14...
  rewrite avg_override in H14.
  eapply eval_equiv in H14. apply H14.
  repeat intro.
  destruct (in_dec eq_dec v (impl_exvars (snd is))).
  repeat rewrite override_in...
  repeat rewrite override_not_in...
  symmetry. apply avg_ctx_iden...
  apply H13. 
  simpl in H15. destruct H15. left...
  right. rewrite<- vars_var_list. simpl...
  icase m. omega.
  rewrite cheight_lt_rewrite in H5.
  spec H5 v. detach H5. rewrite override_not_in in H5...
  apply H13.
  simpl in H15. destruct H15. left...
  right. rewrite<- vars_var_list. simpl...
  repeat intro. apply H13. right...
  repeat intro. apply H13. left. destruct H14...

  repeat intro.
  repeat rewrite fst_replace_isnzvars in *.
  repeat rewrite snd_replace_isnzvars in *.
  repeat rewrite replace_inzvars_reduce in *.
  rewrite replace_inzvars_correct in *.
  rewrite replace_inzvars_id in *.
  spec H0 y. detach H0. spec H0 rho.
  rewrite replace_isnzvars_eval in H0.
  rewrite replace_inzvars_id in *.
  apply H0...
  rewrite<-Heql. right...
  destruct is as [ies1 ies2]. simpl...
 Qed.
  
 Lemma neg_sIMPL_combine: forall l is y,
  l <> nil ->
  (forall x, In x l -> neg_sIMPL is x y) ->
  neg_IMPL (replace_isnzvars is l (y::nil)).
 Proof with try tauto.
  induction l;intros...
  generalize (H0 a);intro.
  destruct H1 as [ctx H1]. left...
  destruct (list_eq_dec eq_dec l nil). subst.
  exists ctx...

  (*Pre-processing, very tedious...*)
  spec IHl is y n.
  destruct IHl as [ctx' H2].
  intros. apply H0. right...
  rewrite fst_replace_isnzvars in H1,H2.
  rewrite snd_replace_isnzvars in H1,H2.
  destruct H1 as [H1L H1R]. destruct H2 as [H2L H2R].
  destruct H1L as [ctx1 H1L].
  destruct H2L as [ctx2 H2L].
  rewrite replace_inzvars_ies2ses in H1L,H2L.
  rewrite replace_inzvars_exvars in H1L,H2L.
  remember (impl_exvars (fst is)) as lex1.
  remember (replace_isnzvars is (a::l) (y::nil)) as is'.
  assert (exists m, cheight ctx1 lex1 < m /\ cheight ctx2 lex1 < m /\
                    cheight ctx  (vars is') < m /\ cheight ctx' (vars is') < m /\
                    |replace_isnzvars is (a::l) (y::nil)| < m).
   exists (1 + (cheight ctx1 lex1) + (cheight ctx2 lex1) + ( cheight ctx  (vars is')) +
           (cheight ctx' (vars is')) + (|replace_isnzvars is (a::l) (y::nil)|)). omega.
  destruct H1 as [m [? [? [? [? ?]]]]].
  destruct is as [ies1 ies2]. unfold fst,snd in *.
  unfold replace_isnzvars in H5.
  simpl in H5. unfold is_h in H5.
  rewrite Nat.max_lub_lt_iff in H5. unfold fst,snd in H5.
  destruct H5 as [H5 H6].
  exists (avg_ctx ctx ctx' m (vars is')).
  
  (*First goal*)
  split. exists (avg_ctx ctx1 ctx2 m (vars is')).
  rewrite<- avg_override.
  assert (impl_exvars (fst is') = impl_exvars ies1 /\ 
          ies2ses (fst is') = replace_snzvars (ies2ses ies1) (a::l)).
   clear - Heqis'.
   destruct is' as [ies1' ies2']. inv Heqis'.
   simpl. split...
  destruct H7 as [H7 H8]. rewrite H7,H8. clear H7 H8.
  rewrite<- Heqlex1.
  rewrite replace_snzvars_nil_eval in *.
  rewrite replace_snzvars_reduce in *.
  rewrite replace_snzvars_correct in *.
  destruct H1L as [H1L H1L'].
  destruct H2L as [H2L H2L'].
  assert (H7 : cheight ([lex1 => ctx1]ctx) (vars is') < m).
   icase m. omega. rewrite cheight_lt_rewrite.
   repeat intro. destruct (in_dec eq_dec v lex1).
   rewrite override_in... 
   rewrite cheight_lt_rewrite in H1. apply H1...
   rewrite override_not_in...
   rewrite cheight_lt_rewrite in H3. apply H3...
  assert (H8 : cheight ([lex1 => ctx2]ctx') (vars is') < m).
   icase m. omega. rewrite cheight_lt_rewrite.
   repeat intro. destruct (in_dec eq_dec v lex1).
   rewrite override_in... 
   rewrite cheight_lt_rewrite in H2. apply H2...
   rewrite override_not_in...
   rewrite cheight_lt_rewrite in H4. apply H4...
  split. apply SAT_avg_ctx_ses...
  subst. destruct ies1 as [l1 l2 l3 l4].
  simpl. repeat intro.
  replace (a :: l ++ vars_list l3 ++ vars_list l4) with
  ((a::l)++(vars_list l3)++(vars_list l4)) by tauto.
  repeat rewrite in_app_iff.
  rewrite in_app_iff in H9...
  replace (a::l) with ((a::nil)++l) by tauto.
  apply IMPL_avg_ctx_list_var...
  subst. simpl.
  repeat intro. rewrite in_app_iff. left.
  rewrite in_app_iff. right. left. inv H9...
  subst. simpl.
  repeat intro. rewrite in_app_iff. left.
  rewrite in_app_iff. right. right.
  rewrite in_app_iff. left...

  (*Second goal*)
  intro.
  destruct H7 as [ctx_r H7].
  assert (impl_exvars (snd is') = impl_exvars ies2 /\ 
          ies2ses (snd is') = replace_snzvars (ies2ses ies2) (y::nil)).
   clear - Heqis'.
   destruct is' as [ies1' ies2']. inv Heqis'.
   simpl. split...
  destruct H8. rewrite H8,H9 in H7. clear H8 H9.
  apply override_eval_height with (v:=y) (l':= vars is') in H7.
  destruct H7 as [ctx'' [H7 H8]].
  icase m. omega.
  assert (H9 : (cheight ctx'' (vars is') <= S m)%nat).
   rewrite Nat.max_le_iff in H7. destruct H7.
   assert ((cheight (avg_ctx ctx ctx' (S m) (vars is')) (vars is') <= S m)%nat).
    rewrite cheight_leq_rewrite.
    intros.
    rewrite avg_ctx_leq... omega.
    rewrite cheight_lt_rewrite in H3. apply H3...
    rewrite cheight_lt_rewrite in H4. apply H4...
    eapply le_trans. apply H7.
    eapply le_trans. Focus 2. apply H9.
    apply cheight_sublist.
    repeat intro. subst is'.
    destruct ies2 as [l1 l2 l3 l4].
    clear - H10.
    simpl in *. rewrite in_app_iff.
    destruct H10. subst. right.
    rewrite in_app_iff. right. left...
    rewrite in_app_iff in H. destruct H.
    right. rewrite in_app_iff. right. right...
    destruct ies1 as [l5 l6 l7 l8]. simpl in *.
    rewrite in_app_iff in H. destruct H. left... right...
   assert (|replace_snzvars (ies2ses ies2) (y :: nil) | = |replace_inzvars ies2 (y :: nil) |) by tauto.
   omega.
  remember (rL_ctx ctx'' (S m) (vars is')) as ctxL.
  remember (rR_ctx ctx'' (S m) (vars is')) as ctxR.
  symmetry in HeqctxL,HeqctxR.
  generalize (round_avg_ctx _ _ _ _ _ H9 HeqctxL HeqctxR);intro.
  rewrite <-H10 in H8.
  rewrite<- avg_override in H8.
  rewrite replace_snzvars_nil_eval in H8.
  rewrite replace_snzvars_reduce,replace_snzvars_correct in H8.
  destruct H8 as [H8L H8R].
  assert (Hy : In y (vars is')).
   subst is'.
   simpl. rewrite in_app_iff. right.
   rewrite in_app_iff. right. left...
  apply IMPL_avg_ctx_ses in H8L...
  assert ([impl_exvars ies2 => ctxL]ctx y <> emptyshare \/ 
          [impl_exvars ies2 => ctxR]ctx' y <> emptyshare).
   assert (avg_ctx ([impl_exvars ies2 => ctxL]ctx)
        ([impl_exvars ies2 => ctxR]ctx') (S m) (vars is') y <> emptyshare).
    destruct H8R...        
   rewrite<- tree_avg_nonzero.
   apply H8.  
   apply avg_ctx_in_var...
   destruct (in_dec eq_dec y (impl_exvars ies2)).
   rewrite override_in...
   subst ctxL. apply rL_ctx_lt...
   rewrite cheight_leq_rewrite in H9.
   apply H9...
   rewrite override_not_in...
   rewrite cheight_lt_rewrite in H3.
   apply H3...
   destruct (in_dec eq_dec y (impl_exvars ies2)).
   rewrite override_in...
   subst ctxR. apply rR_ctx_lt...
   rewrite cheight_leq_rewrite in H9.
   apply H9...
   rewrite override_not_in...
   rewrite cheight_lt_rewrite in H4.
   apply H4...
  destruct H8.
  apply H1R.
  exists ctxL.
  rewrite replace_inzvars_exvars.
  rewrite replace_inzvars_ies2ses.
  rewrite replace_snzvars_nil_eval.
  rewrite replace_snzvars_reduce,replace_snzvars_correct.
  split... split... simpl...
  apply H2R.
  exists ctxR.
  rewrite replace_inzvars_exvars.
  rewrite replace_inzvars_ies2ses.
  rewrite replace_snzvars_nil_eval.
  rewrite replace_snzvars_reduce,replace_snzvars_correct.
  split... split... simpl...
  subst is'. 
  destruct ies2 as [l1 l2 l3 l4]. simpl.
  repeat intro. rewrite in_app_iff. right.
  rewrite in_app_iff. right. right...
  rewrite cheight_lt_rewrite. intros.
  destruct (in_dec eq_dec v (impl_exvars ies2)).
  rewrite override_in...
  subst ctxL. apply rL_ctx_lt...
  rewrite cheight_leq_rewrite in H9.
  apply H9...
  rewrite override_not_in...
  rewrite cheight_lt_rewrite in H3.
  apply H3... 
  rewrite cheight_lt_rewrite. intros.
  destruct (in_dec eq_dec v (impl_exvars ies2)).
  rewrite override_in...
  subst ctxR. apply rR_ctx_lt...
  rewrite cheight_leq_rewrite in H9.
  apply H9...
  rewrite override_not_in...
  rewrite cheight_lt_rewrite in H4.
  apply H4...
  rewrite replace_snzvars_correct...
  subst. repeat intro.
  destruct ies1 as [l1 l2 l3 l4];
  destruct ies2 as [l5 l6 l7 l8].
  simpl in *. repeat rewrite in_app_iff...
 Qed.

 Lemma F_sIMPL_Cond_equiv: forall is, 
 (impl_nzvars (fst is) <> nil) ->
 (F is <-> sIMPL_Cond is).
 Proof with try tauto.
  intros. split;intros.
  icase (classic (sIMPL_Cond is)).
  rewrite neg_sIMPL_Cond_correct in H1.
  destruct H1 as [y [H2 H3]].
  spec H0 y H2.
  assert (forall x, In x (impl_nzvars (fst is)) -> neg_sIMPL is x y).
   intros. apply neg_sIMPL_correct. apply H3...
  assert (exists ctx, ctx |= (fst is) /\ ~ctx |= replace_inzvars (snd is) (y::nil)).
   apply neg_sIMPL_combine in H1...
   destruct H1 as [ ctx [H4 H5]].
   rewrite fst_replace_isnzvars in H4.
   rewrite replace_inzvars_id in H4.
   rewrite snd_replace_isnzvars in H5.
   exists ctx...
  destruct H4 as [ctx [H4 H5]].
  spec H0 ctx. destruct H0.
  rewrite fst_replace_isnzvars.
  rewrite replace_inzvars_id...
  elimtype False. apply H5.
  rewrite snd_replace_isnzvars in H0.
  exists x...
  intros y H1 ctx.
  destruct (H0 y H1) as [x [H2 H3]].
  repeat intro.
  rewrite fst_replace_isnzvars in H4.
  rewrite snd_replace_isnzvars.
  assert (ctx |= replace_inzvars (fst is) (x::nil)).
   rewrite replace_inzvars_nil_eval.
   rewrite replace_inzvars_nil_eval in H4.
   destruct H4 as [ctx' [H4 H5]].
   exists ctx'. split...
   rewrite replace_inzvars_id in H5.
   rewrite list_eval_rewrite in H5.
   rewrite replace_inzvars_correct.
   spec H5 x H2. rewrite replace_inzvars_exvars.
   split... simpl...
  spec H3 ctx. destruct H3.
  rewrite fst_replace_isnzvars...
  rewrite snd_replace_isnzvars in H3...
  exists x0...
 Qed.

 Lemma rLR_ctx_eval_ses: forall ses ctx n l,
  sat_nzvars ses = nil ->
  |ses| < n ->
  le (cheight ctx l) n ->
  sublist (vars ses) l ->
  ctx |= ses ->
  (rL_ctx ctx n l |= ses /\ rR_ctx ctx n l |= ses).
 Proof with try tauto.
  intros.
  remember (rL_ctx ctx n l) as ctxL.
  remember (rR_ctx ctx n l) as ctxR.
  icase n. omega.
  symmetry in HeqctxL,HeqctxR.
  generalize (round_avg_ctx _ _ _ _ _ H1 HeqctxL HeqctxR);intro.
  assert (ses = replace_snzvars ses nil).
   rewrite <-H. rewrite replace_snzvars_id...
  rewrite H5. rewrite H5 in H2,H3,H0.
  rewrite<-H4 in H3.
  rewrite cheight_leq_rewrite in H1.
  apply IMPL_avg_ctx_ses with (l:=l)(n:=S n)...
  rewrite<-HeqctxL. rewrite cheight_lt_rewrite. intros.
  apply rL_ctx_lt... apply H1...
  rewrite<-HeqctxR. rewrite cheight_lt_rewrite. intros.
  apply rR_ctx_lt... apply H1...
 Qed.

End IMPL_Base.