Require Import msl.msl_standard.
Require Import share_dec_base.
Require Import base_properties.
Require Import share_equation_system.
Require Import share_dec_interface.
Require Import NPeano.
Require Import share_correctness_base.

Module SAT_Correctness (sv : SV)
                       (Import es : EQUATION_SYSTEM sv with Module dom := Share_Domain)
                       (Import esf : SYSTEM_FEATURES sv es) : SAT_CORRECTNESS sv es esf.

 Module SB := SAT_Base sv es esf.
 Import SB.

 Lemma SAT_nzvars_separate: forall ses,
  nSAT ses ->
  (SAT ses <-> forall x, In x (sat_nzvars ses) -> sSAT ses x).
 Proof with try tauto.
  intros.
  split;intros.
  destruct H0 as [ctx H0].
  rewrite replace_snzvars_nil_eval in H0.
  exists ctx.
  rewrite replace_snzvars_nil_eval.
  destruct H0.
  rewrite replace_snzvars_reduce.
  split...
  rewrite replace_snzvars_correct.
  rewrite list_eval_rewrite in H2.
  simpl. split... apply H2...
  remember (sat_nzvars ses) as l.
  assert (replace_snzvars ses l = ses). 
   rewrite replace_snzvars_id... symmetry...
  rewrite <- H1.
  icase l...
  apply SAT_nzvars_correct1...
  intro. inv H2.
 Qed.

 Lemma SAT_nSAT: forall (ses : sat_equation_system),
  SAT ses -> nSAT ses.
 Proof.
  intros.
  destruct H as [ctx H].
  exists ctx.
  rewrite replace_snzvars_nil_eval in H.
  destruct H. apply H.
 Qed.

End SAT_Correctness.

Module IMPL_Correctness (sv : SV)
                        (Import es : EQUATION_SYSTEM sv with Module dom := Share_Domain)
                        (Import esf : SYSTEM_FEATURES sv es) : IMPL_CORRECTNESS sv es esf.

 Module SB := SAT_Base sv es esf.
 Import SB.
 Module IB := IMPL_Base sv es esf.
 Import IB.
 Module RA := Round_Average sv es esf.
 Import RA.

 Definition sIMPL_Cond (is : impl_system): Prop :=
  forall y, In y (impl_nzvars (snd is)) ->
  exists x, In x (impl_nzvars (fst is)) /\ sIMPL is x y.
 Definition zIMPL_Cond (is : impl_system) : Prop :=
  forall y, In y (impl_nzvars (snd is)) -> zIMPL is y.

 Lemma IMPL_trivial: forall is,
  ~SAT (ies2ses (fst is)) ->
  IMPL is.
 Proof.
  intros.
  intros rho H1.
  elimtype False. apply H.
  destruct H1 as [rho' H1].
  exists ([impl_exvars (fst is) => rho']rho ).
  trivial.
 Qed.

 Lemma zIMPL_sIMPL: forall is x y,
  zIMPL is y -> sIMPL is x y.
 Proof.
  intros is x y H rho.
  spec H rho.
  rewrite replace_isnzvars_eval in *.
  intro H1.
  apply H.
  destruct H1 as [rho' H1].
  exists rho'.
  rewrite replace_inzvars_ies2ses in *.
  rewrite replace_snzvars_nil_eval in H1. tauto.
 Qed.

 Lemma IMPL_nIMPL: forall is,
  SAT (ies2ses (fst is)) ->
  IMPL is ->
  nIMPL is.
 Proof with try tauto.
  intros is H1 H2 ctx H3.
  rewrite fst_replace_isnzvars in *.
  rewrite snd_replace_isnzvars in *.
  destruct H1 as [ctx' H1].
  destruct H3 as [ctx'' H3].
  rewrite replace_inzvars_ies2ses in H3.
  rewrite replace_snzvars_nil_eval in H1.
  destruct H1 as [H4 H5].
  remember ([impl_exvars (replace_inzvars (fst is) nil) => ctx'']ctx) as rho.
  assert (exists n, max (|is|) (max (cheight ctx' (vars is)) (max (cheight ctx (vars is)) (cheight ctx'' (vars is)))) < n) by apply exist_lt.
  destruct H as [n H].
  repeat rewrite Nat.max_lub_lt_iff in H.
  destruct H as [H6 [H7 [H8 H9]]].
  assert (H10:sublist (vars (replace_snzvars (ies2ses (fst is)) nil)) (vars is)).
   clear. destruct is as [ies1 ies2]. simpl.
   repeat intro. rewrite in_app_iff. left.
   destruct ies1 as [l1 l2 l3 l4]. simpl in *.
   repeat rewrite in_app_iff in *...
  assert (H11:|replace_snzvars (ies2ses (fst is)) nil | < n).
   clear -H6. destruct is as [ies1 ies2]. simpl in *.
   unfold is_h,ses_h in *;simpl in *.
   rewrite Nat.max_lub_lt_iff in H6...
  assert (H12:cheight rho (vars is) < n). 
   icase n. omega.
   rewrite cheight_lt_rewrite. intros.
   rewrite Heqrho.
   rewrite replace_inzvars_exvars.
   destruct (in_dec eq_dec v (impl_exvars (fst is))).
   rewrite override_in...
   rewrite cheight_lt_rewrite in H9. apply H9...
   rewrite override_not_in...
   rewrite cheight_lt_rewrite in H8. apply H8...
  generalize (SAT_avg_eval _ _ _ _ _ H10 H11 H7 H12 H4 H3);intro H13.
  spec H2 (avg_ctx ctx' ctx n (vars is)).
  assert (avg_ctx ctx' ctx n (vars is) |= (fst is)).
   exists (avg_ctx ctx' ctx'' n (vars is)).
   rewrite <- avg_override.
   rewrite replace_inzvars_exvars in Heqrho.
   rewrite <-Heqrho.
   rewrite context_override_idem.
   rewrite replace_snzvars_nil_eval.
   split...
   assert (rho |= @nil var). simpl...
   assert (sublist (sat_nzvars (ies2ses (fst is))) (vars is)).
    clear. destruct is as [ies1 ies2];simpl;repeat intro.
    rewrite in_app_iff. left.
    destruct ies1 as [l1 l2 l3 l4];simpl in *.
    repeat rewrite in_app_iff...
   assert (sublist nil (vars is)).
    repeat intro. inv H1.
   generalize (IMPL_avg_ctx_list_var _ _ _ _ _ _ H5 H H0 H1 H7 H12);intro.
   rewrite app_nil_r in H14...
  spec H2 H.
  destruct H2 as [rho' H2].
  rewrite replace_snzvars_nil_eval in H2.
  destruct H2 as [H2 _].
  apply override_eval_height_2 with (l':= vars is) in H2...
  destruct H2 as [rho'' [H14 H15]].
  assert (H16:le (cheight (avg_ctx ctx' ctx n (vars is)) (vars is)) n).
   icase n. omega.
   rewrite cheight_leq_rewrite. intros.
   apply avg_ctx_leq...
   rewrite cheight_lt_rewrite in H7. apply H7...
   rewrite cheight_lt_rewrite in H8. apply H8...
  assert (le (cheight rho'' (vars is)) n).
   eapply le_trans.
   apply H14.
   rewrite Nat.max_lub_iff.
   split.
   rewrite cheight_leq_rewrite.
   intros.
   rewrite cheight_leq_rewrite in H16. apply H16.
   rewrite in_app_iff in H0. destruct H0...
   clear - H0. destruct is as [ies1 ies2]. simpl in *.
   rewrite in_app_iff. right.
   destruct ies2 as [l1 l2 l3 l4]. simpl in *.
   repeat rewrite in_app_iff in *...
   clear - H6. destruct is as [ies1 ies2].
   simpl in *. unfold is_h,ses_h in *;simpl in *.
   rewrite Nat.max_lub_lt_iff in H6.
   destruct H6 as [_ H6].
   destruct ies2 as [l1 l2 l3 l4];unfold ies_h in *;simpl in *.
   omega.
  apply rLR_ctx_eval_ses with (n:=n) (l:=vars is)in H15...
  destruct H15 as [_ H15].
  rewrite rR_ctx_override in H15.
  exists (rR_ctx rho'' n (vars is)).
  rewrite replace_inzvars_ies2ses.
  eapply eval_equiv. Focus 2. apply H15.
  repeat intro. rewrite replace_inzvars_exvars.
  destruct (in_dec eq_dec v (impl_exvars (snd is))).
  repeat rewrite override_in...
  repeat rewrite override_not_in...
  assert (In v (vars is)).
   clear - H1. destruct is as [ies1 ies2];simpl in *.
   rewrite in_app_iff. right.
   destruct ies2 as [l1 l2 l3 l4];simpl in *.
   repeat rewrite in_app_iff in *...
  symmetry. icase n. omega. apply rLR_avg_ctx. 
  rewrite cheight_lt_rewrite in H7. apply H7...
  rewrite cheight_lt_rewrite in H8. apply H8...
  clear - H6. destruct is as [ies1 ies2].
  simpl in *. unfold is_h,ses_h in *;simpl in *.
  rewrite Nat.max_lub_lt_iff in H6.
  destruct H6 as [_ H6]...
  rewrite cheight_leq_rewrite. intros.
  destruct (in_dec eq_dec v (impl_exvars (snd is))).
  rewrite override_in...
  rewrite cheight_leq_rewrite in H0.
  apply H0...
  rewrite override_not_in...
  rewrite cheight_leq_rewrite in H16.
  apply H16...
  clear. repeat intro.
  destruct is as [ies1 ies2]. simpl in *.
  rewrite in_app_iff. right.
  destruct ies2 as [l1 l2 l3 l4];simpl in *.
  repeat rewrite in_app_iff in *...
  clear. destruct is as [ies1 ies2].
  simpl. repeat intro.
  rewrite in_app_iff. right.
  destruct ies2 as [l1 l2 l3 l4]. simpl in *.
  rewrite in_app_iff...
 Qed.

 Lemma IMPL_case1: forall is,
  impl_nzvars (fst is) <> nil ->
  impl_nzvars (snd is) <> nil ->
  (IMPL is <-> sIMPL_Cond is).
 Proof with try tauto.
  intros.
  rewrite IMPL_F_equiv...
  rewrite F_sIMPL_Cond_equiv...
 Qed.

 Lemma IMPL_case2: forall is,
  impl_nzvars (snd is) <> nil ->
  impl_nzvars (fst is) = nil ->
  (IMPL is <-> zIMPL_Cond is).
 Proof with try tauto.
  intros.
  split;intro.
  intros y H2 ctx H3.
  spec H1 ctx.
  rewrite fst_replace_isnzvars,snd_replace_isnzvars in *.
  rewrite <- H0 in H3. rewrite replace_inzvars_id in H3.
  apply H1 in H3.
  destruct H3 as [ctx' H3].
  rewrite replace_snzvars_nil_eval in H3.
  exists ctx'.
  rewrite replace_inzvars_ies2ses,replace_inzvars_exvars.
  rewrite replace_snzvars_nil_eval.
  rewrite replace_snzvars_correct.
  rewrite replace_snzvars_reduce.
  split...
  split. simpl...
  destruct H3.
  rewrite list_eval_rewrite in H4. apply H4.
  apply H2.
  
  (*Second goal*)
  remember (impl_nzvars (snd is)) as l.
  revert H0 H1 Heql. revert is.
  induction l... intros.
  assert (IMPL (replace_isnzvars is nil (a::nil))).
   apply H1.
   rewrite<-Heql. left...
  intros ctx H3.
  destruct H3 as [ctx' H3].
  spec H2 ctx.
  rewrite replace_isnzvars_eval in H2.
  assert (ctx |= replace_inzvars (fst is) nil).
   exists ctx'.
   rewrite replace_inzvars_ies2ses.
   rewrite replace_inzvars_exvars.
   rewrite<-H0...
  apply H2 in H4.
  destruct (list_eq_dec eq_dec l nil). subst.
  rewrite Heql in H4. rewrite replace_inzvars_id in H4...
  spec IHl n (replace_isnzvars is nil l). clear H2.
  repeat detach IHl.
  spec IHl ctx. rewrite replace_isnzvars_eval in IHl.
  detach IHl.
  destruct IHl as [rho IHl].
  destruct H4 as [rho' H4].
  rewrite replace_inzvars_exvars,replace_inzvars_ies2ses in *.
  assert (exists m, max (max(cheight ([impl_exvars (snd is) => rho']ctx) (vars (snd is)))
  (cheight ([impl_exvars (snd is) => rho]ctx) (vars (snd is)))) (|(snd is)|) < m) by apply exist_lt.
  destruct H2 as [m H2].
  repeat rewrite Nat.max_lub_lt_iff in H2.
  destruct H2 as [[? ?] ?].
  exists (avg_ctx rho' rho m (impl_exvars (snd is))).
  rewrite replace_snzvars_nil_eval.
  rewrite replace_snzvars_nil_eval in H4,IHl.
  rewrite replace_snzvars_reduce in H4,IHl.
  rewrite replace_snzvars_correct in H4,IHl.
  assert (sat_nzvars (ies2ses (snd is)) = impl_nzvars (snd is)) by tauto.
  rewrite<- Heql in H7. rewrite H7. clear H7.
  destruct H4. destruct IHl.
  assert (sublist (vars (replace_snzvars (ies2ses (snd is)) nil)) (vars (snd is))).
   repeat intro.
   destruct (snd is) as [l1 l2 l3 l4].
   simpl in *. repeat rewrite in_app_iff in *...
  assert (|replace_snzvars (ies2ses (snd is)) nil| < m) by tauto.
  generalize (SAT_avg_eval _ _ _ _ _ H10 H11 H2 H5 H4 H8);intro.
  rewrite avg_override in H12.
  split.
  eapply eval_equiv. Focus 2. apply H12.
  repeat intro. destruct (in_dec eq_dec v (impl_exvars (snd is))).
  repeat rewrite override_in...
  assert (In v (vars (snd is))).
  destruct (snd is) as [l1 l2 l3 l4]. simpl in *.
  repeat rewrite in_app_iff...
  unfold avg_ctx. destruct (in_dec eq_dec v (impl_exvars (snd is)))...
  destruct (in_dec eq_dec v (vars (snd is)))...
  repeat rewrite override_not_in...
  symmetry. rewrite avg_ctx_iden...
  destruct (snd is) as [l1 l2 l3 l4]. simpl in *.
  repeat rewrite in_app_iff in *...  
  icase m. omega.
  rewrite cheight_lt_rewrite in H2.
  spec H2 v. detach H2.
  rewrite override_not_in in H2...
  destruct (snd is) as [l1 l2 l3 l4]. simpl in *.
  repeat rewrite in_app_iff in *...
  assert (sublist (a::nil) (vars (snd is)) /\ sublist l (vars (snd is))).
   clear-Heql. destruct (snd is) as [l1 l2 l3 l4].
   simpl in *;rewrite <-Heql;simpl.
   split;repeat intro;repeat rewrite in_app_iff.
   destruct H... subst. right. left...
   simpl. repeat rewrite in_app_iff...
  destruct H13.
  generalize (IMPL_avg_ctx_list_var _ _ _ _ _ _ H7 H9 H13 H14 H2 H5);intro.
  rewrite avg_override in H15.
  eapply eval_equiv. Focus 2. apply H15.
  repeat intro.
  destruct (in_dec eq_dec v (impl_exvars (snd is))).
  repeat rewrite override_in...
  assert (In v (vars (snd is))).
  rewrite Heql in H16. clear -H16.
  destruct (snd is) as [l1 l2 l3 l4]. simpl in *.
  repeat rewrite in_app_iff. right. left.
  rewrite<- vars_var_list...
  unfold avg_ctx. destruct (in_dec eq_dec v (impl_exvars (snd is)))...
  destruct (in_dec eq_dec v (vars (snd is)))...
  repeat rewrite override_not_in...
  symmetry. apply avg_ctx_iden...
  rewrite Heql in H16. clear -H16.
  destruct (snd is) as [l1 l2 l3 l4]. simpl in *.
  repeat rewrite in_app_iff. right. left.
  rewrite<- vars_var_list...
  icase m. omega.
  rewrite cheight_lt_rewrite in H2.
  spec H2 v. detach H2. rewrite override_not_in in H2...
  rewrite Heql in H16. clear -H16.
  destruct (snd is) as [l1 l2 l3 l4]. simpl in *.
  repeat rewrite in_app_iff. right. left.
  rewrite<- vars_var_list...
  exists ctx'.
  rewrite replace_inzvars_exvars,replace_inzvars_ies2ses in *.
  rewrite <-H0.
  rewrite ies2ses_nzvars.
  rewrite replace_snzvars_id...
  rewrite snd_replace_isnzvars. rewrite replace_inzvars_correct...
  intros y H5 rho H6.
  repeat rewrite fst_replace_isnzvars,snd_replace_isnzvars in *.
  rewrite replace_inzvars_reduce in *.
  rewrite replace_inzvars_correct in *.
  spec H1 y . detach H1.
  spec H1 rho. rewrite replace_isnzvars_eval in H1.
  apply H1... rewrite <-Heql. right...
  rewrite fst_replace_isnzvars,replace_inzvars_correct...
 Qed.

 Lemma IMPL_case3: forall is,
  impl_nzvars (snd is) = nil ->
  SAT (ies2ses (fst is)) ->
  (IMPL is <-> nIMPL is).
 Proof with try tauto.
  intros.
  split;intros.
  apply IMPL_nIMPL...
  intros ctx H2.
  spec H1 ctx.
  rewrite<-replace_inzvars_id.
  rewrite H.
  erewrite<- snd_replace_isnzvars.
  apply H1. rewrite fst_replace_isnzvars.
  destruct H2 as [ctx' H2].
  exists ctx'.
  rewrite replace_snzvars_nil_eval in H2...
 Qed.

End IMPL_Correctness.
