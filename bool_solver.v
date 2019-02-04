Require Import msl.msl_standard.
Require Import share_dec_base.
Require Import share_equation_system.
Require Import base_properties.
Require Import share_dec_interface.
Require Import fbool_solver.
Require Import bool_to_formula.
Require Import share_simplifier.

Module Bool_solver (sv : SV) (Import bf : BOOL_FORMULA sv)
                   (Import es : EQUATION_SYSTEM sv with Module dom := Bool_Domain)
                   (Import simplifier : SIMPLIFIER sv Bool_Domain es Bool_Simpl_Spec)
                   (Import interpreter : INTERPRETER sv es bf)
                   (Import bsf : BF_SOLVER sv bf)
                   <: BOOL_SOLVER sv bf es.
 
 Module sys_features := System_Features sv es.
 Import sys_features.

 Lemma ses_int_bounded: forall (ses : sat_equation_system),
  full_quan (exF_quan (vars ses) (interpret ses)).
 Proof with try tauto.
  repeat intro.
  simpl. apply exF_quan_In.
  rewrite exF_quan_vars in H.
  rewrite in_app_iff in H.
  destruct H...
  generalize (vars_int ses);intro.
  apply H0...
 Qed.

 Definition fvars_is := fun (is : impl_system) =>
  let f1 := interpret (fst is) in
  let f2 := interpret (snd is) in
  filter (fun v => if in_dec eq_dec v (impl_exvars (fst is)) then false else true) (vars f1) ++ 
  filter (fun v => if in_dec eq_dec v (impl_exvars (snd is)) then false else true) (vars f2).

 Require Import Classical.

 Lemma fvar_is_In: forall v is,
  In v (fvars_is is) <-> (In v (vars (interpret (fst is))) /\ ~not_free v (interpret (fst is))) \/
                         (In v (vars (interpret (snd is))) /\ ~not_free v (interpret (snd is))).
 Proof with try tauto.
  intros.
  unfold fvars_is. rewrite in_app_iff.
  repeat rewrite filter_In.
  split;intros.

  - destruct H as [[H1 H2]|[H1 H2]].
    left. split...
    destruct (in_dec eq_dec v (impl_exvars (fst is)));inv H2.
    rewrite<- not_free_ies...
    right;split...
    destruct (in_dec eq_dec v (impl_exvars (snd is)));inv H2.
    rewrite<- not_free_ies...

  - destruct H as [[H1 H2]|[H1 H2]].
    left. split...
    destruct (in_dec eq_dec v (impl_exvars (fst is)))...
    rewrite<- not_free_ies in H2...
    right;split...
    destruct (in_dec eq_dec v (impl_exvars (snd is)))...
    rewrite<- not_free_ies in H2...
 Qed.

 Lemma is_int_bounded: forall (is : impl_system),
  full_quan ((allF_quan (fvars_is is)) (interpret is)).
 Proof with try tauto.
  repeat intro.
  simpl.
  rewrite allF_quan_In_iff.
  rewrite allF_quan_vars in H.
  destruct (in_dec eq_dec v (fvars_is is))...
  rewrite in_app_iff in H.
  destruct H...
  right.
  rewrite fvar_is_In in n.
  assert (forall P Q, ~ (P \/ Q) <-> ~P /\ ~Q) by (intros;tauto).
  rewrite H0 in n.
  assert (forall P Q, ~(P /\ Q) <-> ~P \/ ~Q) by (intros;tauto).
  repeat rewrite H1 in n.
  assert (forall P, ~~P <-> P) by (intros;tauto).
  repeat rewrite H2 in n. clear H0 H1 H2.
  destruct n.
  destruct is as [ies1 ies2].
  simpl in *. rewrite in_app_iff in H.
  destruct (in_dec eq_dec v (vars (interpret  ies1))).
  assert (not_free v (interpret  ies1)) by tauto.
  split...
  destruct (in_dec eq_dec v (vars (interpret  ies2)))...
  apply not_free_trivial...
  split... apply not_free_trivial...
 Qed.

 Lemma SAT_ses_int_correct: forall (ses : sat_equation_system),
  SAT ses <-> valid (exF_quan (vars ses) (interpret ses)).
 Proof with try tauto.
  intros.
  split;intros.
  destruct H as [rho H].
  generalize (context_override_idem rho (vars ses));intro.
  rewrite <- H0 in H;clear H0.
  apply beval_int in H.
  assert (beval rho (exF_quan (vars ses) (interpret ses)) = true).
   apply exF_quan_beval.
   exists rho...
  generalize (ses_int_bounded ses);intro.
  apply full_quan_case in H1.
  destruct H1... spec H1 rho.
  elimtype False. apply H1...
  
  spec H (fun (v:var) => false).
  simpl in H.
  rewrite exF_quan_beval in H.
  destruct H as [rho H].
  exists ([vars ses => rho](fun _ => false)).
  simpl.
  generalize (beval_int ses ([vars ses => rho](fun _ => false)));intro.
  apply H0...
 Qed.

 Definition nzvar2eql (v : var): equality := (Vobject v, Cobject true).

 Lemma nzvar2eql_correct: forall rho v,
  rho |= v <-> rho |= nzvar2eql v.
 Proof.
  intros. simpl. icase (rho v);compute;firstorder.
 Qed.

 Definition nzvar2eql_list:= fun l =>
  map nzvar2eql l.

 Lemma nzvar2eql_list_correct: forall rho l,
  rho |= l <-> rho |= nzvar2eql_list l.
 Proof with try tauto.
  induction l;intros;simpl...
  assert (rho a <> false <-> rho a = true).
   icase (rho a);firstorder.
  simpl in IHl;rewrite IHl...
 Qed.

 Definition ses_reduce := fun (ses : sat_equation_system) =>
  Sat_equation_system nil ( nzvar2eql_list (sat_nzvars ses)++(sat_equalities ses)) (sat_equations ses).

 Lemma ses_reduce_correct: forall rho ses,
  rho |= ses <-> rho |= (ses_reduce ses).
 Proof with try tauto.
  intros. destruct ses as [l1 l2 l3];simpl.
  unfold eval_sat_equation_system;simpl.
  change (eval_list rho (nzvar2eql_list l1 ++ l2)) with (rho |= (nzvar2eql_list l1 ++l2)).
  rewrite eval_list_app.
  rewrite<- nzvar2eql_list_correct...
 Qed.

 Definition SAT_preprocess:= fun (ses : sat_equation_system) => 
  SATsimplifier (ses_reduce ses).

 Lemma SAT_preprocess_Some: forall ses ses',
  SAT_preprocess ses = Some ses' ->
  forall rho, rho |= ses <-> rho |= ses'.
 Proof with try tauto.
  intros.
  unfold SAT_preprocess in *.
  apply SATsimplifier_Some with (rho:=rho)in H.
  rewrite<- H. apply ses_reduce_correct.
 Qed.

 Lemma SAT_preprocess_None: forall ses,
  SAT_preprocess ses = None ->
  forall rho, ~rho |= ses.
 Proof with try tauto.
  intros.
  unfold SAT_preprocess in *.
  apply SATsimplifier_None with (rho:=rho) in H.
  rewrite<- ses_reduce_correct in H...
 Qed.

 Definition SATbsolver := fun (ses : sat_equation_system) => 
  match SAT_preprocess ses with
  |None => false
  |Some ses' =>
   match bsolver (exF_quan (vars ses') (interpret ses')) with
   | Some b => b
   | None => false (*never happen*)
   end
  end.

 Lemma SATbsolver_correct: forall (ses : sat_equation_system),
  SAT ses <-> SATbsolver ses = true.
 Proof with try tauto.
  intros.
  unfold SATbsolver.
  case_eq (SAT_preprocess ses). intros ses' Hs.
  assert (Hv : SAT ses <-> SAT ses').
    generalize (SAT_preprocess_Some ses ses' Hs);intro.
    split;intros H1;destruct H1 as [rho H1];spec H rho;exists rho...
  rewrite Hv.
  rewrite SAT_ses_int_correct.
  generalize (ses_int_bounded ses');intro.
  generalize (bsolver_Some _ H);intro.
  destruct H0 as [b H0].
  rewrite H0.
  icase b.
  apply bsolver_valid in H0...
  apply bsolver_unsat in H0...
  split;intros.
  rewrite bF_unsat_rewrite in H0.
  spec H0 (fun (v:var) => false).
  spec H1 (fun (v:var) => false).
  rewrite<-H0,<-H1... inv H1.
  
  intro H. 
  split;intros;disc... destruct H0 as [rho H0].
  apply SAT_preprocess_None with (rho:=rho) in H...
 Qed.

 Lemma IMPL_is_int_correct: forall (is : impl_system),
  IMPL is <->  valid (allF_quan (fvars_is is) (interpret is)).
 Proof with try tauto.
  intros.
  split;intros H rho.
  apply allF_quan_beval;intros.
  spec H ([fvars_is is => rho']rho).
  apply beval_int...

  spec H rho.
  unfold eval,bF_eval in H.
  rewrite allF_quan_beval in H.
  spec H rho. rewrite context_override_idem in H.
  apply beval_int...
 Qed.

 Definition ies_reduce := fun (ies : impl_equation_system) =>
  Impl_equation_system (impl_exvars ies) nil ((nzvar2eql_list (impl_nzvars ies))++(impl_equalities ies)) (impl_equations ies).

 Lemma ies_reduce_correct: forall  rho ies,
  rho |= ies <-> rho |= ies_reduce ies.
 Proof with try tauto.
  intros. destruct ies as [l1 l2 l3 l4];simpl.
  unfold eval_impl_equation_system;simpl.
  split;intros.
  - destruct H as [rho' H].
    exists rho'. simpl in *;unfold eval_sat_equation_system in *;simpl in *.
    change (eval_list ([l1 => rho']rho) (nzvar2eql_list l2 ++ l3)) with (([l1 => rho']rho) |= (nzvar2eql_list l2 ++l3)).
    rewrite eval_list_app.
    rewrite<- nzvar2eql_list_correct...
  - destruct H as [rho' H].
    exists rho'. simpl in *;unfold eval_sat_equation_system in *;simpl in *.
    change (eval_list ([l1 => rho']rho) (nzvar2eql_list l2 ++ l3)) with (([l1 => rho']rho) |= (nzvar2eql_list l2 ++l3)) in H.
    rewrite eval_list_app in H.
    rewrite<- nzvar2eql_list_correct in H...
 Qed.

 Lemma ies_reduce_ses: forall rho ies,
  rho |= ies2ses (ies_reduce ies) <-> rho |= ses_reduce (ies2ses ies).
 Proof with try tauto.
  intros...
 Qed.

 Definition IMPL_preprocess := fun (is : impl_system) =>
  IMPLsimplifier ((ies_reduce (fst is)),(ies_reduce (snd is))).

 Lemma IMPL_preprocess_Same: forall is is',
  IMPL_preprocess is = Same is' ->
  forall rho, (rho |= fst is <-> rho |= fst is') /\ (rho |= is <-> rho |= is') .
 Proof with try tauto.
  intros.
  unfold IMPL_preprocess in *.
  apply IMPLsimplifier_Same with (rho:=rho) in H.
  simpl in *. unfold eval_impl_system in *;simpl in *.
  repeat rewrite <- ies_reduce_correct in H...
 Qed.
 
 Lemma IMPL_preprocess_Absurd: forall is,
  SAT (ies2ses (fst is)) ->
  IMPL_preprocess is = Absurd ->
  ~IMPL is.
 Proof with try tauto.
  intros.
  unfold IMPL_preprocess in *.
  apply IMPLsimplifier_Absurd in H0.
  intro. apply H0.
  intros rho H2. spec H1 rho. unfold fst,snd in *.
  rewrite<- ies_reduce_correct in *.
  apply H1...
  destruct H as [rho H].
  exists rho. 
  unfold fst. apply ies_reduce_ses.
  rewrite <-ses_reduce_correct...
 Qed.

 Lemma IMPL_preprocess_Simpler: forall is,
  IMPL_preprocess is = Simpler tt ->
  forall rho, rho |= is.
 Proof with try tauto.
  intros is H rho H1.
  unfold IMPL_preprocess in *.
  apply IMPLsimplifier_Simpler with (rho:=rho) in H.
  apply ies_reduce_correct. apply H.
  unfold fst.
  rewrite<- ies_reduce_correct...
 Qed.
  
 Definition IMPLbsolver := fun (is : impl_system) => 
  match IMPL_preprocess is with
  |Absurd     => if SATbsolver (ies2ses (fst is)) then false else true
  |Simpler tt => true
  |Same is'   =>
    match bsolver (allF_quan (fvars_is is') (interpret is')) with
    | Some b => b
    | None => false (*never happen*)
    end
  end. 

 Lemma IMPLbsolver_correct: forall (is : impl_system),
  IMPL is <-> IMPLbsolver is = true.
 Proof with try tauto.
  intros.
  unfold IMPLbsolver.
  case_eq (IMPL_preprocess is);intros.
  - case_eq (SATbsolver (ies2ses (fst is)));intros.
    apply SATbsolver_correct in H0.
    apply IMPL_preprocess_Absurd in H...
    split;intros... inv H1.
    split;intros...
    assert (~SAT (ies2ses (fst is))).
     intro. apply SATbsolver_correct in H2.
     rewrite H2 in H0;inv H0.
    intros rho H3. destruct H3 as [rho' H3].
    elimtype False. apply H2.
    exists ([impl_exvars (fst is) => rho']rho)...
  - icase u. 
    split;intros... intros rho H1.
    apply IMPL_preprocess_Simpler with (rho:=rho) in H.
    apply H...
  - assert (IMPL is <-> IMPL i).
     generalize (IMPL_preprocess_Same is i H);intro.
     split;intros H1 rho;spec H0 rho;spec H1 rho...
    rewrite H0. clear H0.
    rewrite IMPL_is_int_correct.
    generalize (is_int_bounded i);intro.
    generalize (bsolver_Some _ H0);intro.
    destruct H1 as [b H1].
    rewrite H1.
    icase b.
    apply bsolver_valid in H1...
    apply bsolver_unsat in H1...
    split;intros.
    rewrite bF_unsat_rewrite in H1.
    spec H1 (fun (v:var) => false).
    spec H2 (fun (v:var) => false).
    rewrite<-H1,<-H2... inv H2.
 Qed.

End Bool_solver.
 