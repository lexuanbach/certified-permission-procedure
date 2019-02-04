Require Import msl.msl_standard.
Require Import share_dec_base.
Require Import share_equation_system.
Require Import base_properties.
Require Import share_dec_interface.
Require Import share_correctness.
Require Import share_decompose.
Require Import share_to_bool.
Require Import fbool_solver.
Require Import bool_solver.
Require Import share_simplifier.
Require Import share_bounder.
Require Import bool_to_formula.

Module Solver (sv : SV)
              (Import es : EQUATION_SYSTEM sv with Module dom := Share_Domain)
              (Import bf : BOOL_FORMULA sv)
              (Import bsf : BF_SOLVER sv bf)
               <: SOLVER sv es.

 Module esf := System_Features sv es.
 Module bes := Equation_system sv Bool_Domain.
 Module besf := System_Features sv bes.
 Module sat_decompose := SAT_Decompose sv es esf.
 Module impl_decompose := IMPL_Decompose sv es esf.
 Module s2b := Share2Bool sv es esf bes besf.
 Module sat_correct := SAT_Correctness sv es esf.
 Module impl_correct := IMPL_Correctness sv es esf.
 Module sh_simplifier := Simplifier sv Share_Domain es Share_Simpl_Spec.
 Module b_simplifier := Simplifier sv Bool_Domain bes Bool_Simpl_Spec.
 Module interpreter := Interpreter sv bes bf.
 Module b_solver := Bool_solver sv bf bes b_simplifier interpreter bsf.
 Module bounder := Bounder sv es.

 Import esf.
 Import sat_decompose.
 Import impl_decompose.
 Import s2b.
 Import sat_correct.
 Import impl_correct.
 Import sh_simplifier.
 Import bounder.
 Import b_solver.

 Fixpoint eval_disjunct {A} (f : A -> bool) (l : list A) :=
  match l with
  |nil  => true
  |a::nil => f a
  |a::l' => if f a then true else eval_disjunct f l'
  end.

 Fixpoint eval_conjunct {A} (f : A -> bool) (l : list A) :=
  match l with
  |nil  => true
  |a::l' => if f a then eval_conjunct f l' else false
  end.

 Definition nSATbsolver := fun (ses : bes.sat_equation_system) => 
  SATbsolver (besf.replace_snzvars ses nil). 
 Definition sSATbsolver := fun v (ses : bes.sat_equation_system) => 
  SATbsolver (besf.replace_snzvars ses (v::nil)).
 Definition nIMPLbsolver := fun (is : bes.impl_system) =>
  IMPLbsolver (besf.replace_isnzvars is nil nil). 
 Definition zIMPLbsolver := fun x (is : bes.impl_system) =>
  IMPLbsolver (besf.replace_isnzvars is nil (x::nil)).
 Definition sIMPLbsolver := fun x y (is : bes.impl_system) =>
  IMPLbsolver (besf.replace_isnzvars is (x::nil) (y::nil)).

 Lemma eval_conjunct_true {A}: forall f (l : list A),
  eval_conjunct f l = true <-> forall a, In a l -> f a = true.
 Proof with try tauto.
  intros. induction l. simpl...
  simpl.
  case_eq (f a);intros.
  rewrite IHl. split;intros. destruct H1;subst...
  apply H0... apply H0...
  split;intros. inv H0. spec H0 a. spec H0...
  rewrite H in H0;inv H0.
 Qed.

 Lemma eval_conjunct_false {A}: forall f (l : list A),
  eval_conjunct f l = false <-> exists a, In a l /\ f a = false.
 Proof with try tauto.
  intros. induction l. simpl.
  split;intros. inv H. destruct H as [? [? ?]]...
  simpl.
  case_eq (f a);intros.
  rewrite IHl. split;intros.
  destruct H0. exists x...
  destruct H0 as [? [? ?]].
  destruct H0;subst. rewrite H1 in H;inv H.
  exists x...
  split;intros...
  exists a...
 Qed.

 Lemma eval_disjunct_true {A}: forall f (l : list A),
  l <> nil ->
  (eval_disjunct f l = true <-> exists a, In a l /\ f a = true).
 Proof with try tauto.
  induction l;intros;
  simpl...
  icase l;simpl.
  split;intros. exists a...
  destruct H0 as [? [? ?]].
  destruct H0;subst...
  case_eq (f a);intros.
  split;intros...
  exists a...
  simpl in IHl.
  spec IHl. intro;disc.
  rewrite IHl. split;intros.
  destruct H1. exists x...
  destruct H1. exists x.
  split...
  destruct H1. destruct H1;subst...
  rewrite H2 in H0;inv H0.
 Qed.

 Lemma eval_disjunct_false {A}: forall f (l : list A),
  l <> nil ->
  (eval_disjunct f l = false <-> forall a, In a l -> f a = false).
 Proof with try tauto.
  induction l;intros;
  simpl...
  icase l;simpl.
  split;intros.
  destruct H1;subst...
  apply H0...
  case_eq (f a);intros.
  split;intros... inv H1.
  spec H1 a. spec H1... rewrite H1 in H0;disc...
  spec IHl. intro;disc.
  rewrite IHl.
  split;intros.
  destruct H2;subst... apply H1;simpl...
  apply H1;simpl in H2...
 Qed.

 Definition SATpreprocess := fun (ses : sat_equation_system) =>
  match SATsimplifier ses with
  |None => None
  |Some ses1 => match SATbounder ses1 with
                |None => None
                |Some ses2 => SATsimplifier ses2
                end
  end.

  Lemma SATpreprocess_None: forall ses,
   SATpreprocess ses = None -> forall rho,~rho |= ses.
  Proof with try tauto.
   intros.
   unfold SATpreprocess in H.
   remember ( SATsimplifier ses).
   symmetry in Heqo. icase o.
   apply SATsimplifier_Some with (rho:=rho) in Heqo.
   remember (SATbounder s0).
   symmetry in Heqo0. icase o.
   apply SATbounder_Some with (rho:=rho) in Heqo0.
   apply SATsimplifier_None with (rho:=rho) in H...
   apply SATbounder_None with (rho:=rho) in Heqo0...
   apply SATsimplifier_None with (rho:=rho) in Heqo...
  Qed.

  Lemma SATpreprocess_Some: forall ses ses',
   SATpreprocess ses = Some ses' -> 
   forall rho, rho |= ses <-> rho |= ses'.
  Proof with try tauto.
   intros.
   unfold SATpreprocess in H.
   remember ( SATsimplifier ses).
   symmetry in Heqo. icase o.
   apply SATsimplifier_Some with (rho:=rho) in Heqo.
   remember (SATbounder s0).
   symmetry in Heqo0. icase o.
   apply SATbounder_Some with (rho:=rho) in Heqo0.
   apply SATsimplifier_Some with (rho:=rho) in H...
  Qed.

 Definition SATsolver := fun (ses : sat_equation_system) =>
  match SATpreprocess ses with
  |None => false
  |Some ses' =>
   let l := map transform (SATdecompose ses') in
   if (eval_conjunct nSATbsolver l) then
    eval_conjunct (fun v => eval_disjunct (sSATbsolver v) l) (sat_nzvars ses')
   else false
  end.

 Lemma SATsolver_case1: forall ses,
  nSAT ses <-> eval_conjunct nSATbsolver (map transform (SATdecompose ses)) = true.
 Proof with try tauto.
  intros.
  rewrite nSAT_decompose_eval.
  rewrite eval_conjunct_true.
  split;intros.
  rewrite in_map_iff in H0.
  destruct H0 as [ses' [H0 H1]].
  spec H ses' H1. rewrite <- H0.
  apply SAT_decompose_height in H1.
  apply nSAT_transform_correct in H...
  unfold nSATbsolver. rewrite<- SATbsolver_correct...

  generalize (SAT_decompose_height _ _ H0);intro.
  apply nSAT_transform_correct...
  unfold besf.nSAT.
  rewrite SATbsolver_correct.
  apply H. apply in_map...
 Qed.

 Lemma SATsolver_case2: forall ses v,
  nSAT ses ->
  (sSAT ses v <-> eval_disjunct (sSATbsolver v) (map transform (SATdecompose ses)) = true).
 Proof with try tauto.
  intros.
  rewrite sSAT_decompose_eval...
  rewrite eval_disjunct_true.
  split;intro H1;destruct H1 as [ses' [H1 H2]].
  exists (transform ses').
  split. apply in_map...
  apply SAT_decompose_height in H1.
  generalize (sSAT_transform_correct _ v H1);intro.
  apply H0 in H2.
  unfold sSATbsolver.
  rewrite<- SATbsolver_correct...

  rewrite in_map_iff in H1.
  destruct H1 as [ses'' [H3 H4]].
  exists ses''. split...
  apply SAT_decompose_height in H4.
  rewrite sSAT_transform_correct...
  rewrite <-H3 in H2.
  unfold besf.sSAT.
  rewrite SATbsolver_correct...

  intro.
  generalize (SAT_decompose_not_nil ses);intro.
  apply H1. apply map_eq_nil in H0...
 Qed.

 Lemma SATsolver_correct : forall ses, SATsolver ses = true <-> SAT ses.
 Proof with try tauto.
  intros.
  unfold SATsolver.
  remember (SATpreprocess ses).
  symmetry in Heqo. destruct o as [ses'|None].
  Focus 2. split;intros;inv H...
  apply SATpreprocess_None with (rho :=x) in Heqo...
  assert (SAT ses <-> SAT ses').
  generalize (SATpreprocess_Some ses ses' Heqo);intro HS.
   split;intro H;destruct H as [rho H];exists rho;apply HS...
  rewrite H. clear.
  remember (eval_conjunct nSATbsolver (map transform (SATdecompose ses'))) as b.
  symmetry in Heqb.
  icase b.
  rewrite<- SATsolver_case1 in Heqb.
  rewrite SAT_nzvars_separate...
  rewrite eval_conjunct_true.
  split;intros H v H0;
  spec H v H0; apply SATsolver_case2 in H...

  assert (~nSAT ses').
   intro. rewrite SATsolver_case1 in H.
   rewrite H in Heqb. inv Heqb.
  split;intros. inv H0.
  elimtype False. apply H.
  apply SAT_nSAT...
 Qed.
              
 Lemma IMPLsolver_case1: forall is,
  SAT (ies2ses (fst is)) ->
  (nIMPL is <-> eval_conjunct nIMPLbsolver (map transform (IMPLdecompose is)) = true).
 Proof with try tauto.
  intros.
  rewrite nIMPL_decompose_eval.
  Focus 2. apply SAT_nSAT...
  rewrite eval_conjunct_true.
  split;intros.
  rewrite in_map_iff in H1.
  destruct H1 as [is' [H1 H2]].
  rewrite <- H1.
  spec H0 is' H2.
  rewrite nIMPL_transform_correct in H0.
  unfold nIMPLbsolver. rewrite<- IMPLbsolver_correct...
  apply IMPL_decompose_height with is...
  rewrite nIMPL_transform_correct.
  apply in_map with (f:=transform) in H1.
  spec H0 (transform is') H1.
  unfold nIMPLbsolver in H0.
  rewrite<- IMPLbsolver_correct in H0...
  apply IMPL_decompose_height with is...
 Qed.

 Lemma IMPLsolver_case2: forall is v,
  SAT (ies2ses (fst is)) ->
  nIMPL is ->
  (zIMPL is v <-> eval_disjunct (zIMPLbsolver v) (map transform (IMPLdecompose is)) = true).
 Proof with try tauto.
  intros.
  rewrite zIMPL_decompose_eval...
  Focus 2. apply SAT_nSAT...
  rewrite eval_disjunct_true.
  Focus 2. intro.
  generalize (IMPL_decompose_not_nil is);intro.
  apply H2. apply map_eq_nil in H1...
  split;intro H2;
  destruct H2 as [is' [H2 H3]].
  exists (transform is').
  split. apply in_map...
  unfold zIMPLbsolver. 
  rewrite<- IMPLbsolver_correct.
  rewrite zIMPL_transform_correct in H3...
  apply IMPL_decompose_height with is...
  rewrite in_map_iff in H2.
  destruct H2 as [is'' [H4 H5]].
  rewrite <- H4 in H3.
  exists is''. split...
  rewrite zIMPL_transform_correct.
  unfold besf.zIMPL.
  rewrite IMPLbsolver_correct...
  apply IMPL_decompose_height with is...
 Qed.

 Lemma IMPLsolver_case3: forall is x y,
  SAT (ies2ses (fst is)) ->
  nIMPL is ->
  ~zIMPL is y ->
  (sIMPL is x y <-> eval_conjunct (sIMPLbsolver x y) (map transform (IMPLdecompose is)) = true).
 Proof with try tauto.
  intros.
  rewrite sIMPL_decompose_eval...
  Focus 2. apply SAT_nSAT...
  rewrite eval_conjunct_true.
  split;intros H2 is' H3.
  rewrite in_map_iff in H3.
  destruct H3 as [is'' [H3 H4]].
  rewrite <-H3.
  spec H2 is'' H4.
  unfold sIMPLbsolver.
  rewrite<- IMPLbsolver_correct.
  rewrite sIMPL_transform_correct in H2...
  apply IMPL_decompose_height with is...
  rewrite nIMPL_decompose_eval in H0...
  apply H0... apply SAT_nSAT...
  rewrite sIMPL_transform_correct.
  unfold besf.sIMPL. rewrite IMPLbsolver_correct.
  apply H2... apply in_map...
  apply IMPL_decompose_height with is...
  rewrite nIMPL_decompose_eval in H0...
  apply H0...
  apply SAT_nSAT...
 Qed.

 Definition IMPLpreprocess := fun (is : impl_system) =>
  match IMPLsimplifier is with
  |Absurd => Absurd
  |Simpler tt => Simpler tt
  |Same is1 => match IMPLbounder is1 with
               |Absurd => Absurd
               |Simpler tt => Simpler tt
               |Same is2 => IMPLsimplifier is2
               end
  end.

  Lemma IMPLpreprocess_Absurd: forall is,
   SAT (ies2ses (fst is)) ->
   IMPLpreprocess is = Absurd -> ~IMPL is.
  Proof with try tauto.
   intros.
   unfold IMPLpreprocess in H0.
   remember (IMPLsimplifier is).
   symmetry in Heqr. icase r.
   apply IMPLsimplifier_Absurd in Heqr... icase u.
   assert (SAT (ies2ses (fst i))).
     destruct H as [rho H].
     apply IMPLsimplifier_Same with (rho:=rho)in Heqr.
     destruct Heqr as [[? _] _].
     spec H1. exists rho. rewrite context_override_idem...
     destruct H1 as [rho' H1]. 
     exists ([impl_exvars (fst i) => rho']rho)...
   remember (IMPLbounder i).
   symmetry in Heqr0. icase r.
   apply IMPLbounder_Absurd in Heqr0...
   intro. apply Heqr0. intro rho.
   spec H2 rho.
   apply IMPLsimplifier_Same with (rho:=rho)in Heqr...
   simpl in *;unfold eval_impl_system in *;simpl in *...
   icase u.
   assert (SAT (ies2ses (fst i0))).
     destruct H1 as [rho H1].
     apply IMPLbounder_Same with (rho:=rho)in Heqr0.
     destruct Heqr0 as [[? _] _].
     spec H2. exists rho. rewrite context_override_idem...
     destruct H2 as [rho' H2]. 
     exists ([impl_exvars (fst i0) => rho']rho)...
   apply IMPLsimplifier_Absurd in H0...
   intro. apply H0. intro rho. spec H3 rho.
   apply IMPLbounder_Same with (rho:=rho) in Heqr0.
   apply IMPLsimplifier_Same with (rho:=rho) in Heqr.
   simpl in *;unfold eval_impl_system in *;simpl in *...
  Qed.

  Lemma IMPLpreprocess_Simpler: forall is,
   IMPLpreprocess is = Simpler tt -> forall rho, rho|= is.
  Proof with try tauto.
   intros.
   unfold IMPLpreprocess in H.
   remember (IMPLsimplifier is).
   symmetry in Heqr. icase r. icase u.
   apply IMPLsimplifier_Simpler with (rho:=rho) in Heqr...  
   apply IMPLsimplifier_Same with (rho:=rho)in Heqr. 
   remember (IMPLbounder i).
   symmetry in Heqr0. icase r. icase u.
   apply IMPLbounder_Simpler with (rho:=rho) in Heqr0.
   simpl in *;unfold eval_impl_system in *;simpl in *...
   apply IMPLbounder_Same with (rho:=rho) in Heqr0.
   apply IMPLsimplifier_Simpler with (rho:=rho) in H.
   simpl in *;unfold eval_impl_system in *;simpl in *...   
  Qed.

  Lemma IMPLpreprocess_Same: forall is is',
   IMPLpreprocess is = Same is' ->
   forall rho, (rho |= fst is <-> rho |= fst is')/\
   (rho |= is <-> rho |= is').
  Proof with try tauto.
   intros.
   unfold IMPLpreprocess in H.
   remember (IMPLsimplifier is).
   symmetry in Heqr. icase r. icase u. 
   apply IMPLsimplifier_Same with (rho:=rho)in Heqr. 
   remember (IMPLbounder i).
   symmetry in Heqr0. icase r. icase u.
   apply IMPLbounder_Same with (rho:=rho) in Heqr0.
   apply IMPLsimplifier_Same with (rho:=rho)in H. 
   simpl in *;unfold eval_impl_system in *;simpl in *...   
  Qed.

  Fixpoint subroutine (l1 l2 : list var) (l : list bes.impl_system) : bool :=
  match l2 with
  | nil => true
  | v::l2' => if eval_disjunct (zIMPLbsolver v) l then subroutine l1 l2' l
              else (eval_disjunct (fun v' => eval_conjunct (sIMPLbsolver v' v) l) l1)&&(subroutine l1 l2' l)
  end.

 Lemma subroutine_rewrite: forall l1 l2 l,
  subroutine l1 l2 l = true <-> 
  forall v, In v l2 -> eval_disjunct (zIMPLbsolver v) l = true \/
                       eval_disjunct (fun v' => eval_conjunct (sIMPLbsolver v' v) l) l1 = true.
 Proof with try tauto.
  induction l2;simpl;split;intros...
  destruct H0. subst.
  simpl in H.
  destruct (eval_disjunct (zIMPLbsolver v) l)...
  rewrite andb_true_iff in H...
  apply IHl2...
  destruct (eval_disjunct (zIMPLbsolver a) l)...
  rewrite andb_true_iff in H...
  remember (eval_disjunct (zIMPLbsolver a) l) as b.
  symmetry in Heqb. destruct b.
  apply IHl2... intros. apply H...
  rewrite andb_true_iff.
  split. spec H a. detach H...
  destruct H... rewrite H in Heqb. inv Heqb.
  apply IHl2... intros.
  apply H...
 Qed. 

 Lemma subroutine_correct: forall is l1 l2 l,
  l = map transform (IMPLdecompose is) ->
  l1 = impl_nzvars (fst is) ->
  l2 = impl_nzvars (snd is) ->
  l1 <> nil -> l2 <> nil ->
  SAT (ies2ses (fst is)) -> nIMPL is ->
  (subroutine l1 l2 l = true <-> IMPL is).
 Proof with try tauto.
  intros.
  rewrite subroutine_rewrite.
  rewrite IMPL_case1;try congruence...
  subst.
  split;intros H6 v H7...
  spec H6 v H7.
  remember (eval_disjunct (zIMPLbsolver v) (map transform (IMPLdecompose is))) as b.
  symmetry in Heqb. destruct b.
  rewrite<- IMPLsolver_case2 in Heqb...
  assert (exists x, In x (impl_nzvars (fst is))).
   destruct (impl_nzvars (fst is))...
   exists v0. left...
  destruct H as [v' H].
  exists v'. split... apply zIMPL_sIMPL...
  destruct H6. inv H.
  assert (~zIMPL is v).
   intro. rewrite IMPLsolver_case2 in H0...
   rewrite H0 in Heqb. inv Heqb.
  rewrite eval_disjunct_true in H...
  destruct H as [v' [H8 H9]].
  exists v'. split...
  rewrite<- IMPLsolver_case3 in H9...

  remember (eval_disjunct (zIMPLbsolver v) (map transform (IMPLdecompose is))) as b.
  symmetry in Heqb.
  destruct b. left...
  assert (~zIMPL is v).
   intro. rewrite IMPLsolver_case2 in H...
   rewrite H in Heqb. inv Heqb.
  right.
  spec H6 v H7.
  destruct H6 as [v' [H8 H9]].
  rewrite eval_disjunct_true...
  exists v'. split...
  rewrite<- IMPLsolver_case3...
 Qed.
 
 Definition IMPLsolver := fun (is : impl_system) =>
  match IMPLpreprocess is with
  |Simpler tt => true
  |Absurd => if SATsolver (ies2ses (fst is)) then false else true
  |Same is' =>
  let (ies1,ies2) := is' in
  match SATsolver (ies2ses ies1) with
  |false => true
  |true  => 
    let l       := map transform (IMPLdecompose is') in
    let (l1,l2) := (impl_nzvars ies1, impl_nzvars ies2) in
    match eval_conjunct nIMPLbsolver l with
    |false => false
    |true  => 
      match list_eq_dec sv.t_eq_dec l2 nil with
      |left _    => true
      |right _   => 
          match list_eq_dec sv.t_eq_dec l1 nil with
          |left _    => eval_conjunct (fun v => eval_disjunct (zIMPLbsolver v) l) l2
          |right _   => subroutine l1 l2 l
          end
       end
      end
  end
  end.

 Lemma IMPLsolver_correct : forall is, IMPLsolver is = true <-> IMPL is.
 Proof with try tauto.
  intros.
  unfold IMPLsolver.
  case_eq (IMPLpreprocess is);intro.
  case_eq (SATsolver (ies2ses (fst is)));intro.
  apply SATsolver_correct in H0.
  split;intros;disc.
  apply IMPLpreprocess_Absurd in H... 
  split;intro... apply IMPL_trivial.
  intro. apply SATsolver_correct in H2.
  rewrite H2 in H0;disc.
  intro. icase u.
  split;intro... intro rho.
  apply IMPLpreprocess_Simpler...

  intro. assert (IMPL is <-> IMPL i).
  generalize (IMPLpreprocess_Same is i H) ;intro.
  split;intros H1 rho;spec H1 rho;spec H0 rho;
  simpl in *;unfold eval_impl_system in *;simpl in *...
  rewrite H0. clear.
  destruct i as [ies1 ies2].
  remember (SATsolver (ies2ses ies1)) as b.
  symmetry in Heqb.
  destruct b. Focus 2. 
  assert (~SAT(ies2ses ies1)).
   intro. rewrite<- SATsolver_correct in H.
   rewrite H in Heqb. inv Heqb.
  split;intros... apply IMPL_trivial...
  remember (eval_conjunct nIMPLbsolver (map transform (IMPLdecompose (ies1, ies2)))) as b1.
  symmetry in Heqb1.
  rewrite SATsolver_correct in Heqb.
  destruct b1. Focus 2.
  split;intros. inv H.
  assert (~nIMPL (ies1,ies2)).
   intro. rewrite IMPLsolver_case1 in H0...
   congruence.
  elimtype False. apply H0.
  apply IMPL_nIMPL...
  rewrite<- IMPLsolver_case1 in Heqb1...
  destruct (list_eq_dec sv.t_eq_dec (impl_nzvars ies2) nil).
  split;intros...
  apply IMPL_case3...
  destruct (list_eq_dec sv.t_eq_dec (impl_nzvars ies1) nil).
  rewrite IMPL_case2...
  rewrite eval_conjunct_true...
  split;intros.
  intros v H1. spec H v H1.
  apply IMPLsolver_case2...
  spec H a H0.
  apply IMPLsolver_case2...
  apply subroutine_correct...
 Qed.

End Solver.
(*
Extraction Language Ocaml.

Set Extraction AutoInline.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
 
Extraction Inline proj1_sig sigT_of_sig projT1.
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive prod => "(*)"  [ "(,)" ].
Extract Inductive sigT => "(*)"  [ "(,)" ].

Extraction "share_dec.ml" Solver.
*)