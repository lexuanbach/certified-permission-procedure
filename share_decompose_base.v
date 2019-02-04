Require Import msl.msl_standard.
Require Import NPeano.
Require Import share_dec_base.
Require Import base_properties.
Require Import share_equation_system.
Require Import share_dec_interface.
Require Import share_correctness_base.
Require Import share_correctness.

(*

Module SAT_Decompose_Base: 2 important lemmas: decompose_nSAT and decompose_sSAT

Module IMPL_Decompose_Base: 3 important lemmas: decompose_nIMPL, 
decompose_zIMPL and decompose_sIMPL

*)

Module Decompose_Base (sv : SV)
                      (Import es : EQUATION_SYSTEM sv with Module dom := Share_Domain)
                      (Import esf : SYSTEM_FEATURES sv es).

 (*Context*)
 Definition context_decompose : context -> (context * context):= 
  fun (ctx : context) =>
  (fun v => fst (decompose (ctx v)), fun v => snd (decompose (ctx v))).
 Instance decompose_context : decomposible context :=
  Decomposible context_decompose.

 Class recomposible (A : Type):= Recomposible {
  recompose : (A*A)-> A
 }.
 Implicit Arguments Recomposible [A].

 Instance share_recompose : recomposible share:= Recomposible Share.recompose.

 Definition context_recompose : (context*context) -> context :=
  fun p => fun v => recompose ((fst p) v, (snd p) v).
 Instance ctx_recompose : recomposible context := Recomposible context_recompose.

 Lemma decompose_context_eval: forall ctx ctxL ctxR v,
  decompose ctx = (ctxL,ctxR) ->
  decompose (ctx v) = (ctxL v,ctxR v).
 Proof.
  intros. inv H. simpl. destruct (Share.tree_decompose (ctx v)). auto.
 Qed.

 Lemma decompose_override: forall ctx ctxL ctxR ctx' ctxL' ctxR' l,
  decompose ctx = (ctxL,ctxR) ->
  decompose ctx' = (ctxL',ctxR') ->
  decompose ([l => ctx'] ctx) = ([l => ctxL'] ctxL,[l => ctxR'] ctxR).
 Proof with try tauto.
  induction l;intros.
  simpl...
  spec IHl H H0.
  simpl in *.
  unfold context_decompose in *.
  inv IHl. inv H. inv H0.
  f_equal;extensionality v.
  destruct (eq_dec a v). subst.
  repeat rewrite upd_eq...
  repeat rewrite upd_neq...
  destruct (eq_dec a v). subst.
  repeat rewrite upd_eq...
  repeat rewrite upd_neq...
 Qed. 
 
 Lemma ctx_recompose_decompose: forall (ctx : context),
  recompose (decompose ctx) = ctx.
 Proof.
  intros.
  remember (decompose ctx). destruct p as [ctxL ctxR].
  extensionality v.
  simpl in Heqp. unfold context_decompose in Heqp. inv Heqp.
  simpl. unfold context_recompose. simpl.
  generalize (Share.recompose_decompose (ctx v));intro.
  simpl in H.
  destruct (Share.tree_decompose (ctx v)). apply H.
 Qed.
 
 Lemma ctx_decompose_recompose: forall (p : (context*context)),
  decompose (recompose p) = p.
 Proof.
  intro. destruct p as [ctxL ctxR].
  simpl. unfold context_decompose,context_recompose.
  f_equal;extensionality v;
  rewrite Share.decompose_recompose;tauto.
 Qed.

 Lemma ctx_decompose_zero_var: forall ctx ctxL ctxR (v : var),
  decompose ctx = (ctxL,ctxR) ->
  |ctx v| = 0 ->
  |ctxL v| = 0 /\ |ctxR v| = 0.
 Proof with try tauto.
  intros.
  apply decompose_context_eval with (v:=v) in H.
  apply Share.decompose_height_zero in H...
  destruct H. rewrite H. rewrite H1...
 Qed.

 Lemma ctx_decompose_zero: forall ctx ctxL ctxR (l : list var),
  decompose ctx = (ctxL,ctxR) ->
  cheight ctx l = 0 ->
  cheight ctxL l = 0 /\ cheight ctxR l = 0.
 Proof with try tauto.
  induction l;intros.
  simpl...
  repeat rewrite cheight_rewrite in *.
  repeat rewrite max_zero in *.
  destruct H0.
  spec IHl H H1.
  apply ctx_decompose_zero_var with (v:=a) in H...
 Qed.

 Lemma ctx_decompose_decrease_var: forall ctx ctxL ctxR (v : var) n,
  decompose ctx = (ctxL,ctxR) ->
  (|ctx v| <= S n)%nat ->
  (|ctxL v| <= n)%nat /\ (|ctxR v| <= n)%nat.
 Proof with try tauto.
  intros.
  remember (|ctx v|) as m. symmetry in Heqm.
  icase m.
  apply ctx_decompose_zero_var with (v:=v) in H...
  destruct H. rewrite H,H1. omega.
  apply decompose_context_eval with (v:=v) in H.
  apply Share.decompose_height with (n:=m) in H...
  destruct H. simpl in *. omega.
 Qed.

 Lemma ctx_decompose_decrease: forall ctx ctxL ctxR (l : list var) n,
  decompose ctx = (ctxL,ctxR) ->
  (cheight ctx l <= S n)%nat->
  (cheight ctxL l <= n)%nat /\ (cheight ctxR l <= n)%nat.
 Proof with try tauto.
  induction l;intros. compute in *. omega.
  spec IHl n H.
  repeat rewrite cheight_rewrite in *.
  repeat rewrite Nat.max_lub_iff in *.
  destruct H0.
  spec IHl H1.
  apply ctx_decompose_decrease_var with (v:=a) (n:=n ) in H...
 Qed. 

(*System*)

 Definition decompose_list {A} `{decomposible A} := fun (l : list A) =>
  fold_right (fun a pl => let (aL,aR) := decompose a in (aL::(fst pl),aR::(snd pl))) (nil,nil) l.
  
 Instance decomposible_list {A} `{decomposible A} : decomposible (list A) :=
  Decomposible decompose_list.

 Definition decompose_obj := fun (obj : object) =>
  match obj with
  |Vobject v => (obj,obj)
  |Cobject c => let (c1,c2) := decompose c in (Cobject c1,Cobject c2)
  end.
 Instance obj_decomposible : decomposible object :=
  Decomposible decompose_obj.

 Definition decompose_eql := fun (eql : equality) => 
  let (obj1,obj2) := eql in
  let (obj1L,obj1R) := decompose obj1 in
  let (obj2L,obj2R) := decompose obj2 in
   ((obj1L,obj2L),(obj1R,obj2R)).
 Instance eql_decompose : decomposible equality :=
  Decomposible decompose_eql.

 Definition decompose_eqn := fun (eqn : equation) =>
  match eqn with (obj1,obj2,obj3) =>
  let (obj1L,obj1R) := decompose obj1 in
  let (obj2L,obj2R) := decompose obj2 in
  let (obj3L,obj3R) := decompose obj3 in
   ((obj1L,obj2L,obj3L),(obj1R,obj2R,obj3R))
  end.
 Instance eqn_decompose : decomposible equation :=
  Decomposible decompose_eqn.
  
 Definition decompose_ses := fun (ses : sat_equation_system) =>
  let (leqlL,leqlR) := decompose (sat_equalities ses) in
  let (leqnL,leqnR) := decompose (sat_equations ses)  in
  let l             := sat_nzvars ses                 in
   (Sat_equation_system l leqlL leqnL, Sat_equation_system l leqlR leqnR).
 Instance ses_decompose : decomposible sat_equation_system :=
  Decomposible decompose_ses.
 
 Definition decompose_ies := fun (ies : impl_equation_system) =>
  let (leqlL,leqlR) := decompose (impl_equalities ies) in
  let (leqnL,leqnR) := decompose (impl_equations ies) in
  let lex := impl_exvars ies in
  let lnz := impl_nzvars ies in
   (Impl_equation_system lex lnz leqlL leqnL, Impl_equation_system lex lnz leqlR leqnR).
 Instance ies_decompose : decomposible impl_equation_system :=
  Decomposible decompose_ies.

 Definition decompose_is := fun (is : impl_system) =>
  let (ies1,ies2) := is in
  let (ies1L,ies1R) := decompose ies1 in
  let (ies2L,ies2R) := decompose ies2 in
   ((ies1L,ies2L),(ies1R,ies2R)).
 Instance is_decompose : decomposible impl_system :=
  Decomposible decompose_is.

 (*Some trivial properties*)
 Lemma decompose_ies_exvars: forall (ies: impl_equation_system) iesL iesR,
  decompose ies = (iesL,iesR) ->
  impl_exvars iesL = impl_exvars ies /\ 
  impl_exvars iesR = impl_exvars ies.
 Proof.
  intros.
  simpl in H.
  destruct ies as [l1 l2 l3 l4].
  unfold decompose_ies in *. simpl in *.
  destruct (decompose_list l3).
  destruct (decompose_list l4).
  inv H. simpl. split;tauto.
 Qed.

 Lemma decompose_ies_nzvars: forall (ies: impl_equation_system) iesL iesR,
  decompose ies = (iesL,iesR) ->
  impl_nzvars iesL = impl_nzvars ies /\ 
  impl_nzvars iesR = impl_nzvars ies.
 Proof.
  intros.
  simpl in H.
  destruct ies as [l1 l2 l3 l4].
  unfold decompose_ies in *. simpl in *.
  destruct (decompose_list l3).
  destruct (decompose_list l4).
  inv H. simpl. split;tauto.
 Qed.

 Lemma decompose_is_rewrite: forall (is:impl_system) isL isR,
  decompose is = (isL,isR) <->
  decompose (fst is) = (fst isL, fst isR) /\
  decompose (snd is) = (snd isL, snd isR).
 Proof.
  intros.
  destruct is as [ies1 ies2].
  simpl.
  destruct (decompose_ies ies1).
  destruct (decompose_ies ies2).
  destruct isL;destruct isR;simpl.
  split;intros. inv H. tauto.
  destruct H. inv H. inv H0. tauto.
 Qed.

 Lemma decompose_replace_snzvars: forall ses sesL sesR l,
  decompose ses = (sesL,sesR) ->
  decompose (replace_snzvars ses l) = (replace_snzvars sesL l,replace_snzvars sesR l).
 Proof with try tauto.
  intros.
  destruct ses as [l1 l2 l3].
  destruct sesL as [l1L l2L l3L].
  destruct sesR as [l1R l2R l3R].
  simpl in *.
  unfold decompose_ses,replace_snzvars in *;simpl in *.
  destruct (decompose_list l2).
  destruct (decompose_list l3).
  inv H...
 Qed.

 Lemma decompose_replace_inzvars: forall ies iesL iesR l,
  decompose ies = (iesL,iesR) ->
  decompose (replace_inzvars ies l) = (replace_inzvars iesL l,replace_inzvars iesR l).
 Proof with try tauto.
  intros.
  destruct ies as [l1 l2 l3 l4].
  destruct iesL as [l1L l2L l3L l4L].
  destruct iesR as [l1R l2R l3R l4R].
  simpl in *.
  unfold decompose_ies,replace_inzvars in *;simpl in *.
  destruct (decompose_list l3).
  destruct (decompose_list l4).
  inv H...
 Qed.

 Lemma decompose_replace_isnzvars: forall is isL isR l1 l2,
  decompose is = (isL,isR) ->
  decompose (replace_isnzvars is l1 l2) = (replace_isnzvars isL l1 l2, replace_isnzvars isR l1 l2).
 Proof with try tauto.
  intros.
  rewrite decompose_is_rewrite in H.
  destruct H.
  destruct is as [ies1 ies2].
  apply decompose_replace_inzvars with (l:=l1) in H.
  apply decompose_replace_inzvars with (l:=l2) in H0.
  simpl in *.
  rewrite H,H0.
  destruct isL;destruct isR...
 Qed.

 Lemma decompose_ses_nzvars: forall ses sesL sesR,
  decompose ses = (sesL,sesR) ->
  sat_nzvars sesL = sat_nzvars ses /\ 
  sat_nzvars sesR = sat_nzvars ses.
 Proof with try tauto.
  intros.
  destruct ses as [l1 l2 l3].
  destruct sesL as [l1L l2L l3L].
  destruct sesR as [l1R l2R l3R].
  simpl in *. unfold decompose_ses in H;simpl in H.
  destruct (decompose_list l2);
  destruct (decompose_list l3);inv H...
 Qed.

 Lemma decompose_ies2ses: forall ies iesL iesR,
  decompose ies = (iesL,iesR) ->
  decompose (ies2ses ies) = (ies2ses iesL,ies2ses iesR).
 Proof with try tauto.
  intros.
  destruct ies as [l1 l2 l3 l4].
  destruct iesL as [l1L l2L l3L l4L].
  destruct iesR as [l1R l2R l3R l4R].
  simpl in *.
  unfold ies2ses,decompose_ses,decompose_ies in *;simpl in *.
  destruct (decompose_list l3).
  destruct (decompose_list l4).
  inv H...
 Qed.
 
 (*End trivial facts*)

 Definition decompose_height_nonzero_spec (A : Type) `{heightable A} `{decomposible A} :=
  forall a aL aR, decompose a = (aL,aR) -> |a| <> 0 -> 
   |aL| < |a| /\ |aR| < |a|. 
 
 Definition decompose_height_zero_spec (A : Type) `{heightable A} `{decomposible A} :=
  forall (a : A),  |a| = 0 -> decompose a = (a,a).

 Class decompose_height_prop (A : Type) `{heightable A} `{decomposible A}:= Decompose_height_prop {
   height_nonzero: decompose_height_nonzero_spec A;
   height_zero : decompose_height_zero_spec A
 }.

 Lemma height_no_increase: forall {A} `{decompose_height_prop A} (a : A) aL aR,
  decompose a = (aL,aR) -> (|aL| <= |a| /\ |aR| <= |a|)%nat.
 Proof with try tauto;try omega.
  intros.
  destruct H1 as [H3 H4]. 
  destruct (is_height_zero a).
  apply H4 in e. rewrite e in H2. inv H2...
  apply H3 in H2. detach H2...
 Qed.

 Lemma share_decompose_height_nonzero : decompose_height_nonzero_spec share.
 Proof with try omega.
  repeat intro.
  remember (|a|).
  icase n...
  symmetry in Heqn.
  destruct (Share.decompose_height _ _ _ _ Heqn H).
  split; simpl in *... 
 Qed.

 Lemma share_decompose_height_zero: decompose_height_zero_spec share.
 Proof with try tauto.
  repeat intro.
  remember (decompose a) as d.
  destruct d as [aL aR]. symmetry in Heqd.
  apply Share.decompose_height_zero in Heqd...
  destruct Heqd;subst...
 Qed.
 
 Instance share_decompose_height : decompose_height_prop share :=
  Decompose_height_prop _ _ _ share_decompose_height_nonzero share_decompose_height_zero .

 Lemma list_decompose_height_zero : forall {A} `{decompose_height_prop A}, 
  decompose_height_zero_spec (list A).
 Proof with try tauto.
  intros.
  do 1 intro.
  induction a;repeat intro...
  rewrite height_rewrite in H2.
  rewrite max_zero in H2. destruct H2.
  remember (decompose a0). destruct p as [lL lR]. symmetry in Heqp.
  remember (decompose a). destruct p as [aL' aR']. symmetry in Heqp0.
  spec IHa H3. inv IHa. copy Heqp0.
  rewrite height_zero in Heqp0... inv Heqp0.
  simpl in *. rewrite Heqp,Heqp1...
 Qed.

 Lemma list_decompose_height_nonzero : forall {A} `{decompose_height_prop A},
  decompose_height_nonzero_spec (list A).
 Proof with try tauto.
  intros.
  do 1 intro. induction a; repeat intro.
  inv H2... copy H1.
  destruct H1 as [H5 H6].
  remember (decompose a0). destruct p as [lL lR]. symmetry in Heqp.
  remember (decompose a). destruct p as [a1 a2]. symmetry in Heqp0.
  spec IHa lL lR. detach IHa...
  rewrite height_rewrite in H3.
  simpl in H2,Heqp.
  rewrite Heqp,Heqp0 in H2. inv H2.
  spec H5 a a1 a2 Heqp0.
  spec H6 a.
  assert (|a0| = 0 -> |lL| = 0 /\ |lR| = 0).
   intros.
   replace (decompose_list a0) with (decompose a0) in Heqp by tauto.
   rewrite list_decompose_height_zero in Heqp... inv Heqp...
  repeat rewrite height_rewrite.
  repeat rewrite Nat.max_lt_iff.
  repeat rewrite Nat.max_lub_lt_iff.
  rewrite max_nonzero in H3. destruct H3.
  destruct (is_height_zero a0).
  detach H1;try omega.
  spec IHa n. spec H5 H2; omega.
  destruct (is_height_zero a).
  spec H6 e. rewrite H6 in Heqp0. inv Heqp0;omega.
  spec H5 n. spec IHa H2;omega.
 Qed.

 Instance list_decompose_height {A} `{decompose_height_prop A}: decompose_height_prop (list A) :=
  Decompose_height_prop _ _ _ list_decompose_height_nonzero list_decompose_height_zero.

 (*This pattern shows up many places so I think we need a separate lemma for it*)
 Lemma decompose_height_max_nonzero: forall {A B} `{decompose_height_prop A} `{decompose_height_prop B}
  (a : A) (b : B) aL aR bL bR,
  max (|a|)(|b|) <> 0 ->
  decompose a = (aL,aR) ->
  decompose b = (bL,bR) ->
  max (|aL|)(|bL|) < max (|a|)(|b|) /\ max (|aR|)(|bR|) < max (|a|)(|b|).
 Proof with try tauto;try omega.
  intros.
  rewrite max_nonzero in H5.
  destruct H1 as [H8 H9].
  destruct H4 as [H10 H11].
  destruct H5.
  apply H8 in H6. detach H6...
  destruct (is_height_zero b). copy e.
  apply H11 in e... rewrite e in H7;inv H7.
  rewrite e0.
  repeat rewrite Max.max_0_r...
  apply H10 in H7. detach H7...
  repeat rewrite Nat.max_lt_iff.
  repeat rewrite Nat.max_lub_lt_iff...
  apply H10 in H7. detach H4...
  destruct (is_height_zero a). copy e.
  apply H9 in e. rewrite e in H6;inv H6.
  rewrite e0.
  repeat rewrite Max.max_0_l...
  apply H8 in H6. detach H6...
  repeat rewrite Nat.max_lt_iff.
  repeat rewrite Nat.max_lub_lt_iff...
 Qed.
(*
 Lemma decompose_height_max_zero: forall {A B} `{decompose_height_prop A} `{decompose_height_prop B}
  (a : A) (b : B) aL aR bL bR,
  max (|a|)(|b|) = 0 ->
  decompose (a,b) = (cL,cR) ->
  decompose a = (a,a) ->
  decompose b = (bL,bR) ->
  cL = (aL,bL) /\ cR.
 Proof with try tauto;try omega.
  repeat intro.
  rewrite max_zero in H5. destruct H5.
  destruct H1 as [H9 H10].
  destruct H4 as [H11 H12].
  apply H10 in H6. detach H6...
  apply H12 in H7. detach H7...
  repeat rewrite max_zero...
 Qed.
*)
 Lemma obj_decompose_height_zero: decompose_height_zero_spec object.
 Proof with auto.
  repeat intro.
  icase a. inv H...
  assert (|s0| = 0) by tauto.
  remember (decompose s0). destruct p. symmetry in Heqp.
  apply height_zero in H.
  unfold s,share in *.
  rewrite H in Heqp;inv Heqp.
  simpl in *. rewrite H...
 Qed.

 Lemma obj_decompose_height_nonzero: decompose_height_nonzero_spec object.
 Proof with try omega;try tauto.
  repeat intro.
  icase a.
  icase aL;icase aR;inv H.
  simpl in H0. tauto.
  assert (|s0| <> 0) by tauto.
  remember (decompose s0). destruct p as [a1 a2]. symmetry in Heqp.
  copy Heqp.
  apply height_nonzero in Heqp.
  detach Heqp...
  simpl in H,Heqp0.
  rewrite Heqp0 in H. inv H...
 Qed.

 Instance obj_decompose_height : decompose_height_prop object :=
  Decompose_height_prop _ _ _ obj_decompose_height_nonzero obj_decompose_height_zero.

 Lemma height_eql_rewrite: forall (o1 o2 : object),
  |(o1,o2)| = max (|o1|) (|o2|).
 Proof. tauto. Qed.

 Lemma eql_decompose_height_zero : decompose_height_zero_spec equality.
 Proof with auto.
  repeat intro.
  destruct a as [o1 o2].
  rewrite height_eql_rewrite in H.
  rewrite max_zero in H. destruct H.
  apply height_zero in H... 
  apply height_zero in H0...
  simpl in *.
  rewrite H,H0...
 Qed.

 Lemma eql_decompose_height_nonzero : decompose_height_nonzero_spec equality.
 Proof with auto.
  repeat intro.
  destruct a as [o1 o2].
  remember (decompose o1). destruct p. symmetry in Heqp.
  remember (decompose o2). destruct p. symmetry in Heqp0.
  unfold decompose,eql_decompose,decompose_eql in H.
  rewrite Heqp,Heqp0 in H. inv H.
  repeat rewrite height_eql_rewrite.
  apply decompose_height_max_nonzero...
 Qed.

 Instance eql_decompose_height : decompose_height_prop equality :=
  Decompose_height_prop _ _ _ eql_decompose_height_nonzero eql_decompose_height_zero.

 Lemma height_eqn_rewrite: forall (po : object*object) o,
  |(po,o)| = max (|po|) (|o|).
 Proof. tauto. Qed.

 Lemma eqn_decompose_height_zero : decompose_height_zero_spec equation.
 Proof with try tauto.
  repeat intro.
  destruct a as [[o1 o2] o3].
  rewrite height_eqn_rewrite in H.
  rewrite height_eql_rewrite in H.
  repeat rewrite max_zero in H.
  destruct H as [[? ?] ?].
  apply height_zero in H.
  apply height_zero in H0.
  apply height_zero in H1.
  simpl in *. rewrite H,H0,H1...
 Qed.

 Lemma eqn_decompose_height_nonzero : decompose_height_nonzero_spec equation.
 Proof with try tauto;try omega.
  repeat intro.
  destruct a as [po o].
  remember (decompose po). destruct p as [poL poR]. symmetry in Heqp.
  remember (decompose o). destruct p as [oL oR]. symmetry in Heqp0.
  assert (aL = (poL,oL) /\ aR = (poR,oR)).
    destruct po as [o2 o3].
    remember (decompose o2). destruct p as [o2L o2R]. symmetry in Heqp1.
    remember (decompose o3). destruct p as [o3L o3R]. symmetry in Heqp2.
    unfold decompose,eqn_decompose,decompose_eqn,eql_decompose,decompose_eql in Heqp,H.
    rewrite Heqp1,Heqp2 in Heqp. inv Heqp.
    rewrite Heqp0,Heqp1,Heqp2 in H. inv H...
  destruct H1. rewrite H1,H2.
  repeat rewrite height_eqn_rewrite.
  rewrite height_eqn_rewrite in H0.
  apply decompose_height_max_nonzero...
 Qed.

 Instance eqn_decompose_height : decompose_height_prop equation :=
  Decompose_height_prop _ _ _ eqn_decompose_height_nonzero eqn_decompose_height_zero.

 Lemma ses_decompose_height_zero: decompose_height_zero_spec sat_equation_system.
 Proof with try tauto.
  repeat intro.
  destruct a as [l1 l2 l3].
  assert (max (|l2|) (|l3|) = 0) by tauto.
  rewrite max_zero in H0.
  destruct H0.
  apply height_zero in H0.
  apply height_zero in H1.
  simpl in *. unfold decompose_ses;simpl.
  rewrite H0,H1...
 Qed.

 Lemma ses_decompose_height_nonzero: decompose_height_nonzero_spec sat_equation_system.
 Proof with try tauto;try omega.
  repeat intro.
  destruct a as [l1 l2 l3].
  assert (max (|l2|) (|l3|) <> 0) by tauto.
  destruct aL as [l1' l2' l3'].
  destruct aR as [l1'' l2'' l3''].
  remember (decompose l2). destruct p as [l2L l2R]. symmetry in Heqp.
  remember (decompose l3). destruct p as [l3L l3R]. symmetry in Heqp0.
  simpl in H. unfold decompose_ses in H. simpl in H.
  simpl in Heqp,Heqp0.
  rewrite Heqp,Heqp0 in H. inv H.
  simpl. unfold ses_h. simpl.
  generalize (decompose_height_max_nonzero l2 l3 _ _ _ _ H1 Heqp Heqp0);intro.
  apply H.
 Qed.

 Instance ses_decompose_height : decompose_height_prop sat_equation_system :=
  Decompose_height_prop _ _ _ ses_decompose_height_nonzero ses_decompose_height_zero.

 Lemma ies_decompose_height_zero : decompose_height_zero_spec impl_equation_system.
 Proof with try tauto.
  repeat intro.
  destruct a as [l1 l2 l3 l4].
  assert (max (|l3|)(|l4|) = 0) by tauto. clear H.
  rewrite max_zero in H0. destruct H0.
  apply height_zero in H. apply height_zero in H0.
  simpl in *. unfold decompose_ies;simpl.
  rewrite H,H0...
 Qed.
  
 Lemma ies_decompose_height_nonzero : decompose_height_nonzero_spec impl_equation_system.
 Proof with try tauto;try omega.
  repeat intro.
  destruct a as [l1 l2 l3 l4].
  assert (max (|l3|) (|l4|) <> 0) by tauto. clear H0.
  destruct aL as [l1' l2' l3' l4'].
  destruct aR as [l1'' l2'' l3'' l4''].
  simpl in H. unfold decompose_ies in H. simpl in H.
  remember (decompose l3). destruct p as [l3L l3R]. symmetry in Heqp.
  remember (decompose l4). destruct p as [l4L l4R]. symmetry in Heqp0.
  simpl in Heqp, Heqp0.
  rewrite Heqp,Heqp0 in H. inv H.
  simpl. unfold ies_h. simpl.
  generalize (decompose_height_max_nonzero l3 l4 _ _ _ _ H1 Heqp Heqp0);intro.
  apply H...
 Qed.

 Instance ies_decompose_height : decompose_height_prop impl_equation_system :=
  Decompose_height_prop _ _ _ ies_decompose_height_nonzero ies_decompose_height_zero.

 Lemma height_is_rewrite: forall (ies1 ies2 : impl_equation_system),
  |(ies1,ies2)| = max (|ies1|) (|ies2|).
 Proof. tauto. Qed.

 Lemma is_decompose_height_zero : decompose_height_zero_spec impl_system.
 Proof with try tauto.
  repeat intro.
  destruct a as [ies1 ies2].
  rewrite height_is_rewrite in H.
  rewrite max_zero in H.
  destruct H.
  apply height_zero in H.
  apply height_zero in H0.
  simpl in *. rewrite H,H0...
 Qed.

 Lemma is_decompose_height_nonzero : decompose_height_nonzero_spec impl_system.
 Proof with try tauto;try omega.
  repeat intro.
  destruct a as [ies1 ies2].
  destruct aL as [ies1' ies2'].
  destruct aR as [ies1'' ies2''].
  remember (decompose ies1). destruct p as [ies1L ies1R]. symmetry in Heqp.
  remember (decompose ies2). destruct p as [ies2L ies2R]. symmetry in Heqp0.
  simpl in H,Heqp,Heqp0.
  rewrite Heqp,Heqp0 in H. inv H.
  repeat rewrite height_is_rewrite in *.
  apply decompose_height_max_nonzero...
 Qed.

 Instance is_decompose_height : decompose_height_prop impl_system :=
  Decompose_height_prop _ _ _ is_decompose_height_nonzero is_decompose_height_zero.

 Definition decompose_eval_spec (A B : Type) `{decomposible A} `{decomposible B} `{evalable B A} :=
  forall (a aL aR : A) (b bL bR: B),
  decompose a = (aL,aR) ->
  decompose b = (bL,bR) ->
  (b |= a <-> (bL |= aL /\ bR |= aR)). 

 Class decompose_eval_prop (A B : Type) `{decomposible A} `{decomposible B} `{evalable B A}:= Decompose_eval_prop {
   decompose_eval : decompose_eval_spec A B
 }.
  
 Lemma list_decompose_eval_correct:
  forall {A B} `{decompose_eval_prop A B},
  decompose_eval_spec (list A) B.
 Proof with try tauto.
  induction a;intros.
  inv H3...
  remember (decompose a). destruct p as [a1 a2]. symmetry in Heqp.
  remember (decompose a0). destruct p as [l1 l2]. symmetry in Heqp0.
  generalize (decompose_eval _ _ _ _ _ _ Heqp H4);intro.
  spec IHa l1 l2 b bL bR.
  detach IHa... detach IHa...
  simpl in H3,Heqp0.
  rewrite Heqp,Heqp0 in H3. inv H3.
  simpl...
 Qed.

 Instance list_decompose_eval {A B} `{decompose_eval_prop A B}: decompose_eval_prop (list A) B.
 constructor. apply list_decompose_eval_correct.
 Defined.

 Lemma obj_decompose_eval: forall (ctx :context) ctxL ctxR (obj : object) objL objR sL sR,
  decompose obj = (objL,objR) ->
  decompose ctx = (ctxL,ctxR) ->
  decompose (get ctx obj) = (sL,sR) ->
  get ctxL objL = sL /\ get ctxR objR = sR.
 Proof with try tauto.
  intros. inv H0.
  destruct obj; inv H.
  simpl in *. rewrite H1...
  simpl in H1.
  rewrite H1 in H2. inv H2...
 Qed.

 Lemma nzvars_decompose_eval: forall (l : list var) ctx ctxL ctxR,
  decompose ctx = (ctxL,ctxR) ->
  (ctx |= l <-> forall v, In v l -> ctxL |= v \/ ctxR |= v).
 Proof with try tauto.
  induction l;intros. simpl. tauto.
  remember (decompose (ctx a)). destruct p as [aL aR]. symmetry in Heqp.
  generalize (Share.decompose_nonzero _ _ _ Heqp);intro.
  rewrite decompose_context_eval with (ctxL:=ctxL)(ctxR:=ctxR) in Heqp...
  inv Heqp.
  simpl. split;intros.
  destruct H2. subst.
  destruct H1. apply H0...
  eapply IHl. apply H. apply H1. apply H2.
  split.
  eapply IHl. apply H.
  repeat intros. apply H1. right...
  apply H0. apply H1...
 Qed.

 Lemma eql_decompose_eval_correct : decompose_eval_spec equality context.
 Proof.
  repeat intro.
  destruct a as [o1 o2].
  remember (decompose o1). destruct p as [o1L o1R]. symmetry in Heqp.
  remember (decompose o2). destruct p as [o2L o2R]. symmetry in Heqp0.
  simpl in *.
  rewrite Heqp,Heqp0 in H. inv H.
  remember (decompose (get b o1)). destruct p. symmetry in Heqp1.
  remember (decompose (get b o2)). destruct p. symmetry in Heqp2.
  destruct (obj_decompose_eval _ _ _ _ _ _ _ _ Heqp H0 Heqp1).
  destruct (obj_decompose_eval _ _ _ _ _ _ _ _ Heqp0 H0 Heqp2).
  generalize (Share.decompose_equal _ _ _ _ _ _ Heqp1 Heqp2);intro.
  simpl in *. 
  rewrite H,H1,H2,H3. auto.
 Qed.

 Instance eql_decompose_eval : decompose_eval_prop equality context.
 constructor. apply eql_decompose_eval_correct.
 Defined.

 Lemma eqn_decompose_eval_correct : decompose_eval_spec equation context.
 Proof.
  repeat intro.
  destruct a as [[o1 o2] o3].
  remember (decompose o1). destruct p as [o1L o1R]. symmetry in Heqp.
  remember (decompose o2). destruct p as [o2L o2R]. symmetry in Heqp0.
  remember (decompose o3). destruct p as [o3L o3R]. symmetry in Heqp1.
  simpl in *.
  rewrite Heqp,Heqp0,Heqp1 in H. inv H.
  remember (decompose (get b o1)). destruct p. symmetry in Heqp2.
  remember (decompose (get b o2)). destruct p. symmetry in Heqp3.
  remember (decompose (get b o3)). destruct p. symmetry in Heqp4.
  destruct (obj_decompose_eval _ _ _ _ _ _ _ _ Heqp H0 Heqp2).
  destruct (obj_decompose_eval _ _ _ _ _ _ _ _ Heqp0 H0 Heqp3).
  destruct (obj_decompose_eval _ _ _ _ _ _ _ _ Heqp1 H0 Heqp4).
  generalize (Share.decompose_join _ _ _ _ _ _ _ _ _ Heqp2 Heqp3 Heqp4);intro.
  simpl in *.
  rewrite H,H1,H2,H3,H4,H5. auto.
 Qed.

 Instance eqn_decompose_eval : decompose_eval_prop equation context.
 constructor. apply eqn_decompose_eval_correct.
 Defined.

 Lemma decompose_ses_eval_nil: 
  forall (ses : sat_equation_system) sesL sesR ctx ctxL ctxR,
  sat_nzvars ses = nil ->
  decompose ses = (sesL,sesR) ->
  decompose ctx = (ctxL,ctxR) ->
  (ctx |= ses <-> ctxL |= sesL /\ ctxR |= sesR).
 Proof.
  repeat intros.
  destruct ses as [l1 l2 l3].
  destruct sesL as [l1L l2L l3L].
  destruct sesR as [l1R l2R l3R].
  simpl in H0. unfold decompose_ses in H0. simpl in H0.
  simpl in H. inv H. simpl.
  unfold eval_sat_equation_system. simpl.
  remember (decompose l2). destruct p. symmetry in Heqp.
  remember (decompose l3). destruct p. symmetry in Heqp0.
  generalize (decompose_eval _ _ _ _ _ _ Heqp H1);intro.
  generalize (decompose_eval _ _ _ _ _ _ Heqp0 H1);intro.
  simpl in Heqp,Heqp0.
  rewrite Heqp,Heqp0 in H0. inv H0. simpl. tauto.
 Qed.

 Lemma decompose_ses_eval: forall (ses: sat_equation_system) sesL sesR ctx ctxL ctxR,
  decompose ses = (sesL,sesR) ->
  decompose ctx = (ctxL,ctxR) ->
  (ctx |= ses <-> ctxL |= (replace_snzvars sesL nil) /\ ctxR |= (replace_snzvars sesR nil) /\ 
                  forall v, In v (sat_nzvars ses) -> (ctxL |= v \/ ctxR |= v)).
 Proof with try tauto.
  repeat intros.
  rewrite replace_snzvars_nil_eval.
  rewrite<- nzvars_decompose_eval with (ctx:=ctx)...
  rewrite decompose_ses_eval_nil with (ctxL:=ctxL)(ctxR:=ctxR)...
  Focus 2. apply decompose_replace_snzvars. apply H.
  tauto.
 Qed.

 Lemma decompose_ses_eval_single: forall ses sesL sesR ctx ctxL ctxR x,
  sat_nzvars ses = x::nil ->
  decompose ses = (sesL,sesR) ->
  decompose ctx = (ctxL,ctxR) ->
  ctx |=  replace_snzvars ses nil ->
  (ctx |= ses <-> ctxL |= sesL \/ ctxR |= sesR).
 Proof with try tauto.
  intros.
  generalize (decompose_ses_eval _ _ _ _ _ _ H0 H1);intro.
  rewrite H3.
  assert (sat_nzvars (replace_snzvars ses nil) = nil) by tauto.
  generalize (decompose_replace_snzvars _ _ _ nil H0);intro.
  generalize (decompose_ses_eval_nil _ _ _ _ _ _ H4 H5 H1);intro.
  apply H6 in H2.
  split;intros.
  destruct H7 as [H7 [H8 H9]].
  spec H9 x. detach H9.
  destruct (decompose_ses_nzvars _ _ _ H0).
  destruct H9.
  left. rewrite replace_snzvars_nil_eval.
  split... rewrite H10,H. split... simpl...
  right. rewrite replace_snzvars_nil_eval.
  split... rewrite H11,H. split... simpl...
  rewrite H. left...
  split... split...
  rewrite H. intros. destruct H8... subst.
  destruct (decompose_ses_nzvars _ _ _ H0).
  destruct H7;rewrite replace_snzvars_nil_eval in H7;
  destruct H7 as [H10 H11].
  rewrite H8,H in H11. destruct H11. left...
  rewrite H9,H in H11. destruct H11. right...
 Qed.

 Lemma decompose_ses_SAT : forall (ses : sat_equation_system) sesL sesR,
  decompose ses = (sesL,sesR) ->
  (SAT sesL /\ SAT sesR) -> SAT ses.
 Proof with auto.
  intros.
  destruct H0 as [[ctxL H1] [ctxR H2]].
  remember (recompose (ctxL,ctxR)) as ctx.
  apply f_apply with (f:=decompose) in Heqctx.
  rewrite ctx_decompose_recompose in Heqctx.
  exists ctx.
  generalize (decompose_ses_eval _ _ _ _ _ _ H Heqctx);intro.
  apply H0.
  rewrite replace_snzvars_nil_eval in H1,H2.
  destruct H1. destruct H2.
  rewrite list_eval_rewrite in H3.
  split... split...
  intros. left. apply H3.
  generalize (decompose_ses_nzvars _ _ _ H);intro.
  destruct H6. rewrite H6...
 Qed.

 Lemma decompose_nSAT : forall ses sesL sesR,
  decompose ses = (sesL,sesR) ->
  (nSAT ses <-> nSAT sesL /\ nSAT sesR).
 Proof with try tauto.
  intros.
  split. Focus 2.
  apply decompose_ses_SAT.
  apply decompose_replace_snzvars...
  intro. destruct H0 as [ctx H0].
  remember (decompose ctx) as d.
  destruct d as [ctxL ctxR]. symmetry in Heqd.
  assert (sat_nzvars (replace_snzvars ses nil) = nil) by apply replace_snzvars_correct.
  apply decompose_replace_snzvars with (l:=nil) in H.
  generalize (decompose_ses_eval_nil _ _ _ _ _ _ H1 H Heqd);intro.
  apply H2 in H0.
  destruct H0.
  split. exists ctxL... exists ctxR...
 Qed.
  
 Lemma decompose_sSAT: forall ses sesL sesR x,
  nSAT ses ->
  decompose ses = (sesL,sesR) ->
  (sSAT ses x <-> sSAT sesL x \/ sSAT sesR x).
 Proof with try tauto.
  intros.
  rewrite decompose_nSAT with (sesL:=sesL)(sesR:=sesR)in H...
  destruct H.
  destruct H as [ctxL H].
  destruct H1 as [ctxR H1].
  copy H0.
  apply decompose_replace_snzvars with (l:= x::nil) in H0.
  split;intros.
  destruct H3 as [ctx H3].
  remember (decompose ctx) as d.
  destruct d as [ctxL' ctxR']. symmetry in Heqd.
  generalize (decompose_ses_eval _ _ _ _ _ _ H0 Heqd);intro.
  apply H4 in H3.
  destruct H3 as [? [? ?]].
  rewrite replace_snzvars_correct in H6.
  spec H6 x. detach H6. destruct H6.
  left. exists ctxL'.
  rewrite replace_snzvars_nil_eval.
  rewrite replace_snzvars_reduce,replace_snzvars_correct.
  split... split... simpl...
  right. exists ctxR'.
  rewrite replace_snzvars_nil_eval.
  rewrite replace_snzvars_reduce,replace_snzvars_correct.
  split... split... simpl...
  left...

  destruct H3.

  destruct H3 as [ctxL' H3].
  remember (recompose (ctxL',ctxR)) as ctx.
  apply f_apply with (f:=decompose) in Heqctx.
  rewrite ctx_decompose_recompose in Heqctx.
  rewrite replace_snzvars_nil_eval in H3.
  rewrite replace_snzvars_reduce,replace_snzvars_correct in H3.
  destruct H3. destruct H4 as [_ H4].
  exists ctx.
  rewrite replace_snzvars_nil_eval.
  rewrite replace_snzvars_reduce,replace_snzvars_correct.
  split.
  eapply decompose_ses_eval_nil with (ctxL:=ctxL')(ctxR:=ctxR)...
  apply decompose_replace_snzvars. apply H2.
  split...
  generalize (nzvars_decompose_eval (x::nil) _ _ _ Heqctx);intro.
  apply H5. intros. destruct H6... subst...

  destruct H3 as [ctxR' H3].
  remember (recompose (ctxL,ctxR')) as ctx.
  apply f_apply with (f:=decompose) in Heqctx.
  rewrite ctx_decompose_recompose in Heqctx.
  rewrite replace_snzvars_nil_eval in H3.
  rewrite replace_snzvars_reduce,replace_snzvars_correct in H3.
  destruct H3. destruct H4 as [_ H4].
  exists ctx.
  rewrite replace_snzvars_nil_eval.
  rewrite replace_snzvars_reduce,replace_snzvars_correct.
  split.
  eapply decompose_ses_eval_nil with (ctxL:=ctxL)(ctxR:=ctxR')...
  apply decompose_replace_snzvars. apply H2.
  split...
  generalize (nzvars_decompose_eval (x::nil) _ _ _ Heqctx);intro.
  apply H5. intros. destruct H6... subst...
 Qed.

 (*IMPL section*)
 
 Import ClassicalProps.
 Module IB := IMPL_Base sv es esf.
 Import IB.
 Module IC := IMPL_Correctness sv es esf.
 Import IC.

 Lemma decompose_ies_eval_correct1:
  forall (ies: impl_equation_system) iesL iesR ctx ctxL ctxR,
  impl_nzvars ies = nil ->
  decompose ies = (iesL,iesR) ->
  decompose ctx = (ctxL,ctxR) ->
  (ctx |= ies <-> ctxL |= iesL /\ ctxR |= iesR).
 Proof with try tauto.
  repeat intro.
  destruct ies as [l1 l2 l3 l4].
  destruct iesL as [l1L l2L l3L l4L].
  destruct iesR as [l1R l2R l3R l4R].
  simpl in *. subst.
  unfold decompose_ies, eval_impl_equation_system,e_eval in *.
  simpl in *.
  unfold ies2ses,eval_sat_equation_system. simpl.
  remember (decompose_list l3). destruct p as [l3L' l3R'].
  remember (decompose_list l4). destruct p as [l4L' l4Rl].
  inv H0. symmetry in Heqp0,Heqp.
  replace (decompose_list l4) with (decompose l4) in Heqp0 by tauto.
  replace (decompose_list l3) with (decompose l3) in Heqp by tauto.
  split;intro. destruct H as [ctx' [H2 [H3 _]]].
  remember (decompose ctx'). destruct p as [ctxL' ctxR'].
  symmetry in Heqp1.
  generalize (decompose_override _ _ _ _ _ _ l1R H1 Heqp1);intro.
  generalize (decompose_eval _ _ _ _ _ _ Heqp0 H);intro.
  generalize (decompose_eval _ _ _ _ _ _ Heqp H);intro.
  simpl in H0,H4. rewrite H0 in H3. rewrite H4 in H2.
  simpl. split. exists ctxL'... exists ctxR'...
  
  destruct H as [[ctxL' H2] [ctxR' H3]].
  remember (recompose (ctxL',ctxR')) as ctx'.
  apply f_apply with (f:= decompose) in Heqctx'.
  rewrite ctx_decompose_recompose in Heqctx'.
  generalize (decompose_override _ _ _ _ _ _ l1R H1 Heqctx');intro.
  generalize (decompose_eval _ _ _ _ _ _ Heqp0 H);intro.
  generalize (decompose_eval _ _ _ _ _ _ Heqp H);intro.
  exists ctx'...
 Qed.

 Lemma decompose_ies_eval_correct2:
  forall (ies: impl_equation_system) iesL iesR ctx ctxL ctxR v,
  impl_nzvars ies = v::nil ->
  decompose ies = (iesL,iesR) ->
  decompose ctx = (ctxL,ctxR) ->
  ctx |= replace_inzvars ies nil ->
  (ctx |= ies <-> ctxL |= iesL \/ ctxR |= iesR).
 Proof with try tauto.
  intros.
  generalize (replace_inzvars_correct ies nil);intro.
  generalize (decompose_replace_inzvars _ _ _ nil H0);intro.
  generalize (decompose_ies_eval_correct1 _ _ _ _ _ _ H3 H4 H1);intro.
  copy H2. apply H5 in H6. destruct H6.
  rewrite neg_equiv.
  rewrite neg_or.
  generalize (decompose_ies_nzvars _ _ _ H0);intro.
  destruct H8.
  generalize (decompose_ies_exvars _ _ _ H0);intro.
  destruct H10.

  split;repeat intro.
  split;repeat intro;apply H12.
  destruct H13 as [rhoL' H14].
  destruct H7 as [rhoR' H15].
  rewrite replace_inzvars_ies2ses,replace_inzvars_exvars in *.
  rewrite H10 in H14. rewrite H11 in H15.
  remember (recompose (rhoL',rhoR')) as rho'.
  apply f_apply with (f:=decompose) in Heqrho'.
  rewrite ctx_decompose_recompose in Heqrho'.
  exists rho'.
  generalize (decompose_override _ _ _ _ _ _ (impl_exvars ies) H1 Heqrho');intro.
  rewrite replace_snzvars_nil_eval in H14.
  rewrite<-ies2ses_nzvars in H14.
  rewrite H8 in H14.
  rewrite replace_snzvars_nil_eval.
  rewrite<-ies2ses_nzvars.
  split.
  apply decompose_ies2ses in H0.
  apply decompose_replace_snzvars with (l:=nil) in H0.
  eapply decompose_ses_eval_nil 
   with (ctxL:=[impl_exvars ies => rhoL']ctxL)
        (ctxR:=[impl_exvars ies => rhoR']ctxR)...
  apply H0. split...
  destruct H14.
  rewrite nzvars_decompose_eval. 
  Focus 2. apply H7. intros.
  rewrite list_eval_rewrite in H14.
  spec H14 v0 H16...

  destruct H13 as [rhoR' H15].
  destruct H6 as [rhoL' H14].
  rewrite replace_inzvars_ies2ses,replace_inzvars_exvars in *.
  rewrite H10 in H14. rewrite H11 in H15.
  remember (recompose (rhoL',rhoR')) as rho'.
  apply f_apply with (f:=decompose) in Heqrho'.
  rewrite ctx_decompose_recompose in Heqrho'.
  exists rho'.
  generalize (decompose_override _ _ _ _ _ _ (impl_exvars ies) H1 Heqrho');intro.
  rewrite replace_snzvars_nil_eval in H15.
  rewrite<-ies2ses_nzvars in H15.
  rewrite H9 in H15.
  rewrite replace_snzvars_nil_eval.
  rewrite<-ies2ses_nzvars.
  split.
  apply decompose_ies2ses in H0.
  apply decompose_replace_snzvars with (l:=nil) in H0.
  eapply decompose_ses_eval_nil 
   with (ctxL:=[impl_exvars ies => rhoL']ctxL)
        (ctxR:=[impl_exvars ies => rhoR']ctxR)...
  apply H0. split...
  destruct H15.
  rewrite nzvars_decompose_eval. 
  Focus 2. apply H6. intros.
  rewrite list_eval_rewrite in H15.
  spec H15 v0 H16...


  destruct H12.
  destruct H13 as [rho' H13].
  rewrite replace_snzvars_nil_eval in H13.
  rewrite<- ies2ses_nzvars in H13.
  rewrite H in H13.
  destruct H13.
  remember (decompose rho') as d.
  destruct d as [rhoL' rhoR'].
  symmetry in Heqd.
  destruct H15 as [_ H15].
  generalize (decompose_override _ _ _ _ _ _ (impl_exvars ies) H1 Heqd);intro.
  apply decompose_ies2ses in H0.
  apply decompose_replace_snzvars with (l:=nil) in H0.
  generalize (decompose_context_eval _ _ _ v H16);intro.
  apply Share.decompose_nonzero in H17.
  rewrite H17 in H15.
  assert (sat_nzvars (replace_snzvars (ies2ses ies) nil) = nil)
   by (apply replace_snzvars_correct;tauto).
  generalize (decompose_ses_eval_nil _ _ _ _ _ _ H18 H0 H16);intro.
  apply H19 in H13.

  destruct H15.

  apply H12. exists rhoL'.
  rewrite replace_snzvars_nil_eval.
  rewrite<- ies2ses_nzvars.
  rewrite H8,H10,H.
  split... split... simpl...

  apply H14. exists rhoR'.
  rewrite replace_snzvars_nil_eval.
  rewrite<- ies2ses_nzvars.
  rewrite H9,H11,H.
  split... split... simpl...
 Qed.

 Lemma decompose_nIMPL: forall (is:impl_system) isL isR,
  nSAT (ies2ses (fst is)) ->
  decompose is = (isL,isR) ->
  (nIMPL is <-> nIMPL isL /\ nIMPL isR).
 Proof with try tauto.
  intros.
  destruct H as [rho H].
  rewrite decompose_is_rewrite in H0.
  destruct H0.
  remember (decompose rho) as d.
  destruct d as [rhoL rhoR]. symmetry in Heqd.
  assert (rho |= replace_inzvars (fst is) nil).
   exists rho.
   rewrite context_override_idem...
  generalize (replace_inzvars_correct (fst is) nil);intro.
  generalize (replace_inzvars_correct (snd is) nil) ;intro.
  generalize (decompose_replace_inzvars _ _ _ nil H0);intro.
  generalize (decompose_replace_inzvars _ _ _ nil H1);intro.
  generalize (decompose_ies_eval_correct1 _ _ _ _ _ _ H3 H5 Heqd);intro.  
  apply H7 in H2. destruct H2.
  split;intro.
  split.

  intro ctxL.
  rewrite replace_isnzvars_eval;intro.
  remember (recompose (ctxL,rhoR)) as ctx.
  apply f_apply with (f:=decompose) in Heqctx.
  rewrite ctx_decompose_recompose in Heqctx.
  generalize (decompose_ies_eval_correct1 _ _ _ _ _ _ H3 H5 Heqctx);intro.
  assert (ctx |= replace_inzvars (fst is) nil) by (apply H11;tauto).
  spec H9 ctx. rewrite replace_isnzvars_eval in H9.
  spec H9 H12.
  generalize (decompose_ies_eval_correct1 _ _ _ _ _ _ H4 H6 Heqctx);intro.
  apply H13 in H9.
  destruct H9...

  intro ctxR.
  rewrite replace_isnzvars_eval;intro.
  remember (recompose (rhoL,ctxR)) as ctx.
  apply f_apply with (f:=decompose) in Heqctx.
  rewrite ctx_decompose_recompose in Heqctx.
  generalize (decompose_ies_eval_correct1 _ _ _ _ _ _ H3 H5 Heqctx);intro.
  assert (ctx |= replace_inzvars (fst is) nil) by (apply H11;tauto).
  spec H9 ctx. rewrite replace_isnzvars_eval in H9.
  spec H9 H12.
  generalize (decompose_ies_eval_correct1 _ _ _ _ _ _ H4 H6 Heqctx);intro.
  apply H13 in H9.
  destruct H9...

  destruct H9.
  intro ctx. rewrite replace_isnzvars_eval;intro.
  remember (decompose ctx) as d.
  destruct d as [ctxL ctxR]. symmetry in Heqd0.
  generalize (decompose_ies_eval_correct1 _ _ _ _ _ _ H3 H5 Heqd0);intro.
  apply H12 in H11. destruct H11.
  spec H9 ctxL. spec H10 ctxR.
  rewrite replace_isnzvars_eval in H9,H10.
  spec H9 H11. spec H10 H13.
  generalize (decompose_ies_eval_correct1 _ _ _ _ _ _ H4 H6 Heqd0);intro.
  apply H14...
 Qed.

 Lemma decompose_zIMPL: forall is isL isR y,
  nIMPL is ->
  decompose is = (isL,isR) ->
  (zIMPL is y <-> zIMPL isL y \/ zIMPL isR y).
 Proof with try tauto.
  intros.
  rewrite decompose_is_rewrite in H0.
  destruct H0.
  generalize (replace_inzvars_correct (fst is) nil);intro.
  generalize (replace_inzvars_correct (snd is) (y::nil)) ;intro.
  generalize (decompose_replace_inzvars _ _ _ nil H0);intro.
  generalize (decompose_replace_inzvars _ _ _ (y::nil) H1);intro.

  rewrite neg_equiv.
  rewrite neg_or.
  repeat rewrite neg_zIMPL_correct.
  split;intros.
  destruct H6 as [rho H6].
  rewrite fst_replace_isnzvars,snd_replace_isnzvars in *.
  destruct H6.
  remember (decompose rho) as d.
  destruct d as [rhoL rhoR]. symmetry in Heqd.
  generalize (decompose_ies_eval_correct1 _ _ _ _ _ _ H2 H4 Heqd);intro.
  generalize (decompose_ies_eval_correct2 _ _ _ _ _ _ _ H3 H5 Heqd);intro.
  spec H rho. rewrite replace_isnzvars_eval in H.
  spec H H6.
  rewrite replace_inzvars_reduce in H9. spec H9 H.
  rewrite neg_equiv in H9.
  apply H9 in H7.
  apply H8 in H6.
  split. exists rhoL.
  rewrite fst_replace_isnzvars,snd_replace_isnzvars...
  exists rhoR.
  rewrite fst_replace_isnzvars,snd_replace_isnzvars...
  
  destruct H6.
  destruct H6 as [rhoL H6].
  destruct H7 as [rhoR H7].
  rewrite fst_replace_isnzvars,snd_replace_isnzvars in *.
  destruct H6. destruct H7.
  remember (recompose (rhoL,rhoR)) as rho.
  apply f_apply with (f:=decompose) in Heqrho.
  rewrite ctx_decompose_recompose in Heqrho.
  generalize (decompose_ies_eval_correct1 _ _ _ _ _ _ H2 H4 Heqrho);intro.
  assert (rho |= replace_inzvars (fst is) nil) by (apply H10;tauto).
  spec H rho. rewrite replace_isnzvars_eval in H.
  spec H H11.
  generalize (decompose_ies_eval_correct2 _ _ _ _ _ _ _ H3 H5 Heqrho H);intro.
  rewrite neg_equiv in H12.
  exists rho.
  rewrite fst_replace_isnzvars,snd_replace_isnzvars...
 Qed.

 Lemma decompose_sIMPL_1: forall is isL isR x y,
  decompose is = (isL,isR) ->
  sIMPL is x y ->
  (sIMPL isL x y \/ zIMPL isR y) /\ (zIMPL isL y \/ sIMPL isR x y).
 Proof with try tauto.
  intros.
  repeat rewrite or_equiv.
  repeat rewrite neg_sIMPL_correct,neg_zIMPL_correct.
  rewrite decompose_is_rewrite in H.
  destruct H.
  generalize (replace_inzvars_correct (fst is) (x::nil));intro.
  generalize (replace_inzvars_correct (snd is) (y::nil)) ;intro.
  generalize (decompose_replace_inzvars _ _ _ (x::nil) H);intro.
  generalize (decompose_replace_inzvars _ _ _ (y::nil) H1);intro.

  split;intro H6;destruct H6 as [H6 H7].

  destruct H6 as [rhoL H6].
  destruct H7 as [rhoR H7].
  rewrite fst_replace_isnzvars,snd_replace_isnzvars in *.
  destruct H6. destruct H7.
  remember (recompose (rhoL,rhoR)) as rho.
  apply f_apply with (f:=decompose) in Heqrho.
  rewrite ctx_decompose_recompose in Heqrho.
  assert (rho |= replace_inzvars (fst is) nil).
   assert (rhoL |= replace_inzvars (fst isL) nil) by 
    (apply replace_inzvars_eval_nil in H6;trivial).
   apply decompose_replace_inzvars with (l:=nil) in H.
   generalize (replace_inzvars_correct (fst is) nil);intro.
   generalize (decompose_ies_eval_correct1 _ _ _ _ _ _ H11 H Heqrho);intro.
   apply H12...
  generalize (decompose_ies_eval_correct2 _ _ _ _ _ _ _ H2 H4 Heqrho H10);intro.
  assert (rho |= replace_inzvars (fst is) (x::nil)) by (apply H11;tauto).
  spec H0 rho.
  rewrite replace_isnzvars_eval in H0. spec H0 H12.
  assert (rho |= replace_inzvars (snd is) nil) 
   by (apply replace_inzvars_eval_nil in H0;trivial).
  generalize (decompose_ies_eval_correct2 _ _ _ _ _ _ _ H3 H5 Heqrho H13);intro.
  rewrite neg_equiv in H14.
  rewrite neg_or in H14.
  apply H14...

  destruct H6 as [rhoL H6].
  destruct H7 as [rhoR H7].
  rewrite fst_replace_isnzvars,snd_replace_isnzvars in *.
  destruct H6. destruct H7.
  remember (recompose (rhoL,rhoR)) as rho.
  apply f_apply with (f:=decompose) in Heqrho.
  rewrite ctx_decompose_recompose in Heqrho.
  assert (rho |= replace_inzvars (fst is) nil).
   assert (rhoR |= replace_inzvars (fst isR) nil) 
    by (apply replace_inzvars_eval_nil in H7;trivial).
   apply decompose_replace_inzvars with (l:=nil) in H.
   generalize (replace_inzvars_correct (fst is) nil);intro.
   generalize (decompose_ies_eval_correct1 _ _ _ _ _ _ H11 H Heqrho);intro.
   apply H12...
  generalize (decompose_ies_eval_correct2 _ _ _ _ _ _ _ H2 H4 Heqrho H10);intro.
  assert (rho |= replace_inzvars (fst is) (x::nil)) by (apply H11;tauto).
  spec H0 rho.
  rewrite replace_isnzvars_eval in H0. spec H0 H12.
  assert (rho |= replace_inzvars (snd is) nil)
   by (apply replace_inzvars_eval_nil in H0;trivial).
  generalize (decompose_ies_eval_correct2 _ _ _ _ _ _ _ H3 H5 Heqrho H13);intro.
  rewrite neg_equiv in H14.
  rewrite neg_or in H14.
  apply H14...
 Qed.

 Lemma decompose_sIMPL_2: forall is isL isR x y,
  decompose is = (isL,isR) ->
  nIMPL is ->
  sIMPL isL x y \/ zIMPL isR y ->
  zIMPL isL y \/ sIMPL isR x y ->
  sIMPL is x y.
 Proof with try tauto.
  intros.
  destruct H1.
  Focus 2.
  apply zIMPL_sIMPL...
  rewrite decompose_zIMPL with (isL:=isL)(isR:=isR)...
  destruct H2.
  apply zIMPL_sIMPL...
  rewrite decompose_zIMPL with (isL:=isL)(isR:=isR)...
  rewrite decompose_is_rewrite in H.
  destruct H.
  generalize (replace_inzvars_correct (fst is) (x::nil));intro.
  generalize (replace_inzvars_correct (snd is) (y::nil)) ;intro.
  generalize (decompose_replace_inzvars _ _ _ (x::nil) H);intro.
  generalize (decompose_replace_inzvars _ _ _ (y::nil) H3);intro.
  intros rho H8.
  rewrite fst_replace_isnzvars,snd_replace_isnzvars in *.
  remember (decompose rho) as d.
  destruct d as [rhoL rhoR]. symmetry in Heqd.
  generalize (decompose_ies_eval_correct2 _ _ _ _ _ _ _ H4 H6 Heqd);intro.
  rewrite replace_inzvars_reduce in H9.
  assert (rho |= replace_inzvars (fst is) nil)
   by (apply replace_inzvars_eval_nil in H8;trivial).
  spec H9 H10.
  assert (nSAT (ies2ses (fst is))).
   destruct H10 as [rho' H10].
   rewrite replace_inzvars_ies2ses,replace_inzvars_exvars in H10.
   exists ([impl_exvars (fst is) => rho']rho)...
  apply H9 in H8.
  spec H0 rho.
  rewrite replace_isnzvars_eval in H0.
  spec H0 H10.
  assert (rhoL |= replace_inzvars (snd isL) (y :: nil) \/
          rhoR |= replace_inzvars (snd isR) (y :: nil)).
   destruct H8. left.
   spec H1 rhoL. rewrite replace_isnzvars_eval in H1.
   apply H1... right.
   spec H2 rhoR. rewrite replace_isnzvars_eval in H2.
   apply H2...
  rewrite<- decompose_ies_eval_correct2 with (ctx:=rho)in H12...
  apply H12. apply replace_inzvars_correct.
  apply decompose_replace_inzvars...
  rewrite replace_inzvars_reduce...
 Qed.

 Lemma decompose_sIMPL_full: forall is isL isR x y,
  decompose is = (isL,isR) ->
  nIMPL is ->
  (sIMPL is x y <-> (sIMPL isL x y \/ zIMPL isR y) /\ (zIMPL isL y \/ sIMPL isR x y)).
 Proof with try tauto.
  intros.
  split;intros.
  apply decompose_sIMPL_1 with (is:=is)...
  destruct H1.
  apply decompose_sIMPL_2 with isL isR...
 Qed.

 Lemma decompose_sIMPL: forall is isL isR x y,
  decompose is = (isL,isR) ->
  nIMPL is ->
  ~zIMPL is y ->
  (sIMPL is x y <-> sIMPL isL x y /\ sIMPL isR x y).
 Proof with try tauto.
  intros.
  rewrite decompose_sIMPL_full with (isL:=isL) (isR:=isR)...
  assert (~zIMPL isL y /\ ~zIMPL isR y).
   rewrite<- neg_or.
   intro. apply H1. 
   rewrite decompose_zIMPL with (isL:=isL) (isR:=isR)...
  tauto.
 Qed.


(*Section for height correctness. Should be moved later*)


Lemma cheight_app: forall {A B} `{cheightable A B} (l1 l2 : list B) ctx,
 cheight ctx (l1++l2) = max (cheight ctx l1) (cheight ctx l2).
Proof with try tauto.
 induction l1;intros.
 simpl...
 spec IHl1 l2 ctx.
 simpl in *. unfold list_cheight in *. simpl in *.
 rewrite IHl1. apply Max.max_assoc.
Qed.

 Instance eval_equiv_prop_ies : eval_equiv_prop impl_equation_system.
 Proof with try tauto.
 constructor. repeat intro.
 split;intro.
 destruct H0 as [rho H0].
 exists rho. eapply eval_equiv... Focus 2. apply H0.
 repeat intro.
 destruct (in_dec eq_dec v (impl_exvars a)).
 repeat rewrite override_in...
 repeat rewrite override_not_in...
 symmetry. apply H.
 clear - H1. unfold ies2ses in H1.
 destruct a as [l1 l2 l3 l4]. simpl in *.
 repeat rewrite in_app_iff in *...
 destruct H0 as [rho H0].
 exists rho. eapply eval_equiv... Focus 2. apply H0.
 repeat intro.
 destruct (in_dec eq_dec v (impl_exvars a)).
 repeat rewrite override_in...
 repeat rewrite override_not_in...
 apply H.
 clear - H1. unfold ies2ses in H1.
 destruct a as [l1 l2 l3 l4]. simpl in *.
 repeat rewrite in_app_iff in *...
Qed.

Definition SAT_h {A B} `{evalable A B} `{varsable B var} `{cheightable A (list var)} :=
 fun (b : B) (h : nat) => exists (a : A), a |= b /\ cheight a (vars b) = h.
Definition SAT_zero {A B} `{evalable A B} `{varsable B var} `{cheightable A (list var)} :=
 fun (b : B) => SAT_h b 0.
Definition nSAT_zero (ses : sat_equation_system): Prop :=
 SAT_zero (replace_snzvars ses nil).
Definition sSAT_zero (ses : sat_equation_system) (x  : var): Prop :=
 SAT_zero (replace_snzvars ses (x::nil)).
Definition IMPL_zero (is : impl_system): Prop :=
 forall rho, cheight rho (vars is) = 0 ->
 (exists rho', cheight rho' (impl_exvars (fst is)) = 0 /\ 
 [impl_exvars (fst is) => rho']rho |= ies2ses (fst is)) ->
 (exists rho'', cheight rho'' (impl_exvars (snd is)) = 0 /\
 [impl_exvars (snd is) => rho'']rho |= ies2ses (snd is)).
Definition nIMPL_zero (is : impl_system): Prop :=
 IMPL_zero (replace_isnzvars is nil nil).
Definition zIMPL_zero (is : impl_system) x: Prop :=
 IMPL_zero (replace_isnzvars is nil (x::nil)).
Definition sIMPL_zero (is : impl_system) x y: Prop :=
 IMPL_zero (replace_isnzvars is (x::nil) (y::nil)).

Lemma nSAT_zero_eval: forall ses,
 |ses| = 0 ->
 (nSAT ses <-> nSAT_zero ses).
Proof with try tauto.
 intros. split;intro. Focus 2.
 destruct H0 as [ctx [H0 _]].
 exists ctx...
 destruct H0 as [ctx H0].
 remember (cheight ctx (vars (replace_snzvars ses nil))) as n.
 assert (le (cheight ctx (vars (replace_snzvars ses nil))) n) by omega.
 clear Heqn.
 rewrite<- replace_snzvars_height with (l:=nil) in H.
 revert H0 H H1.
 revert ctx ses. induction n;intros.
 exists ctx. split... inv H1...
 
 remember (decompose ctx) as d.
 destruct d as [ctxL ctxR]. symmetry in Heqd.
 assert (sat_nzvars (replace_snzvars ses nil) = nil) by apply replace_snzvars_correct.
 generalize (height_zero _ H);intro.
 generalize (decompose_ses_eval_nil _ _ _ _ _ _ H2 H3 Heqd);intro.
 apply H4 in H0.
 destruct H0.
 destruct (ctx_decompose_decrease _ _ _ _ _ Heqd H1).
 spec IHn ctxL ses H0 H H6. apply IHn.
Qed.

Lemma sSAT_zero_eval: forall ses x,
 |ses| = 0 ->
 (sSAT ses x <-> sSAT_zero ses x).
Proof with try tauto.
 intros. split;intros. Focus 2.
 destruct H0 as [ctx [H0 _]]. exists ctx...
 destruct H0 as [ctx H0].
 remember (cheight ctx (vars (replace_snzvars ses (x::nil)))) as n.
 assert (le (cheight ctx (vars (replace_snzvars ses (x::nil)))) n) by omega.
 clear Heqn.
 rewrite<- replace_snzvars_height with (l:=x::nil) in H.
 revert H0 H H1.
 revert ctx ses. induction n;intros.
 exists ctx. split... inv H1...
 
 remember (decompose ctx) as d.
 destruct d as [ctxL ctxR]. symmetry in Heqd.
 generalize (height_zero _ H);intro.
 assert (sat_nzvars (replace_snzvars ses (x::nil)) = x::nil) by apply replace_snzvars_correct.
 generalize (decompose_ses_eval_single _ _ _ _ _ _ _ H3 H2 Heqd);intro.
 destruct (ctx_decompose_decrease _ _ _ _ _ Heqd H1).
 rewrite H4 in H0.
 destruct H0 as [H0|H0].
 spec IHn ctxL ses. apply IHn...
 spec IHn ctxR ses. apply IHn...
 clear - H0. rewrite replace_snzvars_nil_eval in H0...
Qed.

Lemma ies_zero_eval1: forall (ies : impl_equation_system) rho,
 |ies| = 0 ->
 impl_nzvars ies = nil ->
 rho |= ies ->
 cheight rho (vars ies) = 0 ->
 exists rho', cheight rho' (impl_exvars ies) = 0 /\ 
 [(impl_exvars ies)=> rho'] rho |= ies2ses ies.
Proof with try tauto.
 intros.
 destruct H1 as [rho' H1].
 remember (cheight rho' (impl_exvars ies)) as n. symmetry in Heqn.
 assert (le (cheight rho' (impl_exvars ies)) n) by omega. clear Heqn.
 revert H3 H1. revert rho'.
 induction n;intros.
 assert (cheight rho' (impl_exvars ies) = 0) by omega.
 exists rho'...
 remember (decompose rho) as d.
 destruct d as [rhoL rhoR]. symmetry in Heqd.
 remember (decompose rho') as d'.
 destruct d' as [rhoL' rhoR']. symmetry in Heqd'.
 apply IHn with rhoL'.
 destruct (ctx_decompose_decrease _ _ _ _ _ Heqd' H3)...
 replace (|ies|) with (|ies2ses ies|) in H by tauto.
 apply height_zero in H.
 generalize (decompose_override _ _ _ _ _ _ (impl_exvars ies) Heqd Heqd');intro.
 rewrite ies2ses_nzvars in H0.
 generalize (decompose_ses_eval_nil _ _ _ _ _ _ H0 H H4);intro.
 apply H5 in H1.
 destruct H1 as [H1 _].
 eapply eval_equiv. Focus 2. apply H1.
 repeat intro.
 destruct (in_dec eq_dec v (impl_exvars ies)).
 repeat rewrite override_in...
 repeat rewrite override_not_in...
 apply decompose_context_eval with (v:=v) in Heqd.
 assert (le (cheight rho (vars ies)) 0) by omega.
 rewrite cheight_leq_rewrite in H7.
 spec H7 v. detach H7.
 assert (|rho v| = 0) by omega.
 destruct (Share.decompose_height_zero _ _ _ Heqd H8).
 rewrite H9...
 clear - H6. destruct ies as [l1 l2 l3 l4].
 simpl in *. repeat rewrite in_app_iff in *...
Qed.

Lemma ies_zero_eval2: forall (ies : impl_equation_system) rho x,
 |ies| = 0 ->
 impl_nzvars ies = x::nil ->
 rho |= ies ->
 cheight rho (vars ies) = 0 ->
 exists rho', cheight rho' (impl_exvars ies) = 0 /\ 
 [(impl_exvars ies)=> rho'] rho |= ies2ses ies.
Proof with try tauto.
 intros.
 destruct H1 as [rho' H1].
 remember (cheight rho' (impl_exvars ies)) as n. symmetry in Heqn.
 assert (le (cheight rho' (impl_exvars ies)) n) by omega. clear Heqn.
 revert H3 H1. revert rho'.
 induction n;intros.
 assert (cheight rho' (impl_exvars ies) = 0) by omega.
 exists rho'...
 remember (decompose rho) as d.
 destruct d as [rhoL rhoR]. symmetry in Heqd.
 remember (decompose rho') as d'.
 destruct d' as [rhoL' rhoR']. symmetry in Heqd'.
 destruct (ctx_decompose_decrease _ _ _ _ _ Heqd' H3)...
 replace (|ies|) with (|ies2ses ies|) in H by tauto.
 apply height_zero in H.
 generalize (decompose_override _ _ _ _ _ _ (impl_exvars ies) Heqd Heqd');intro.
 rewrite ies2ses_nzvars in H0.
 generalize (decompose_ses_eval_single _ _ _ _ _ _ _ H0 H H6);intro.
 detach H7. apply H7 in H1.
 destruct H1.
 
 apply IHn with rhoL'...
 eapply eval_equiv. Focus 2. apply H1.
 repeat intro.
 destruct (in_dec eq_dec v (impl_exvars ies)).
 repeat rewrite override_in...
 repeat rewrite override_not_in...
 apply decompose_context_eval with (v:=v) in Heqd.
 assert (le (cheight rho (vars ies)) 0) by omega.
 rewrite cheight_leq_rewrite in H9.
 spec H9 v. detach H9.
 assert (|rho v| = 0) by omega.
 destruct (Share.decompose_height_zero _ _ _ Heqd H10).
 rewrite H11...
 clear - H8. destruct ies as [l1 l2 l3 l4].
 simpl in *. repeat rewrite in_app_iff in *...

 apply IHn with rhoR'...
 eapply eval_equiv. Focus 2. apply H1.
 repeat intro.
 destruct (in_dec eq_dec v (impl_exvars ies)).
 repeat rewrite override_in...
 repeat rewrite override_not_in...
 apply decompose_context_eval with (v:=v) in Heqd.
 assert (le (cheight rho (vars ies)) 0) by omega.
 rewrite cheight_leq_rewrite in H9.
 spec H9 v. detach H9.
 assert (|rho v| = 0) by omega.
 destruct (Share.decompose_height_zero _ _ _ Heqd H10).
 rewrite H12...
 clear - H8. destruct ies as [l1 l2 l3 l4].
 simpl in *. repeat rewrite in_app_iff in *...

 rewrite replace_snzvars_nil_eval in H1...
Qed.

Lemma nIMPL_zero_eval1: forall  (is:impl_system),
 |is| = 0 ->
 nIMPL is -> nIMPL_zero is.
Proof with try tauto.
 repeat intro.
 destruct H2 as [rho' [H2 H3]].
 spec H0 rho.
 rewrite replace_isnzvars_eval in H0.
 destruct is as [ies1 ies2].
 rewrite height_is_rewrite in H.
 rewrite max_zero in H. destruct H.
 rewrite fst_replace_isnzvars,snd_replace_isnzvars in *.
 unfold fst,snd in *.
 rewrite replace_inzvars_exvars in *.
 generalize (height_zero ies2 H4);intro.
 detach H0.
 destruct H0 as [ctx H0].
 rewrite replace_inzvars_exvars in *. Focus 2. exists rho'...
 assert (impl_exvars ies2 = impl_exvars (replace_inzvars ies2 nil)) by tauto.
 rewrite H6. apply ies_zero_eval1...
 exists ctx...
 rewrite vars_replace_isnzvars in *.
 rewrite cheight_app in H1.
 rewrite max_zero in H1...
Qed.

Lemma nIMPL_zero_eval2: forall  (is:impl_system),
 |is| = 0 ->
 nIMPL_zero is -> nIMPL is.
Proof with try tauto.
 intros. intros rho.
 rewrite<-replace_isnzvars_height with (l:=nil) (l':= nil) in H.
 destruct is as [ies1 ies2].
 unfold replace_isnzvars in H.
 rewrite height_is_rewrite in H.
 rewrite max_zero in H. destruct H.
 remember (cheight rho (vars (replace_isnzvars (ies1,ies2) nil nil))) as n.
 assert (le (cheight rho (vars (replace_isnzvars (ies1, ies2) nil nil))) n) by omega.
 clear Heqn.
 revert H2. revert rho.

 induction n;intros;rewrite replace_isnzvars_eval;intros;
 unfold fst,snd in *.
 spec H0 rho.
 assert (cheight rho (vars (replace_isnzvars (ies1, ies2) nil nil)) = 0) by omega;clear H2.
 rewrite fst_replace_isnzvars,snd_replace_isnzvars in *.
 unfold fst,snd in *. 
 repeat detach H0...
 destruct H0 as [rho'' [H5 H6]].
 exists rho''...
 apply ies_zero_eval1...
 rewrite vars_replace_isnzvars in H4.
 rewrite cheight_app in H4.
 rewrite max_zero in H4...

 remember (decompose rho) as d.
 destruct d as [rhoL rhoR]. symmetry in Heqd.
 generalize (height_zero _ H);intro.
 generalize (height_zero _ H1);intro.
 assert (rhoL |= replace_inzvars ies1 nil /\ rhoR |= replace_inzvars ies1 nil).
  apply decompose_ies_eval_correct1 with (ctx:=rho) (ies := replace_inzvars ies1 nil)... 
 destruct H6.
 generalize (ctx_decompose_decrease _ _ _ _ _ Heqd H2);intro.
 destruct H8.
 generalize (IHn rhoL H8 H6);intro.
 generalize (IHn rhoR H9 H7);intro.
 rewrite snd_replace_isnzvars in *.
 unfold snd in *.
 assert (impl_nzvars (replace_inzvars ies2 nil) = nil) by tauto.
 generalize (decompose_ies_eval_correct1 _ _ _ _ _ _ H12 H5 Heqd);intro.
 apply H13...
Qed.

Lemma nIMPL_zero_eval: forall  (is:impl_system),
 |is| = 0 ->
 (nIMPL is <-> nIMPL_zero is).
Proof with try tauto.
 intros. split;intros.
 apply nIMPL_zero_eval1...
 apply nIMPL_zero_eval2...
Qed.

Lemma zIMPL_zero_eval1: forall  (is:impl_system) x,
 |is| = 0 ->
 zIMPL is x -> zIMPL_zero is x.
Proof with try tauto.
 repeat intro.
 destruct H2 as [rho' [H2 H3]].
 spec H0 rho.
 rewrite replace_isnzvars_eval in H0.
 destruct is as [ies1 ies2].
 rewrite height_is_rewrite in H.
 rewrite max_zero in H. destruct H.
 rewrite fst_replace_isnzvars,snd_replace_isnzvars in *.
 unfold fst,snd in *.
 rewrite replace_inzvars_exvars in *.
 generalize (height_zero ies2 H4);intro.
 detach H0.
 destruct H0 as [ctx H0].
 rewrite replace_inzvars_exvars in *. Focus 2. exists rho'...
 assert (impl_exvars ies2 = impl_exvars (replace_inzvars ies2 (x::nil))) by tauto.
 rewrite H6.
 apply ies_zero_eval2 with x...
 exists ctx...
 rewrite vars_replace_isnzvars in H1.
 rewrite cheight_app in H1.
 rewrite max_zero in H1...
Qed.

Lemma zIMPL_zero_eval2: forall  (is:impl_system) x,
 |is| = 0 ->
 zIMPL_zero is x -> zIMPL is x.
Proof with try tauto.
 intros. intros rho.
 rewrite<-replace_isnzvars_height with (l:=nil) (l':= x::nil) in H.
 destruct is as [ies1 ies2].
 unfold replace_isnzvars in H.
 rewrite height_is_rewrite in H.
 rewrite max_zero in H. destruct H.
 remember (cheight rho (vars (replace_isnzvars (ies1,ies2) nil (x::nil)))) as n.
 assert (le (cheight rho (vars (replace_isnzvars (ies1, ies2) nil (x :: nil)))) n) by omega.
 clear Heqn.
 revert H2. revert rho.

 induction n;intros;rewrite replace_isnzvars_eval;intros;
 unfold fst,snd in *.
 spec H0 rho.
 assert (cheight rho (vars (replace_isnzvars (ies1, ies2) nil (x :: nil))) = 0) by omega;clear H2.
 rewrite fst_replace_isnzvars,snd_replace_isnzvars in *.
 unfold fst,snd in *. 
 repeat detach H0...
 destruct H0 as [rho'' [H5 H6]].
 exists rho''... 
 apply ies_zero_eval1...
 rewrite vars_replace_isnzvars in H4.
 rewrite cheight_app in H4.
 rewrite max_zero in H4...

 remember (decompose rho) as d.
 destruct d as [rhoL rhoR]. symmetry in Heqd.
 generalize (height_zero _ H);intro.
 generalize (height_zero _ H1);intro.
 assert (rhoL |= replace_inzvars ies1 nil /\ rhoR |= replace_inzvars ies1 nil).
  apply decompose_ies_eval_correct1 with (ctx:=rho) (ies := replace_inzvars ies1 nil)... 
 destruct H6.
 generalize (ctx_decompose_decrease _ _ _ _ _ Heqd H2);intro.
 destruct H8.
 generalize (IHn rhoL H8 H6);intro.
 generalize (IHn rhoR H9 H7);intro.
 rewrite snd_replace_isnzvars in *.
 unfold snd in *.
 assert (rho |= replace_inzvars ies2 nil).
  apply replace_inzvars_eval_nil with (l:=x::nil) in H10.
  apply replace_inzvars_eval_nil with (l:=x::nil) in H11.
  assert (impl_nzvars (replace_inzvars ies2 nil) = nil) by apply replace_inzvars_correct.
  rewrite <-replace_inzvars_height with (l:= nil) in H1.
  rewrite replace_inzvars_reduce in H1.
  apply height_zero in H1.
  generalize (decompose_ies_eval_correct1 _ _ _ _ _ _ H12 H1 Heqd);intro.
  apply H13...
 assert (impl_nzvars (replace_inzvars ies2 (x::nil)) = x::nil) by tauto.
 generalize (decompose_ies_eval_correct2 _ _ _ _ _ _ _ H13 H5 Heqd H12);intro.
 apply H14...
Qed.

Lemma zIMPL_zero_eval: forall (is:impl_system) x,
 |is| = 0 ->
 (zIMPL is x <-> zIMPL_zero is x).
Proof with try tauto.
 intros. split;intros.
 apply zIMPL_zero_eval1...
 apply zIMPL_zero_eval2...
Qed.

Lemma sIMPL_zero_eval1: forall (is:impl_system) x y,
 |is| = 0 ->
 sIMPL is x y -> sIMPL_zero is x y.
Proof with try tauto.
 repeat intro.
 destruct H2 as [rho' [H2 H3]].
 spec H0 rho.
 rewrite replace_isnzvars_eval in H0.
 destruct is as [ies1 ies2].
 rewrite height_is_rewrite in H.
 rewrite max_zero in H. destruct H.
 rewrite fst_replace_isnzvars,snd_replace_isnzvars in *.
 unfold fst,snd in *.
 rewrite replace_inzvars_exvars in *.
 generalize (height_zero ies2 H4);intro.
 detach H0. Focus 2. exists rho'...
 assert (impl_exvars ies2 = impl_exvars (replace_inzvars ies2 (y::nil))) by tauto.
 rewrite H6.
 apply ies_zero_eval2 with y...
 rewrite vars_replace_isnzvars in H1.
 rewrite cheight_app in H1.
 rewrite max_zero in H1...
Qed.

Lemma sIMPL_zero_eval2: forall (is:impl_system) x y,
 |is| = 0 ->
 nIMPL is ->
 sIMPL_zero is x y-> sIMPL is x y.
Proof with try tauto.
 intros. intros rho.
 rewrite<-replace_isnzvars_height with (l:=x::nil) (l':= y::nil) in H.
 destruct is as [ies1 ies2].
 unfold replace_isnzvars in H.
 rewrite height_is_rewrite in H.
 rewrite max_zero in H. destruct H.
 remember (cheight rho (vars (replace_isnzvars (ies1,ies2) (x::nil)(y::nil)))) as n.
 assert (le (cheight rho (vars (replace_isnzvars (ies1, ies2) (x :: nil) (y::nil)))) n) by omega.
 clear Heqn.
 revert H3. revert rho.

 induction n;intros;rewrite replace_isnzvars_eval;intros;
 unfold fst,snd in *.
 spec H1 rho.
 assert (cheight rho (vars (replace_isnzvars (ies1, ies2)(x :: nil)(y::nil))) = 0) by omega;clear H3.
 rewrite fst_replace_isnzvars,snd_replace_isnzvars in *.
 unfold fst,snd in *. 
 repeat detach H1...
 destruct H1 as [rho'' [H6 H7]].
 exists rho''...
 apply ies_zero_eval2 with x...
 rewrite vars_replace_isnzvars in H5.
 rewrite cheight_app in H5.
 rewrite max_zero in H5...

 remember (decompose rho) as d.
 destruct d as [rhoL rhoR]. symmetry in Heqd.
 assert (rho |= replace_inzvars ies2 nil).
  apply H0. apply replace_inzvars_eval_nil with (l:=x::nil)...
 generalize (height_zero _ H);intro.
 generalize (height_zero _ H2);intro.
 assert (rhoL |= replace_inzvars ies1 (x::nil) \/ rhoR |= replace_inzvars ies1 (x::nil)).
  eapply decompose_ies_eval_correct2 with (ies:= replace_inzvars ies1 (x::nil)) (ctx:=rho)...
  rewrite replace_inzvars_reduce.
  apply replace_inzvars_eval_nil with (l:=x::nil)...
 destruct (ctx_decompose_decrease _ _ _ _ _ Heqd H3).
 assert (rhoL |= replace_inzvars ies2 (y::nil) \/ rhoR |= replace_inzvars ies2 (y::nil)).
  destruct H8.
  left;apply IHn... right;apply IHn...
 assert (impl_nzvars (replace_inzvars ies2 (y::nil)) = y::nil) by apply replace_inzvars_correct.
 generalize (decompose_ies_eval_correct2 _ _ _ _ _ _ _ H12 H7 Heqd H5);intro.
 apply H13...
Qed.

Lemma sIMPL_zero_eval: forall is x y,
 |is| = 0 ->
 nIMPL is ->
 (sIMPL is x y <-> sIMPL_zero is x y).
Proof with try tauto.
 intros. split;intros.
 apply sIMPL_zero_eval1...
 apply sIMPL_zero_eval2...
Qed.
 

End Decompose_Base.

(*

Module SAT_Decompose_Base (sv : SV)
                          (Import es : EQUATION_SYSTEM sv with Definition s := share)
                          (Import esf : SHARE_ES_FEATURES sv es).

 Module DB := Decompose_Base sv es esf.
 Import DB.    
 


End SAT_Decompose_Base.

Module IMPL_Decompose_Base (sv : SV)
                           (Import es : EQUATION_SYSTEM sv with Definition s := share)
                           (Import esf : SHARE_ES_FEATURES sv es).
(*
 Module SDB := SAT_Decompose_Base sv es esf.
 Import SDB.
*)
 Import ClassicalProps.
 Module IB := IMPL_Base sv es esf.
 Import IB.
 Module IC := IMPL_Correctness sv es esf.
 Import IC.

End IMPL_Decompose_Base.
*)  