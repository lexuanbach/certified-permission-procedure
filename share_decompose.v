Require Import msl.msl_standard.
Require Import NPeano.
Require Import share_dec_base.
Require Import base_properties.
Require Import share_equation_system.
Require Import share_dec_interface.
Require Import share_decompose_base.
Require Import share_correctness.

Module SAT_Decompose (sv : SV)
                     (Import es : EQUATION_SYSTEM sv with Module dom := Share_Domain)
                     (Import esf : SYSTEM_FEATURES sv es) <:
                     SAT_DECOMPOSE sv es esf.

 Module DB := Decompose_Base sv es esf.
 Import DB.

 Function SATdecompose (ses : sat_equation_system) {measure height ses} :=
  if is_height_zero ses then (ses::nil) else
   let (sesL,sesR) := decompose ses in 
   (SATdecompose sesL)++(SATdecompose sesR).
 Proof with try tauto;try omega.
  repeat intro.
  apply height_nonzero in teq0.
  detach teq0...
  repeat intro.
  apply height_nonzero in teq0.
  detach teq0...
 Defined.

 Lemma SAT_decompose_not_nil: forall ses,
  SATdecompose ses <> nil.
 Proof with try tauto.
  do 1 intro.
  apply SATdecompose_ind; repeat intro. inv H.
  apply app_eq_nil in H1...
 Qed.
  
 Lemma SAT_decompose_height: forall ses ses',
  In ses' (SATdecompose ses) -> |ses'| = 0 .
 Proof with try tauto.
  do 1 intro.
  apply SATdecompose_ind . repeat intro.
  simpl in H. destruct H... subst...
  repeat intros.
  apply in_app_or in H1.
  destruct H1.
  apply H... apply H0...
 Qed.

 Lemma nSAT_decompose_eval: forall ses,
  nSAT ses <-> forall ses', In ses' (SATdecompose ses) -> nSAT ses'.
 Proof with try tauto.
  do 1 intro.
  apply SATdecompose_ind;repeat intros.
  split;intros.
  destruct H0...
  subst ses'...
  apply H. left...
  apply decompose_nSAT in e0.
  split;intros.
  rewrite in_app_iff in H2. destruct H2.
  apply H... apply H0...
  apply e0. split.
  apply H... intros. apply H1. rewrite in_app_iff...
  apply H0... intros. apply H1. rewrite in_app_iff...
 Qed. 

 Lemma sSAT_decompose_eval: forall ses x,
  nSAT ses ->
  (sSAT ses x <-> (exists ses', In ses' (SATdecompose ses) /\ sSAT ses' x)).
 Proof with try tauto.
  do 2 intro.
  apply SATdecompose_ind;intros.
  split;intros.
  exists ses0. split... left...
  destruct H0 as [? [? ?]]... 
  destruct H0... subst x0...
  generalize (decompose_sSAT _ _ _ x H1 e0);intro.
  rewrite H2.
  generalize (decompose_nSAT _ _ _ e0);intro.
  rewrite H3 in H1. destruct H1.
  spec H H1. spec H0 H4.
  split;intros.
  destruct H5.
  apply H in H5. destruct H5.
  exists x0. rewrite in_app_iff...
  apply H0 in H5. destruct H5.
  exists x0. rewrite in_app_iff...
  destruct H5 as [? [? ?]].
  rewrite in_app_iff in H5.
  destruct H5.
  left. apply H. exists x0...
  right. apply H0. exists x0...
 Qed.

End SAT_Decompose.

Module IMPL_Decompose (sv : SV)
                      (Import es : EQUATION_SYSTEM sv with Module dom := Share_Domain)
                      (Import esf : SYSTEM_FEATURES sv es) <:
                       IMPL_DECOMPOSE sv es esf.

 Module DB := Decompose_Base sv es esf.
 Import DB.
 Import ClassicalProps.

 Function IMPLdecompose (is : impl_system) {measure height is} :=
  if is_height_zero is then (is::nil) else
   let (isL,isR) := decompose is in
   (IMPLdecompose isL)++(IMPLdecompose isR).
 Proof with try tauto;try omega.
  repeat intro.
  apply height_nonzero in teq0.
  detach teq0...
  repeat intro.
  apply height_nonzero in teq0.
  detach teq0...
 Defined.

 Lemma IMPL_decompose_not_nil: forall is,
  IMPLdecompose is <> nil.
 Proof with try tauto.
  do 1 intro.
  apply IMPLdecompose_ind; repeat intro. inv H.
  apply app_eq_nil in H1...
 Qed.

 Lemma IMPL_decompose_height : forall (is is':impl_system),
  In is' (IMPLdecompose is) -> 
  |is'| = 0.
 Proof with try tauto.
  do 1 intro.
  apply IMPLdecompose_ind;intros.
  simpl in H. destruct H... subst...
  rewrite in_app_iff in H1. destruct H1.
  apply H... apply H0...
 Qed.

 Lemma nIMPL_decompose_eval: forall (is:impl_system),
  nSAT (ies2ses (fst is)) ->
  (nIMPL is <-> forall (is':impl_system), In is' (IMPLdecompose is) -> nIMPL is').
 Proof with try tauto.
  do 1 intro.
  apply IMPLdecompose_ind ;intros.
  split;intros.
  destruct H1... subst...
  apply H0. left...

  assert (nSAT (ies2ses (fst isL)) /\ nSAT (ies2ses (fst isR))).
   rewrite<- decompose_nSAT with (ses:=ies2ses (fst is0))...
   rewrite decompose_is_rewrite in e0.
   destruct e0 as [H2 _].
   clear - H2.
   destruct (fst is0) as [l1 l2 l3 l4].
   destruct (fst isL) as [l1L l2L l3L l4L].
   destruct (fst isR) as [l1R l2R l3R l4R].
   simpl in *. 
   unfold decompose_ses,decompose_ies,ies2ses in *;simpl in *.
   simpl.
   destruct (decompose_list l3).
   destruct (decompose_list l4).
   inv H2... 
  destruct H2.
  apply H in H2.
  apply H0 in H3.
  rewrite decompose_nIMPL with (isL:=isL)(isR:=isR)...
  split;intros.
  rewrite in_app_iff in H5.
  destruct H5. apply H2... apply H3...
  split. apply H2. intros. apply H4.
  rewrite in_app_iff...
  apply H3. intros. apply H4.
  rewrite in_app_iff...
 Qed.

 Lemma zIMPL_decompose_eval: forall (is:impl_system) y,
  nSAT (ies2ses (fst is)) ->
  nIMPL is  ->
  (zIMPL is y <-> exists (is':impl_system), In is' (IMPLdecompose is) /\ zIMPL is' y).
 Proof with try tauto.
  do 1 intro.
  apply IMPLdecompose_ind ;intros.
  split;intros.
  exists is0.
  split... left...
  destruct H1 as [is'[H1 H2]].
  destruct H1...
  subst is'...

  assert (nSAT (ies2ses (fst isL)) /\ nSAT (ies2ses (fst isR))).
   rewrite<- decompose_nSAT with (ses:=ies2ses (fst is0))...
   rewrite decompose_is_rewrite in e0.
   destruct e0 as [H3 _].
   clear - H3.
   destruct (fst is0) as [l1 l2 l3 l4].
   destruct (fst isL) as [l1L l2L l3L l4L].
   destruct (fst isR) as [l1R l2R l3R l4R].
   simpl in *. 
   unfold decompose_ses,decompose_ies,ies2ses in *;simpl in *.
   destruct (decompose_list l3).
   destruct (decompose_list l4).
   inv H3...
  destruct H3.
  assert (nIMPL isL /\ nIMPL isR).
   rewrite<- decompose_nIMPL with (is:=is0)...
  destruct H5.
  spec H y H3 H5.
  spec H0 y H4 H6.
  rewrite decompose_zIMPL with (isL:=isL)(isR:=isR)...
  split;intros.
  destruct H7. 
  apply H in H7. destruct H7 as [is' H7].
  exists is'. rewrite in_app_iff...
  apply H0 in H7. destruct H7 as [is' H7].
  exists is'. rewrite in_app_iff...
  destruct H7 as [is' [H7 H8]].
  rewrite in_app_iff in H7.
  destruct H7.
  left. apply H. exists is'...
  right. apply H0. exists is'...
 Qed.

 Lemma sIMPL_decompose_eval: forall (is:impl_system) x y,
  nSAT (ies2ses (fst is)) ->
  nIMPL is ->
  ~zIMPL is y ->
  (sIMPL is x y <-> forall (is':impl_system), In is' (IMPLdecompose is) -> sIMPL is' x y).
 Proof with try tauto.
  do 1 intro.
  apply IMPLdecompose_ind ;intros.
  split;intros.
  destruct H3...
  subst is'...
  apply H2... left...

  assert (nSAT (ies2ses (fst isL)) /\ nSAT (ies2ses (fst isR))).
   rewrite<- decompose_nSAT with (ses:=ies2ses (fst is0))...
   rewrite decompose_is_rewrite in e0.
   destruct e0 as [H4 _].
   clear - H4.
   destruct (fst is0) as [l1 l2 l3 l4].
   destruct (fst isL) as [l1L l2L l3L l4L].
   destruct (fst isR) as [l1R l2R l3R l4R].
   simpl in *. 
   unfold decompose_ses,decompose_ies,ies2ses in *;simpl in *.
   destruct (decompose_list l3).
   destruct (decompose_list l4).
   inv H4...
  destruct H4.
  assert (nIMPL isL /\ nIMPL isR).
   rewrite<- decompose_nIMPL with (is:=is0)...
  destruct H6.
  assert (~zIMPL isL y /\ ~zIMPL isR y).
   rewrite<-neg_or.
   rewrite<- decompose_zIMPL with (is:=is0)...
  destruct H8.
  spec H x y H4 H6 H8.
  spec H0 x y H5 H7 H9.
  rewrite decompose_sIMPL with (isL:=isL)(isR:=isR)...
  split;intros.
  rewrite in_app_iff in H11.
  destruct H11. apply H... apply H0...
  split. apply H. intros. apply H10. rewrite in_app_iff...
  apply H0. intros. apply H10. rewrite in_app_iff...
 Qed.

End IMPL_Decompose.
