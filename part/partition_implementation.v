Add LoadPath "..".
Require Import base.
Require Import Orders.
Require Import List.
Require Import Omega.
Require Import uf.UF_interface.
Require Import partition_interface.
Require Import partition_base.
Require Import partition_ibase.

Open Scope part_scope.

Module Partition (Import Input : INPUT) 
                 (Import ot : OrderedType with Definition t := Input.e
                                          with Definition eq := @Logic.eq Input.e)
                 (Import pi : PARTITION_INPUT with Definition var := ot.t)
                 <: PARTITION pi.

  Module IS := Internal_Structures Input ot.
  Import IS.

  Definition partition (l : list equation) : list (list equation) :=
   let (l,rbt) := eqnlist2RBT l (eqnlist2uf l) in
    l::(remove_1st (RBT.elements rbt)).

  Lemma partition_sublist : forall (l : list equation),
   forall l', In l' (partition l) -> sublist l' l.
  Proof. 
   intros.
   unfold partition in H. 
   generalize (eqnlist2uf_lcomponents_cond l);intro.
   apply UF_lcomponents_cond_prop3 in H0.
   remember (eqnlist2uf l) as uf.
   remember (eqnlist2RBT l uf) as p.
   icase p.
   apply eqnlist2RBT_rewrite in Heqp.
   destruct Heqp. subst l0 m.
   destruct H. subst l'.
   repeat intro. eapply list2RBT_spec3.
   apply H0. apply H.
   apply remove_1st_spec2 in H.
   destruct H. eapply list2RBT_spec2.
   apply H0. apply H.
  Qed.

  Lemma partition_exist : forall (l : list equation),
   forall e, In e l -> exists l', In l' (partition l) /\ In e l'.
  Proof.
   intros.
   unfold partition.
   generalize (eqnlist2uf_lcomponents_cond l);intro.
   apply UF_lcomponents_cond_prop3 in H0.
   remember (eqnlist2uf l) as uf.
   remember (eqnlist2RBT l uf) as p.
   icase p. apply eqnlist2RBT_rewrite in Heqp.
   destruct Heqp. subst l0 m.
   generalize (list_eq_dec e_eq_dec (vars e0) nil);intro.
   destruct H1.
   exists (eqnlist2RBT_l l uf).
   split. left;trivial.
   apply list2RBT_spec3;tauto.
   copy H.
   eapply UF_in_cond_prop2 in H;try apply H0.
   eapply find_var_v_spec1 in n;try apply H.
   destruct n.
   generalize (eqnlist2RBT_spec1 _ _ _ _ H0 H1 H2);intro.
   destruct H3 as [? [? ?]].
   exists x0. split;trivial.
   right. apply remove_1st_spec2.
   exists x;trivial.
  Qed.

  Lemma partition_disjoint : forall (l:list equation),
  disjoint_pwise (var_list_extract (partition l)).
  Proof.
   repeat intro.
   unfold partition in *.
   generalize (eqnlist2uf_lcomponents_cond l);intro.
   generalize (UF_lcomponents_cond_prop3 _ _ H3);intro.
   remember (eqnlist2uf l) as uf.
   remember (eqnlist2RBT l uf) as p.
   icase p. apply eqnlist2RBT_rewrite in Heqp.
   destruct Heqp;subst l1 m.
   destruct H2. simpl in *.
   assert (vars_list (eqnlist2RBT_l l uf) = vars (eqnlist2RBT_l l uf)) by trivial.
   rewrite H6 in H0;rewrite H6 in H1;clear H6.
   rewrite list2RBT_spec7 in H0;rewrite list2RBT_spec7 in H1;trivial.
   icase i;icase j;simpl in *.
   inv H0. inv H2.
   inv H1. inv H5.
   rewrite var_list_extract_nth_op in H0.
   rewrite var_list_extract_nth_op in H1.
   destruct H0 as [? [? ?]].
   destruct H1 as [? [? ?]].
   apply remove_1st_nth_op in H0.
   apply remove_1st_nth_op in H1.
   destruct H0. destruct H1.
   assert (In (x2,x0) (RBT.elements (eqnlist2RBT_rbt l uf))).
    apply nth_op_In. exists i;trivial.
   assert (In (x3,x1) (RBT.elements (eqnlist2RBT_rbt l uf))).
    apply nth_op_In. exists j;trivial.
   apply InA_Kvpeq_In in H8.
   apply InA_Kvpeq_In in H9.
   apply RBT.elements_spec1 in H8.
   apply RBT.elements_spec1 in H9.
   assert (x2 <> x3).
    eapply RBT_elements_diff. apply H0. apply H1. omega.
   subst l0 l'.
   eapply list2RBT_spec6 in H10. eapply H10. split.
   apply H2. apply H5. apply H3. apply H8. apply H9.
  Qed.

  Lemma partition_eval : forall (l : list equation) rho,
    rho |= l<-> forall l', In l' (partition l) -> rho |= l'.
  Proof.
   intros.
   split;intros.
   apply sublist_eval with l;trivial.
   apply partition_sublist;trivial.
   apply list_eval_rewrite. intros.
   apply partition_exist in H0.
   destruct H0 as [? [? ?]].
   spec H x H0.
   rewrite list_eval_rewrite in H.
   apply H;trivial.
  Qed.

End Partition.

Module Partition_Lemmas (Import pi : PARTITION_INPUT)
                        (Import partition : PARTITION pi).

  Lemma partition_nth_disjoint : forall l l1 l2 i j,
   nth_op i (partition l) = Some l1 ->
   nth_op j (partition l) = Some l2 ->
   i <> j -> disjoint (vars l1) (vars l2).
  Proof.
   intros.
   generalize (partition_disjoint l);intros.
   spec H2 (vars l1) (vars l2) i j H1.
   apply H2.
   apply var_list_extract_nth_op.
   exists l1. split;trivial.
   apply var_list_extract_nth_op.
   exists l2. split;trivial.
  Qed.

  Lemma partition_not_in : forall (l : list equation) l' eqn,
   In l' (partition l) -> In eqn l -> ~In eqn l' -> disjoint (vars eqn) (vars l').
  Proof.
   intros.
   generalize (partition_exist _ _ H0);intro.
   destruct H2 as [? [? ?]].
   apply nth_op_In in H.
   apply nth_op_In in H2.
   destruct H. destruct H2.
   generalize (eq_nat_dec x0 x1);intro.
   destruct H4. subst. rewrite H2 in H. inv H.
   elimtype False;apply H1;trivial.
   apply partition_nth_disjoint with (l:=l) (l1:=l') (l2:=x) in n;trivial.
   apply sublist_disjoint with (vars x).
   apply sublist_vars;trivial.
   apply disjoint_comm;trivial.
  Qed. 

End Partition_Lemmas.

Module Partition_SAT (Import Input : INPUT)
                     (Import ot : OrderedType with Definition t := Input.e 
                                              with Definition eq := @Logic.eq Input.e)
                     (Import pi : PARTITION_INPUT with Definition var := ot.t)<: 
                      PARTITION_SAT pi.

  Module Part := Partition Input ot pi.
  Import Part. 
  Module PL := Partition_Lemmas pi Part.
  Import PL.
  Definition partition_SAT := partition.  

  Definition SAT (l : list equation) : Prop := 
    exists rho, rho |= l.

  Fixpoint SATL (L : list (list equation)) (lctx : list context) : Prop :=
   match (L, lctx) with 
   | (nil,nil) => True
   | (leqn::l,ctx::l') => ctx |= leqn /\ SATL l l'
   | _ => False
   end.

  Lemma SATL_length_eq: forall (L : list (list equation)) (lctx : list context),
   SATL L lctx -> length L = length lctx.
  Proof.
   induction L;intros;
   icase lctx.
   destruct H.
   spec IHL lctx H0.
   simpl. omega.
  Qed. 

  Lemma SATL_split: forall L1 L2 lctx1 lctx2,
   length L1 = length lctx1 ->
   (SATL (L1++L2) (lctx1++lctx2) <-> SATL L1 lctx1 /\ SATL L2 lctx2).
  Proof.
   induction L1;intros.
   simpl. icase lctx1.
   simpl. tauto.
   icase lctx1.
   inv H.
   spec IHL1 L2 lctx1 lctx2 H1.
   simpl;tauto.
  Qed. 

  Lemma SATL_rewrite1 : forall (L : list (list equation)),
   (exists (lctx : list context), SATL L lctx) <-> forall l', In l' L -> SAT l'.
  Proof.
   induction L;split;intros.
   inversion H0.
   exists nil;simpl;trivial.
   destruct H as [lctx H].
   icase lctx.
   destruct H.
   destruct H0.
   subst. exists c. trivial.
   apply IHL;trivial.
   exists lctx. exact H1.

   copy H.
   spec H a.
   detach H.
   destruct H as [ctx H].
   assert (H1 : forall l', In l' L -> SAT l').
   intros.
   apply H0.
   right. exact H1.
   rewrite<- IHL in H1.
   destruct H1 as [lctx H1].
   exists (ctx::lctx).
   split;trivial.
   left;trivial.
  Qed.

  Lemma SATL_rewrite2: forall ( L : list (list equation)) (lctx : list context),
   SATL L lctx -> forall l, (In l L -> (exists ctx, In ctx lctx /\ ctx |= l)).
  Proof.
   induction L;intros.
   inversion H0.
   icase lctx.
   destruct H.
   destruct H0.
   subst. exists c.
   split;trivial.
   left;trivial.
   spec IHL lctx H1 l H0.
   destruct IHL as [ctx [H2 H3]].
   exists ctx.
   split;trivial.
   right;trivial.
  Qed.

  Lemma partition_SAT_correct1: forall l,
    SAT l -> forall l', In l' (partition_SAT l) -> SAT l'.
  Proof.
   intros.
   destruct H as [rho H].
   exists rho.
   rewrite partition_eval in H.
   apply H;trivial.
  Qed.

  Fixpoint upd_lctx (L : list (list var)) (lctx : list context) : context :=
   match (L,lctx) with
   |(lv::L',ctx::lctx')=> [lv=>ctx] (upd_lctx L' lctx')
   | _ => a_context
  end.

  Lemma upd_lctx_global: forall L1 L2 lctx1 lctx2 ctx eqn l,
    length L1 = length lctx1 ->
    length L2 = length lctx2 ->
    ctx |= eqn -> sublist (vars eqn) l ->
    disjoint_pwise (L1++l::L2) ->
    upd_lctx (L1++l::L2) (lctx1++ctx::lctx2) |= eqn.
  Proof.
   induction L1;intros;
   icase lctx1;simpl in *.
   apply eval_override_sublist;trivial.
   apply eval_override_disjoint.
   rewrite disjoint_pwise_equiv in H3.
   destruct H3. spec H3 l.
   apply disjoint_comm. apply sublist_disjoint with l;trivial.
   apply disjoint_comm. apply H3. apply in_app_iff. right. left. trivial.
   apply IHL1;try omega;trivial.
   rewrite disjoint_pwise_equiv.
   rewrite disjoint_pwise_equiv in H3.
   destruct H3. apply H4.
  Qed.

  Lemma partition_SAT_correct2 : forall l,
    (forall l', In l' (partition_SAT l) -> SAT l') -> SAT l.
  Proof.
    intros.
    apply SATL_rewrite1 in H.
    destruct H as [lctx H].
    exists (upd_lctx (var_list_extract (partition_SAT l)) lctx).
    apply list_eval_rewrite. intros.
    apply partition_exist in H0.
    destruct H0 as [l' [H1 H2]].
    generalize (In_split_length_eq _ _ _ (SATL_length_eq _ _ H) H1);intro.
    destruct H0 as [l1 [l2 [l3 [l4 [ctx [H3 [H4 [H5 H6]]]]]]]].
    rewrite H3 in *.
    rewrite var_list_extract_app;simpl.
    rewrite H4 in *.
    apply SATL_split in H;trivial.
    destruct H as [? [? ?]].
    apply upd_lctx_global.
    rewrite var_list_extract_length_eq;trivial.
    rewrite var_list_extract_length_eq;trivial.
    eapply list_eval_rewrite. apply H0. apply H2.
    generalize (sublist_vars _ _ H2);intros. apply H8.
    generalize (partition_disjoint l);intros. unfold partition_SAT in H3.
    rewrite H3 in H8. rewrite var_list_extract_app in H8. apply H8.
  Qed.

End Partition_SAT.

Definition varsable_pair (A B C : Type) `{varsable A B} : varsable (A * C ) B.
constructor. intros [? _]. apply (vars a).
Defined.

Module Partition_Input_Impl (Import pi : PARTITION_INPUT) <: PARTITION_INPUT
                             with Definition var := pi.var
                             with Definition equation := (pi.equation * bool)%type
                             with Definition varsable_equation := varsable_pair pi.equation pi.var bool .
  
  Definition equation : Type := (pi.equation * bool)%type.
  Definition var := pi.var.
  Definition eqn_eq_dec : EqDec equation.
  repeat intro. destruct a as [? ?]. destruct a' as [? ?].
  destruct (pi.eqn_eq_dec e e0).
  destruct (Bool.bool_dec b b0).
  left. subst. trivial.
  right. intro. apply n. inversion H;subst. trivial.
  right. intro. apply n. inversion H;subst. trivial.
  Defined.
  Existing Instance eqn_eq_dec.
  Definition var_eq_dec : EqDec var := pi.var_eq_dec.
  Existing Instance var_eq_dec.

  Definition varsable_equation: varsable equation var := varsable_pair pi.equation pi.var bool.
  Existing Instance varsable_equation.

  Definition context := context.
  Definition a_context := a_context.
  Definition context_override := context_override.

  Definition eval : evalable context equation.
  constructor. intros. destruct X0. apply (X |= e).
  Defined.
  Existing Instance eval.
  Lemma eval_override_disjoint: forall 
    (l : list var) (ctx ctx' : context) (eqn : equation),
    disjoint l (vars eqn) ->
    (ctx |= eqn <-> ([l => ctx'] ctx) |= eqn).
  Proof with auto.
   intros.
   destruct eqn. simpl.
   apply eval_override_disjoint...
  Qed.

  Lemma eval_override_sublist: forall
    (l : list var) (ctx ctx' : context) (eqn : equation),
    ctx |= eqn -> sublist (vars eqn) l ->
    ([l => ctx] ctx') |= eqn.
  Proof with auto.
   intros.
   destruct eqn.
   apply eval_override_sublist...
  Qed.

End Partition_Input_Impl.

Module Partition_IMPL (Import Input : INPUT)
                      (Import ot : OrderedType with Definition t := Input.e 
                                               with Definition eq := @Logic.eq Input.e)
                      (Import pi : PARTITION_INPUT with Definition var := ot.t)<:
                       PARTITION_IMPL pi.

  Module pi' := Partition_Input_Impl pi.
  Module Part := Partition Input ot pi'.
  Import Part.
  Module PL := Partition_Lemmas pi' Part.
  Import PL.  

 Definition IMPL (l1 l2 : list equation) : Prop :=
    forall rho, rho |= l1 -> rho |= l2.

  Definition merge {A} (L1 L2 : list A) : list (A * bool) :=
    (map (fun x => (x, false)) L1) ++ (map (fun x => (x, true)) L2).

  Definition separate {A} (L : list (A * bool)) : (list A) * (list A) :=
    (map (@fst _ _) (filter (fun x => negb (snd x)) L), 
     map (@fst _ _) (filter (fun x => snd x) L)).

  Definition IMPL_pair p := IMPL (fst p) (snd p).

  Definition partition_IMPL (l1 l2 : list equation) : list ((list equation)*(list equation))%type :=
   map separate (partition (merge l1 l2)).

  Definition SAT (l : list equation) : Prop := 
    exists rho, rho |= l.

  Lemma filter_app A f (l l':list A) :
   List.filter f (l ++ l') = List.filter f l ++ List.filter f l'.
  Proof.
   induction l as [|x l IH]; simpl; trivial.
   destruct (f x); simpl; now rewrite IH.
  Qed.

  Lemma merge_separate: forall {A : Type} (l1 l2 :list A),
   separate (merge l1 l2) = (l1,l2).
  Proof.
   intros.
   unfold separate,merge.
   repeat rewrite filter_app.
   repeat rewrite map_app.
   f_equal.
   rewrite<-app_nil_r.
   f_equal.
   induction l1;simpl;trivial.
   f_equal;apply IHl1.
   induction l2;simpl;trivial.
   rewrite<-app_nil_l.
   f_equal.
   induction l1;simpl;trivial.
   induction l2;simpl;trivial.
   f_equal;apply IHl2.
  Qed.

  Lemma merge_in1: forall {A : Type} (l1 l2 : list A) a,
   In a l1 <-> In (a,false) (merge l1 l2).
  Proof.
   induction l1;intros.
   split;intros. inv H.
   unfold merge in H. simpl in H.
   elimtype False. induction l2. inv H.
   apply IHl2. destruct H. inv H. apply H.
   unfold merge in *.
   split;intros. simpl.
   destruct H. subst. left. trivial.
   rewrite IHl1 in H. right. apply H.
   
   simpl in *.
   destruct H. inv H. left. trivial.
   apply IHl1 in H. right. trivial.
  Qed.

  Lemma merge_in2: forall {A : Type} (l1 l2 : list A) a,
   In a l2 <-> In (a,true) (merge l1 l2).
  Proof.
   induction l2;intros.
   split;intros. inv H.
   unfold merge in H. simpl in H.
   elimtype False. induction l1. inv H.
   apply IHl1. destruct H. inv H. apply H.
   unfold merge in *.
   split;intros. simpl.
   destruct H. subst. rewrite in_app_iff. right. left. trivial.
   rewrite IHl2 in H. rewrite in_app_iff in *.
   destruct H. left. trivial. right. right. trivial.
   
   rewrite in_app_iff in H.
   destruct H.
   right. apply IHl2.
   rewrite in_app_iff. left. trivial.
   destruct H. inv H. left. trivial.
   right. apply IHl2.
   rewrite in_app_iff. right. trivial.
  Qed.
 
  Lemma separate_in1: forall {A : Type}l (a : A),
   In a (fst (separate l)) <-> In (a,false) l.
  Proof.
   induction l;intros.
   simpl. tauto.
   split;intros.
   destruct a. destruct b. simpl in H.
   right. apply IHl. apply H.
   destruct H. inv H. left. trivial.
   right. apply IHl. apply H.
   destruct H. inv H. left. trivial.
   apply IHl in H.
   destruct a. destruct b; simpl. apply H. right. apply H.
  Qed.

  Lemma separate_in2: forall {A : Type}l (a : A),
   In a (snd (separate l)) <-> In (a,true) l.
  Proof.
   induction l;intros.
   simpl. tauto.
   split;intros.
   destruct a. destruct b; simpl in H.
   destruct H. subst. left. trivial.
   right. apply IHl. apply H.
   right. apply IHl. apply H.
   destruct H. subst. left. trivial.
   apply IHl in H.
   destruct a. destruct b;simpl. right. apply H. apply H.
  Qed.

  Lemma separate_merge_sublist: forall {A : Type} l (l1 l2 : list A),
   separate l = (l1,l2) ->
   sublist (merge l1 l2) l /\ sublist l (merge l1 l2).
  Proof.
   repeat intro.
   split;repeat intro.
   destruct e0. icase b.
   apply separate_in2.
   rewrite (merge_in2 l1). rewrite H. apply H0.
   apply separate_in1.
   rewrite (merge_in1 _ l2). rewrite H. apply H0.
   destruct e0. icase b.
   rewrite<- (merge_in2 l1). rewrite<- separate_in2 in H0.
   rewrite H in H0;apply H0.
   rewrite<- (merge_in1 _ l2). rewrite<- separate_in1 in H0.
   rewrite H in H0;apply H0.
  Qed.

  Lemma separate_merge_exists: forall {A : Type} L (l1 l2 : list A),
   In (l1,l2) (map separate L) ->
   exists l', In l' L /\ sublist (merge l1 l2) l' /\ sublist l' (merge l1 l2).
  Proof.
   induction L;intros. inv H.
   simpl in H.
   destruct H. exists a.
   split. left. trivial.
   apply separate_merge_sublist;trivial.
   spec IHL l1 l2 H.
   destruct IHL as [? [? ?]].
   exists x.
   split;trivial. right. trivial.
  Qed.
      
  Lemma partition_IMPL_sublist1: forall l1 l2 l1' l2',
   In (l1',l2') (partition_IMPL l1 l2) -> sublist l1' l1.
  Proof.
   repeat intro.
   apply merge_in1 with l2.
   apply (merge_in1 l1' l2' e0) in H0.
   unfold partition_IMPL in H.
   apply separate_merge_exists in H.
   destruct H as [? [? [? ?]]].
   apply partition_sublist in H.
   apply H. apply H1. apply H0.
  Qed.

  Lemma partition_IMPL_sublist2: forall l1 l2 l1' l2',
   In (l1',l2') (partition_IMPL l1 l2) -> sublist l2' l2.
  Proof.
   repeat intro.
   apply merge_in2 with l1.
   apply (merge_in2 l1' l2' e0) in H0.
   unfold partition_IMPL in H.
   apply separate_merge_exists in H.
   destruct H as [? [? [? ?]]].
   apply partition_sublist in H.
   apply H. apply H1. apply H0.
  Qed.

  Lemma partition_IMPL_In1: forall l1 l2 eqn,
   In eqn l1 -> exists l1' l2', In eqn l1' /\ In (l1',l2') (partition_IMPL l1 l2).
  Proof with try tauto.
   repeat intro.
   apply merge_in1 with l1 l2 eqn in H.
   unfold partition_IMPL.
   apply partition_exist in H.
   destruct H as [l' [H H1]].
   remember (separate l').
   destruct p as [l1' l2'];symmetry in Heqp.
   exists l1',l2'. apply separate_in1 in H1.
   rewrite Heqp in H1;simpl in H1.
   split... rewrite <- Heqp.
   apply in_map...
  Qed.
  
  Lemma partition_IMPL_In2: forall l1 l2 eqn,
   In eqn l2 -> exists l1' l2', In eqn l2' /\ In (l1',l2') (partition_IMPL l1 l2).
  Proof with try tauto.
   repeat intro.
   apply merge_in2 with l1 l2 eqn in H.
   unfold partition_IMPL.
   apply partition_exist in H.
   destruct H as [l' [H H1]].
   remember (separate l').
   destruct p as [l1' l2'];symmetry in Heqp.
   exists l1',l2'. apply separate_in2 in H1.
   rewrite Heqp in H1;simpl in H1.
   split... rewrite <- Heqp.
   apply in_map...
  Qed.

  Lemma nth_op_map: forall {A B} n l (f : A -> B) b,
   nth_op n (map f l) = Some b <-> exists a, nth_op n l = Some a /\ f a = b.
  Proof with try tauto.
   induction n;intros;simpl.
   case_eq (map f l);intros.
   split;intros. inv H0. destruct H0. icase l.
   destruct H0. inv H0. icase l. inv H.
   split;intros. inv H. exists a...
   destruct H as [? [? ?]]. congruence.
   case_eq (map f l). intros.
   split;intros. inv H0. destruct H0. icase l. 
   destruct H0. congruence.
   intros. icase l. inv H. apply IHn.
  Qed.
  
  Lemma vars_beqn: forall (eqn : equation) (b : bool),
   vars (eqn,b) = vars eqn.
  Proof.
   trivial.
  Qed.

  Lemma vars_merge: forall (l1 l2 : list equation),
   vars (merge l1 l2) = (vars l1)++(vars l2).
  Proof.
   induction l1;intros.
   unfold merge. simpl.
   induction l2. simpl. trivial.
   simpl. rewrite IHl2. f_equal.
   simpl in *.
   rewrite<- app_assoc. f_equal.
   apply IHl1.
  Qed.
    
  Lemma separate_sublist_vars: forall l l1 l2,
   separate l = (l1,l2) ->
   sublist (vars (l1++l2)) (vars l) /\ sublist (vars l) (vars (l1++l2)).
  Proof with try tauto.
   intros. apply separate_merge_sublist in H.
   repeat rewrite vars_app_rewrite.
   repeat rewrite <- vars_merge.
   split;apply sublist_listvars...
  Qed.

  Lemma partition_IMPL_disjoint: forall l1 l2 l1' l2' l1'' l2'' i j,
   nth_op i (partition_IMPL l1 l2) = Some (l1',l2') ->
   nth_op j (partition_IMPL l1 l2) = Some (l1'',l2'') ->
   i <> j -> disjoint (vars (l1'++l2')) (vars (l1''++l2'')).
  Proof with try tauto.
   intros.
   unfold partition_IMPL in *.
   apply nth_op_map in H.
   apply nth_op_map in H0.
   destruct H as [? [? ?]].
   destruct H0 as [? [? ?]].
   generalize (partition_nth_disjoint _ _ _ _ _ H H0 H1);intros.
   apply separate_sublist_vars in H2.
   apply separate_sublist_vars in H3.
   destruct H2;destruct H3.
   eapply sublist_disjoint;eauto.
   apply disjoint_comm. apply disjoint_comm in H4.
   eapply sublist_disjoint;eauto.
  Qed.

  Lemma partition_IMPL_correct1: forall l1 l2,
    (forall pl', In pl' (partition_IMPL l1 l2) -> IMPL_pair pl') ->
    IMPL l1 l2.
  Proof.
   repeat intro.
   apply list_eval_rewrite. intros.
   rewrite (merge_in2 l1) in H1.
   apply partition_exist in H1.
   destruct H1 as [? [? ?]].
   assert (In (separate x) (map separate (partition (merge l1 l2)))).
    apply in_map;trivial.
   spec H (separate x) H3.
   apply partition_IMPL_sublist1 in H3.     
   apply sublist_eval with (ctx:=rho) in H3;trivial.
   spec H rho H3.
   rewrite list_eval_rewrite in H. spec H e0. apply H.
   apply separate_in2. trivial.
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

  Lemma partition_IMPL_correct2 : forall l1 l2,
    SAT l1 ->
    IMPL l1 l2 ->
    forall pl', In pl' (partition_IMPL l1 l2) -> IMPL_pair pl'.
  Proof.
    intros.
    destruct H as [rho H].
    destruct pl' as [l1' l2']. unfold IMPL_pair;simpl. repeat intro.
    generalize (partition_IMPL_sublist1 _ _ _ _ H1);intro.
    generalize (partition_IMPL_sublist2 _ _ _ _ H1);intro.
    assert ([exclude (vars l1) (vars (l1'++l2')) => rho]rho0 |= l1).
     rewrite list_eval_rewrite;intros.
     assert ({In e0 l1'} + {~In e0 l1'}). apply In_dec. apply eqn_eq_dec.
     (*In e l1'*)
     rewrite vars_app_rewrite.
     destruct H6.
     apply eval_override_disjoint. 
     repeat intro. rewrite exclude_correct in H6. destruct H6 as [[? ?] ?].
     apply H7. apply in_app_iff. left. 
     apply sublist_vars in i. apply i. trivial.
     rewrite list_eval_rewrite in H2. apply H2;trivial.
     (*~In e l1'*)
     assert (disjoint (vars e0) ((vars l1')++(vars l2'))). 
       unfold partition_IMPL in H1.
       rewrite (merge_in1 _ l2) in H5.
       rewrite (merge_in1 _ l2') in n.
       apply separate_merge_exists in H1.
       destruct H1 as [? [? [? ?]]].
       assert (~In (e0,false) x). intro. apply n. apply H7. trivial.
       apply partition_not_in with (l:=merge l1 l2) in H8;trivial.
       apply sublist_listvars in H6.
       rewrite vars_merge in H6.
       apply disjoint_comm.
       apply disjoint_comm in H8.
       apply sublist_disjoint with (vars x);trivial. 
     rewrite disjoint_app_iff in H6.
     destruct H6. 
     assert (sublist (vars e0 ) (vars l1)). 
      apply sublist_vars;trivial.
     assert (sublist(vars e0) (exclude (vars l1) (vars l1' ++ vars l2'))).
      repeat intro.
      rewrite exclude_correct.
      rewrite in_app_iff. split. apply H8. trivial.
      intro. destruct H10.
      spec H6 e1. apply H6;auto.
      spec H7 e1. apply H7;auto.
     apply eval_override_sublist;trivial.
     rewrite list_eval_rewrite in H. apply H;trivial.
    spec H0 ([exclude (vars l1) (vars (l1'++l2')) => rho]rho0) H5.
    apply sublist_eval with (l:= l2')in H0;trivial.
    rewrite list_eval_rewrite. intros.
    rewrite list_eval_rewrite in H0. spec H0 e0 H6.
    rewrite<- eval_override_disjoint in H0;trivial.
    repeat intro.
    rewrite vars_app_rewrite in H7.
    rewrite exclude_correct in H7.
    destruct H7 as [[? ?] ?].
    apply H8.
    rewrite in_app_iff.
    right. apply sublist_vars in H6. apply H6. trivial.
  Qed.

End Partition_IMPL. 

Close Scope part_scope.