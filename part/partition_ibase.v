Add LoadPath "..".
Require Import List.
Require Import base.
Require Import uf.UF_interface.
Require Import uf.UF_implementation.
Require Import rbt.MMapRBT.
Require Import rbt.MMapInterface.
Require Import partition_base.
Require Import partition_interface.

Module Internal_Structures (Import Input : INPUT) 
                           (Import ot : OrderedType with Definition t := Input.e
                                                    with Definition eq := @Logic.eq Input.e).

  Module UF := Union_Find Input ot.
  Module UFL := UnionFind_Lemmas Input UF. Import UFL.
  Module RBT := Make ot.  

  Definition var := ot.t.

  (*Implementation section*)
  Definition emptyUF := UF.empty.
  Definition add_singleton2uf (uf : UF.t) (v : var) : 
   (UF.t * var) :=
   match (UF.find uf v) with
   | (Some v', uf') => (uf', v')
   | (None, uf')    => (UF.singleton uf' v,v)
   end.
  Definition add_singleton2uf_t p v := fst (add_singleton2uf p v).
  Definition add_singleton2uf_v p v := snd (add_singleton2uf p v).
  Definition union_singleton2uf (v : var) (p : (UF.t * option var)):
   (UF.t * option var):=
   let (uf,ov)  := p in
   let (uf',v') := add_singleton2uf uf v in
   match ov with
   | None     => (uf', Some v')
   | Some v'' => let uf'' := UF.union uf' v' v'' in (uf'',UF.find_e uf'' v')
   end.
  Definition union_singleton2uf_t v p := fst (union_singleton2uf v p).
  Definition union_singleton2uf_v v p := snd (union_singleton2uf v p).
  Definition add_list2uf (uf : UF.t) (l : list var)  : (UF.t * option var):=
   fold_right union_singleton2uf (uf,None) l. 
  Definition add_list2uf_t uf l := fst (add_list2uf uf l).
  Definition add_list2uf_v uf l := snd (add_list2uf uf l). 
  Definition eqn2uf {A : Type} `{VAB : varsable A var} (uf : UF.t) (eqn : A) :=
   add_list2uf uf (vars eqn) .
  Implicit Arguments eqn2uf [A VAB].
  Definition eqn2uf_t {A : Type} `{VAB : varsable A var} (uf : UF.t) (eqn : A) := fst (eqn2uf uf eqn).
  Implicit Arguments eqn2uf_t [A VAB].
  Definition eqn2uf_v {A : Type} `{VAB : varsable A var} uf eqn:= snd (eqn2uf uf eqn).
  Implicit Arguments eqn2uf_v [A VAB].
  Definition eqnlist2uf {A : Type} `{VAB : varsable A var} (l : list A) : UF.t :=
   fold_right (fun eqn uf => eqn2uf_t uf eqn) emptyUF l.
  Definition get_t {A : Type} (p : (UF.t * A)) := fst p.
  Definition get_v {A : Type} (p : (UF.t * A)) := snd p.

  Definition emptyRBT (A : Type):= @RBT.empty A.
  Definition find_var {A : Type } `{VAB : varsable A var} (uf : UF.t)  (eqn : A) : 
  (option var * UF.t) :=
   match (vars eqn) with
   | nil  => (None,uf)
   | v::l => UF.find uf v
   end.
  Definition find_var_v {A : Type } `{VAB : varsable A var} (uf : UF.t) (eqn : A) : 
   option var := fst (find_var uf eqn). 
  Definition find_var_uf {A : Type } `{VAB : varsable A var} (uf : UF.t)  (eqn : A) : 
   UF.t := snd (find_var uf eqn). 
  Definition find_add {B: Type} 
  (a : var) (b : B) (rbt : RBT.map_of (list B)) : RBT.map_of (list B):=
   match RBT.find a rbt with
   | Some l => RBT.add a (b::l) rbt
   | None   => RBT.add a (b::nil) rbt
   end.
  Definition find_list_rbt {B : Type} (a : var) (rbt : RBT.map_of (list B)) : list B :=
   match RBT.find a rbt with
   | None => nil
   | Some l => l
   end.
  (*Precondition: all vars were already in uf*)
  Definition add_equation2RBT {A : Type} `{VAB : varsable A var}
  (eqn : A) (uf : UF.t) (rbt : RBT.map_of (list A)) (l : list A) : 
  (list A * (RBT.map_of (list A)))%type:=
   match find_var_v uf eqn with
   | None   => match (vars eqn) with
               | nil    => (eqn::l,rbt)
               | v'::l' => (l,rbt) (*should never happen*)
               end
   | Some v => (l,find_add v eqn rbt)
   end.
  Definition add_equation2RBT_l {A : Type} `{VAB : varsable A var} (eqn:A) uf rbt l := 
   fst (add_equation2RBT eqn uf rbt l).
  Implicit Arguments add_equation2RBT_l [A VAB].
  Definition add_equation2RBT_rbt {A : Type} `{VAB : varsable A var} (eqn:A) uf rbt l := 
   snd (add_equation2RBT eqn uf rbt l).
  Implicit Arguments add_equation2RBT_rbt [A VAB].
  Definition get_list {A B : Type} (p : (list A * RBT.map_of B)%type) := fst p.
  Definition get_rbt {A B : Type} (p : (list A * RBT.map_of B)%type) := snd p.
  (*Precondition: all vars were already in uf*)
  Definition eqnlist2RBT {A : Type} `{VAB : varsable A var}
  (l : list A) (uf : UF.t) : (list A * RBT.map_of (list A))%type :=
   fold_right (fun eqn p => add_equation2RBT eqn uf (snd p) (fst p)) 
              (nil,emptyRBT (list A)) l.
  Definition eqnlist2RBT_l {A : Type} `{VAB : varsable A var} (l : list A) uf :=
   fst (eqnlist2RBT l uf).
  Implicit Arguments eqnlist2RBT_l [A VAB].
  Definition eqnlist2RBT_rbt {A : Type} `{VAB : varsable A var} (l : list A) uf :=
   snd (eqnlist2RBT l uf).
  Implicit Arguments eqnlist2RBT_rbt [A VAB].
  (*Conditions for UF section*)
  Definition UF_in_cond {A : Type} `{VAB : varsable A var} (uf : UF.t) (l : A)  : Prop :=
   forall v', In v' (vars l) -> UF.In uf v'.
  Definition UF_component_cond {A : Type} `{VAB : varsable A var} (uf : UF.t)  (eqn : A): Prop :=
   (vars eqn) <> nil ->
   (exists v, forall v', In v' (vars eqn) -> UF.find_e uf v' = Some v).
  Definition UF_lcomponents_cond {A : Type} `{VAB : varsable A var} uf (l : list A) : Prop :=
   forall eqn, In eqn l -> UF_component_cond uf eqn.
  Definition UF_set_of_cond {A : Type} `{VAB:varsable A var}(uf : UF.t) (eqn : A) : Prop :=
   forall v1 v2, In v1 (vars eqn) -> In v2 (vars eqn) -> UF.In uf v1 /\ UF.set_of uf v1 v2.

  Lemma UF_set_of_cond_equiv: forall {A : Type} `{VAB:varsable A var} uf (eqn : A),
   UF_set_of_cond uf eqn <-> UF_component_cond uf eqn.
  Proof.
   intros. split;repeat intro.
   unfold UF_set_of_cond in H.
   remember (vars eqn).
   icase l. tauto.
   assert (In v (v::l)). left;trivial.
   destruct (H v v H1 H1).
   apply In_Some in H2.
   destruct H2. exists x. intros.
   destruct (H v v' H1 H4). congruence.
   unfold UF_component_cond in H.
   detach H. destruct H.
   generalize (H _ H0);intro.
   generalize (H _ H1);intro.
   split. apply In_Some. exists x;trivial.
   congruence.
   intro. unfold var in H. unfold t in *.
   rewrite H in H0. inv H0.
  Qed.

  Lemma UF_in_cond_prop1 : forall {A : Type} `{VAB : varsable A var} (a : A) l uf,
   UF_in_cond uf  (a::l) <-> UF_in_cond uf a /\ UF_in_cond uf l.
  Proof.
   repeat intro.
   unfold UF_in_cond.
   simpl. split;intros.
   split;intros;
   spec H v'; rewrite in_app_iff in H; tauto.
   rewrite in_app_iff in H0.
   destruct H.
   spec H v'. spec H1 v'. tauto.
  Qed.

  Lemma UF_in_cond_prop2: forall (A : Type) (VAB : varsable A var) (l : list A) (a : A)  uf,
   UF_in_cond uf l -> In a l-> UF_in_cond uf a.
  Proof.
   induction l;intros. inversion H0.
   apply UF_in_cond_prop1 in H.
   destruct H0. subst. tauto.
   apply IHl;trivial. tauto.
  Qed.

  Lemma UF_component_cond_prop1: forall {A : Type} `{VAB : varsable A var} (a : A) l uf,
   UF_component_cond uf (a::l)  -> UF_component_cond uf a /\ UF_component_cond uf l.
  Proof. 
   intros.
   unfold UF_component_cond in *.
   split;intros.
   detach H. destruct H.
   exists x;intros. apply H.
   simpl. rewrite in_app_iff. left;trivial.
   simpl. intro. apply H0. apply app_eq_nil in H. tauto.
   detach H. destruct H.
   exists x;intros. apply H.
   simpl. rewrite in_app_iff. right;trivial.
   simpl. intro. apply H0. apply app_eq_nil in H. tauto.
  Qed.

  Lemma UF_component_cond_prop2: forall {A : Type} `{VAB : varsable A var} (a : A) uf,
   UF_component_cond uf a -> UF_in_cond uf a.
  Proof.
   intros.
   unfold UF_in_cond,UF_component_cond in *.
   intros.
   detach H. destruct H. spec H v' H0.
   unfold UF.In. rewrite H. simpl. trivial.
   intro. unfold var in *. unfold t in *. 
   rewrite H in H0. inv H0.
  Qed.

  Lemma UF_lcomponents_cond_prop1: forall {A : Type} `{VAB : varsable A var} (a : A) l uf,
   UF_lcomponents_cond uf (a::l) <-> UF_component_cond uf a /\ UF_lcomponents_cond uf l.
  Proof.
   intros.
   unfold UF_lcomponents_cond,UF_component_cond in *.
   split;intros.
   split;intros.
   apply H;trivial. left;trivial.
   apply H;trivial. right;trivial.
   destruct H.
   destruct H0. subst a. apply H. trivial.
   apply H2;trivial.
  Qed.

  Lemma UF_lcomponents_cond_prop2: forall {A : Type} `{VAB: varsable A var} (l : list A) uf,
   UF_component_cond uf l -> UF_lcomponents_cond uf l.
  Proof.
   intros.
   unfold UF_lcomponents_cond, UF_component_cond in *.
   intros.
   detach H. destruct H.
   exists x. intros. apply H. eapply sublist_vars.
   apply H0. apply H2.
   intro. apply H1. apply sublist_vars in H0. rewrite H in H0.
   apply sublist_nil;trivial.
  Qed.

  Lemma UF_lcomponents_cond_prop3: forall {A : Type} `{VAB: varsable A var} (l : list A) uf,
   UF_lcomponents_cond uf l -> UF_in_cond uf l.
  Proof.
   intros.
   unfold UF_lcomponents_cond,UF_component_cond,UF_in_cond in *.
   intros.
   apply var_list_exist in H0.
   destruct H0 as [? [? ?]].
   spec H x H0. detach H. destruct H.
   spec H v' H1.
   unfold UF.In. rewrite H. simpl;trivial.
   intro. rewrite H in H1. inversion H1.
  Qed.

  Lemma UF_lcomponents_cond_prop4: forall {A : Type} `{VAB: varsable A var} (l l' : list A) uf,
   UF_lcomponents_cond uf l -> sublist l' l -> UF_lcomponents_cond uf l'.
  Proof.
   intros.
   unfold UF_lcomponents_cond in *.
   intros. apply H. apply H0. apply H1.
  Qed.


  (*UF Lemmas section*)
  Lemma find_rewrite: forall uf uf' e e',
   (e',uf') = UF.find uf e -> uf' = UF.find_t uf e /\ e' = UF.find_e uf e.
  Proof.
   intros.
   unfold UF.find_t,UF.find_e. 
   rewrite<-H;simpl. tauto.
  Qed.

  Lemma add_singleton2uf_rewrite: forall uf uf' v v',
   (uf',v') = add_singleton2uf uf v -> 
   uf' = add_singleton2uf_t uf v /\ v' = add_singleton2uf_v uf v.
  Proof.
   intros.
   unfold add_singleton2uf_t,add_singleton2uf_v.
   rewrite<- H. simpl;tauto.
  Qed.

  Lemma add_singleton2uf_not_In: forall uf v ,
   ~UF.In uf v -> 
   UF.set_in (add_singleton2uf_t uf v) (set_singleton v).
  Proof.
   intros.
   unfold add_singleton2uf_t,add_singleton2uf .
   remember (UF.find uf v). icase p.
   apply find_rewrite in Heqp. destruct Heqp;subst.
   remember (UF.find_e uf v). icase o;simpl.
   elimtype False. apply H.
   apply In_Some. exists e0. rewrite Heqo;trivial.
   apply UF.singleton_set_in_refl. intro. apply H.
   rewrite In_find_reduce in H0. trivial.
  Qed.

  Lemma add_singleton2uf_In: forall uf v1 v2,
   UF.In uf v1 -> UF.set_of uf v1 v2 ->
   forall v, UF.In (add_singleton2uf_t uf v) v1 /\ 
             UF.set_of (add_singleton2uf_t uf v) v1 v2 .
  Proof.
   intros.
   unfold add_singleton2uf_t,add_singleton2uf.
   remember (UF.find uf v). icase p.
   apply find_rewrite in Heqp.
   destruct Heqp;subst.
   remember (UF.find_e uf v). icase o;simpl.
   split. apply In_find_reduce. trivial.
   rewrite set_of_find_reduce. trivial.
   assert (~UF.In (UF.find_t uf v) v).
    rewrite In_find_reduce. intro.
    apply In_Some in H1. destruct H1. rewrite H1 in Heqo. inv Heqo.
   apply singleton_set_of;trivial.
   apply In_find_reduce. trivial.
   rewrite set_of_find_reduce. trivial.
  Qed.

  Lemma add_singleton2uf_set_of: forall uf v,
   UF.In (add_singleton2uf_t uf v) (add_singleton2uf_v uf v) /\ 
   UF.set_of (add_singleton2uf_t uf v) (add_singleton2uf_v uf v) v.
  Proof.
   intros.
   unfold add_singleton2uf_t,add_singleton2uf_v,add_singleton2uf.
   remember (UF.find uf v). icase p.
   apply find_rewrite in Heqp.
   destruct Heqp;subst.
   remember (UF.find_e uf v). icase o;simpl.
   split. apply In_find_reduce. apply find_In with v.
   rewrite Heqo;trivial.
   rewrite set_of_find_reduce.
   apply set_of_comm.
   apply Some_set_of.
   rewrite Heqo;trivial.
   split. apply In_Some.
   exists v. symmetry in Heqo. 
   apply set_singleton_find. 
   apply UF.singleton_set_in_refl.
   rewrite In_find_reduce.
   apply In_None. trivial.
   apply set_of_refl.
  Qed.

  Lemma union_singleton2uf_rewrite: forall uf uf' v v',
   (uf',v') = union_singleton2uf uf v -> 
   uf' = union_singleton2uf_t uf v /\ v' = union_singleton2uf_v uf v.
  Proof.
   intros.
   unfold union_singleton2uf_t,union_singleton2uf_v.
   rewrite<- H. simpl;tauto.
  Qed.
   
  Lemma union_singleton2uf_In: forall uf v v' v1 v2, 
   UF.In uf v ->
   UF.In uf v1 ->
   UF.set_of uf v1 v2 -> 
   UF.In (union_singleton2uf_t v' (uf,Some v)) v1 /\ 
   UF.set_of (union_singleton2uf_t v' (uf,Some v) ) v1 v2. 
  Proof.
   intros.
   unfold union_singleton2uf_t,union_singleton2uf.
   remember (add_singleton2uf uf v'). icase p;simpl.
   apply add_singleton2uf_rewrite in Heqp.
   destruct Heqp;subst.
   generalize (add_singleton2uf_set_of uf v);intro.
   destruct H2. 
   generalize (add_singleton2uf_In _ _ _ H0 H1 v);intro.
   simpl.
   destruct H4.
   apply union_set_of.
   apply add_singleton2uf_set_of.
   eapply add_singleton2uf_In.
   apply H. apply set_of_refl.
   eapply add_singleton2uf_In.
   apply H0. apply set_of_refl.
   apply add_singleton2uf_In;trivial.
  Qed.

  Lemma union_singleton2uf_None: forall uf v,
   union_singleton2uf v (uf,None) = 
  (add_singleton2uf_t uf v, Some (add_singleton2uf_v uf v)).
  Proof.
   intros.
   unfold union_singleton2uf.
   unfold add_singleton2uf_v,add_singleton2uf_t.
   remember (add_singleton2uf uf v).
   destruct p. simpl. trivial.
  Qed.

  Lemma union_singleton2uf_Some: forall uf a a' v,
   UF.In uf a ->
   union_singleton2uf_v a' (uf,Some a) = Some v ->
   UF.In (union_singleton2uf_t a' (uf,Some a)) v /\ 
   UF.set_of (union_singleton2uf_t a' (uf,Some a)) a' v.
  Proof.
   intros.
   unfold union_singleton2uf_t.
   unfold union_singleton2uf_v in H0.
   unfold union_singleton2uf in *.
   remember (add_singleton2uf uf a'). icase p.
   apply add_singleton2uf_rewrite in Heqp.
   destruct Heqp;subst. simpl in *.
   split. eapply find_In. apply H0.
   apply set_of_trans with (e':=add_singleton2uf_v uf a').
   eapply union_set_of.
   apply add_singleton2uf_set_of.
   eapply add_singleton2uf_In;trivial.
   apply set_of_refl.
   destruct (add_singleton2uf_set_of uf a').
   apply In_Some in H1. destruct H1.
   apply In_Some. exists x. congruence.
   apply set_of_comm. apply add_singleton2uf_set_of.
   apply Some_set_of in H0. apply H0.
  Qed.   

  Lemma union_singleton2uf_combine: forall uf a v,
   UF.In uf a ->
   UF.In (union_singleton2uf_t v (uf, Some a)) a /\ 
   UF.set_of (union_singleton2uf_t v (uf, Some a)) v a.
  Proof.
   intros.
   unfold union_singleton2uf_t,union_singleton2uf.
   remember (add_singleton2uf uf v). icase p. simpl.
   apply add_singleton2uf_rewrite in Heqp. destruct Heqp. subst.
   split. eapply union_set_of.
   apply add_singleton2uf_set_of.
   eapply add_singleton2uf_In;trivial.
   apply set_of_refl.
   eapply add_singleton2uf_In;trivial.
   apply set_of_refl.
   apply set_of_refl.
   apply set_of_trans with (add_singleton2uf_v uf v).
   eapply union_set_of.
   apply add_singleton2uf_set_of.
   eapply add_singleton2uf_In;trivial.
   apply set_of_refl.
   destruct (add_singleton2uf_set_of uf v).
   apply In_Some in H0. destruct H0.
   apply In_Some. exists x.
   rewrite<- H0.
   generalize (set_of_rewrite);intro.
   rewrite H2 in H1. congruence.
   apply set_of_comm. apply add_singleton2uf_set_of.
   apply union_combine.
   apply add_singleton2uf_set_of.
   eapply add_singleton2uf_In;trivial.
   apply set_of_refl.
  Qed.

  Lemma union_singleton2uf_exist_Some: forall {A : Type} `{VAB:varsable A var} uf a v,
   UF.In uf a ->
   exists v', union_singleton2uf_v v (uf,Some a) = Some v'.
  Proof.
   intros.
   unfold union_singleton2uf_v,union_singleton2uf.
   remember (add_singleton2uf uf v).
   icase p. apply add_singleton2uf_rewrite in Heqp.
   destruct Heqp;subst. simpl.
   apply In_Some.
   eapply union_set_of.
   apply add_singleton2uf_set_of.
   eapply add_singleton2uf_In;trivial.
   apply set_of_refl.
   apply add_singleton2uf_set_of.
   apply set_of_refl.
  Qed.

  Lemma add_list2uf_rewrite: forall uf uf' a' l,
   (uf',a') = add_list2uf uf l -> 
   uf' = add_list2uf_t uf l /\ a' = add_list2uf_v uf l.
  Proof.
   intros.
   unfold add_list2uf_t,add_list2uf_v;rewrite<-H.
   simpl;auto.
  Qed.

  Lemma add_list2uf_step_rewrite: forall uf a l,
   add_list2uf uf (a::l) = union_singleton2uf a (add_list2uf uf l).
  Proof.
   intros. simpl. tauto.
  Qed.

  Lemma add_list2uf_single: forall uf a,
   add_list2uf uf (a::nil) = union_singleton2uf a (uf,None).
  Proof.
   intros. simpl. tauto.
  Qed.

  Lemma add_list2uf_Some: forall {A : Type} `{VAB:varsable A var} l uf a,
    add_list2uf_v uf l = Some a -> UF.In (add_list2uf_t uf l) a .
  Proof.
   induction l;intros.
   unfold add_list2uf_v in H. inv H.
   unfold add_list2uf_t.
   unfold add_list2uf_v in H.
   rewrite add_list2uf_step_rewrite in *.
   remember (add_list2uf uf l).
   remember (union_singleton2uf a p).
   icase p0.
   apply union_singleton2uf_rewrite in Heqp0.
   destruct Heqp0;subst t0 o. simpl in *.
   icase p. apply add_list2uf_rewrite in Heqp.
   destruct Heqp;subst.
   remember (add_list2uf_v uf l). icase o.
   symmetry in Heqo. apply IHl in Heqo.
   destruct (union_singleton2uf_combine _ _ a Heqo).
   apply union_singleton2uf_Some;trivial.
   unfold union_singleton2uf_v,union_singleton2uf_t in *.
   rewrite union_singleton2uf_None in *. simpl in *.
   inv H. apply add_singleton2uf_set_of.
  Qed.

  Lemma add_list2uf_None: forall {A : Type} `{VAB:varsable A var} l uf,
   add_list2uf_v uf l = None <-> l = nil.
  Proof.
   induction l;intros;
   unfold add_list2uf_v.
   simpl;tauto.
   rewrite add_list2uf_step_rewrite.
   split;intros.
   remember (add_list2uf uf l). icase p.
   apply add_list2uf_rewrite in Heqp.
   destruct Heqp;subst.
   remember (add_list2uf_v uf l). 
   icase o;symmetry in Heqo.
   apply add_list2uf_Some in Heqo.
   apply union_singleton2uf_exist_Some with (v:=a) in Heqo.
   destruct Heqo. 
   unfold union_singleton2uf_v in H0.
   unfold var in *. unfold t in *. rewrite H0 in H. inv H.
   apply IHl in Heqo. subst.
   unfold add_list2uf_t in H. simpl in H.
   destruct (add_singleton2uf uf a);inv H.
   inv H.
  Qed.

  Lemma add_list2uf_In: forall {A : Type} `{VAB:varsable A var} l uf a a',
   UF.In uf a ->
   UF.set_of uf a a' ->
   UF.In (add_list2uf_t uf l) a /\ UF.set_of (add_list2uf_t uf l) a a'.
  Proof.
   induction l;intros.
   unfold add_list2uf_t;simpl. tauto.
   unfold add_list2uf_t.
   rewrite add_list2uf_step_rewrite.
   remember (add_list2uf uf l).
   remember (union_singleton2uf a p).
   icase p0. 
   apply union_singleton2uf_rewrite in Heqp0.
   destruct Heqp0;subst. simpl.
   remember (add_list2uf uf l).
   icase p.
   apply add_list2uf_rewrite in Heqp. destruct Heqp.
   icase o;subst.
   apply union_singleton2uf_In.
   apply add_list2uf_Some. rewrite H2;trivial.
   eapply IHl;trivial. apply H0.
   apply IHl;trivial.
   unfold union_singleton2uf_t.
   rewrite union_singleton2uf_None. simpl.
   apply add_singleton2uf_In.
   eapply IHl;trivial. apply H0.
   apply IHl;trivial.
  Qed.  

  Lemma add_list2uf_set_of: forall {A : Type} `{VAB:varsable A var} l uf a v,
   In v l -> 
   add_list2uf_v uf l = Some a ->
   UF.set_of (add_list2uf_t uf l) a v.
  Proof.
   induction l;intros. inv H.
   generalize (add_list2uf_Some _ _ _ H0);intro.
   unfold add_list2uf_t. unfold add_list2uf_v,add_list2uf_t in H0,H1.
   rewrite add_list2uf_step_rewrite in *.
   remember (union_singleton2uf a (add_list2uf uf l)).
   destruct p. apply union_singleton2uf_rewrite in Heqp.
   destruct Heqp. subst. simpl in *.
   apply set_of_comm.
   remember (add_list2uf uf l).
   icase p. apply add_list2uf_rewrite in Heqp.
   destruct Heqp. subst.
   remember (add_list2uf_v uf l).
   symmetry in Heqo. icase o.
   destruct H;subst.
   apply union_singleton2uf_Some;trivial.
   apply add_list2uf_Some;trivial.
   generalize (IHl _ _ _ H Heqo);intro.
   apply add_list2uf_Some in Heqo.
   remember (add_list2uf_t uf l) as uf'.
   apply set_of_comm.
   apply set_of_trans with (e':=v0).
   apply set_of_trans with (e':=a).
   apply set_of_comm.
   apply union_singleton2uf_Some;trivial.
   apply union_singleton2uf_combine;trivial.
   apply union_singleton2uf_In;trivial.

   unfold union_singleton2uf_t,union_singleton2uf_v in *.
   rewrite union_singleton2uf_None in *. simpl in *. inv H0.
   destruct H;subst.
   apply set_of_comm. apply add_singleton2uf_set_of.
   apply add_list2uf_None in Heqo. subst. inv H.
  Qed.

  Lemma eqn2uf_component_cond: forall {A : Type} `{VAB:varsable A var} 
  (a : A) (uf : UF.t),
   UF_component_cond (eqn2uf_t uf a) a.
  Proof.
   intros. apply UF_set_of_cond_equiv.
   repeat intro.
   unfold eqn2uf_t,eqn2uf.
   remember (add_list2uf uf (vars a)).
   icase p. apply add_list2uf_rewrite in Heqp.
   destruct Heqp;subst. simpl.
   remember (add_list2uf_v uf (vars a)).
   symmetry in Heqo. icase o.
   apply add_list2uf_set_of with (uf:=uf) (a:=v) in H;trivial.
   apply add_list2uf_set_of with (uf:=uf) (a:=v) in H0;trivial.
   apply add_list2uf_Some in Heqo.
   apply In_Some in Heqo. destruct Heqo.
   split. apply In_Some. exists x. 
   unfold var in *;unfold t in *;congruence.
   unfold var in *;unfold t in *;congruence.
   apply add_list2uf_None in Heqo.
   unfold var in *;unfold t in *;rewrite Heqo in H. inv H.
  Qed.

  Lemma eqnlist2uf_lcomponents_cond: forall {A : Type} `{VAB:varsable A var} (l : list A),
   UF_lcomponents_cond (eqnlist2uf l) l.
  Proof.
   induction l;intros.
   unfold UF_lcomponents_cond. intros. inversion H.
   rewrite UF_lcomponents_cond_prop1. split.
   apply eqn2uf_component_cond. simpl.
   do 2 intro.
   apply UF_set_of_cond_equiv.
   spec IHl eqn H.
   apply UF_set_of_cond_equiv in IHl.
   repeat intro.
   destruct (IHl v1 v2 H0 H1).
   unfold eqn2uf_t,eqn2uf.
   apply add_list2uf_In;trivial.
  Qed.


  (*RBT Lemmas section*)

  Lemma find_list_rbt_spec: forall {B : Type} rbt a (b : list B),
   RBT.MapsTo a b rbt -> find_list_rbt a rbt = b.
  Proof.
   intros.
   unfold find_list_rbt.
   rewrite<- RBT.find_spec in H.
   rewrite H. trivial.
  Qed.
  Lemma find_add_spec1: forall {A : Type} `{VAB : varsable A var} 
   (eqn : A) v rbt,
   RBT.MapsTo v (eqn::(find_list_rbt v rbt)) (find_add v eqn rbt).
  Proof.
   intros.
   unfold find_list_rbt,find_add.
   remember (RBT.find v rbt). 
   icase o;
   apply RBT.add_spec1.
  Qed.
  Lemma find_add_spec2: forall {A : Type} `{VAB : varsable A var}
   (eqn : A) v v' l rbt,
   v' <> v ->
   (RBT.MapsTo v' l (find_add v eqn rbt) <-> RBT.MapsTo v' l rbt). 
  Proof.
   intros.
   unfold find_add.
   remember (RBT.find v rbt).
   icase o;apply RBT.add_spec2;trivial.
  Qed.

  Lemma find_var_v_spec1: forall {A : Type} `{VAB : varsable A var} (eqn : A) uf,
   UF_in_cond uf eqn ->
   vars eqn <> nil ->
   exists v, find_var_v uf eqn = Some v.
  Proof.
   intros.
   unfold find_var_v,find_var.
   unfold UF_in_cond in H.
   remember (vars eqn). icase l. tauto.
   spec H v. detach H. unfold UF.In,UF.find_e in H.
   icase (UF.find uf v). icase o. exists e0. trivial.
   left;trivial.
  Qed.
  
  Lemma add_equation2RBT_rewrite : forall {A : Type} `{VAB :varsable A var} (eqn : A) rbt rbt' uf l l',
   (l',rbt') = add_equation2RBT eqn rbt uf l ->
   l' = add_equation2RBT_l eqn rbt uf l /\
   rbt' = add_equation2RBT_rbt eqn rbt uf l.
  Proof.  
   intros.
   unfold add_equation2RBT_l,add_equation2RBT_rbt.
   rewrite <-H;simpl. tauto.
  Qed.

  Lemma add_equation2RBT_spec1 : forall {A : Type} `{VAB :varsable A var} v (eqn : A) rbt uf l,
   find_var_v uf eqn = Some v -> 
   RBT.MapsTo v (eqn::(find_list_rbt v rbt)) 
                (add_equation2RBT_rbt eqn uf rbt l).
  Proof with auto.
   intros.
   unfold add_equation2RBT_rbt,add_equation2RBT in *.
   icase (find_var_v uf eqn). inv H.
   apply find_add_spec1.
  Qed.

  Lemma add_equation2RBT_spec2 : forall {A : Type} `{VAB :varsable A var} v v' eqn rbt uf l l',
   find_var_v uf eqn = Some v -> 
   v' <> v ->
   (RBT.MapsTo v' l' (add_equation2RBT_rbt eqn uf rbt l) <-> 
    RBT.MapsTo v' l' rbt).
  Proof.
   intros.
   unfold add_equation2RBT_rbt,add_equation2RBT.
   remember (find_var_v uf eqn). icase o. inv H.
   apply find_add_spec2;trivial.
  Qed.

  Lemma add_equation2RBT_spec3: forall {A : Type} `{VAB :varsable A var} v eqn rbt uf l,
   find_var_v uf eqn = Some v -> 
   add_equation2RBT_l eqn uf rbt l = l.
  Proof.
   intros.
   unfold add_equation2RBT_l,add_equation2RBT.
   icase (find_var_v uf eqn).
  Qed.

  Lemma add_equation2RBT_spec4 : forall {A : Type} `{VAB :varsable A var} (eqn : A) rbt uf l,
   vars eqn = nil ->
   add_equation2RBT eqn uf rbt l = (eqn::l,rbt).
  Proof.
   intros.
   unfold add_equation2RBT.
   unfold find_var_v,find_var.
   remember (vars eqn). icase l0.
  Qed.

  Lemma add_equation2RBT_spec5 : forall {A : Type} `{VAB : varsable A var} (eqn : A) rbt uf l,
   add_equation2RBT_l eqn uf rbt l = eqn::l ->
   vars eqn = nil.
  Proof.
   intros.
   unfold add_equation2RBT_l,add_equation2RBT in H.
   unfold find_var_v,find_var in H.
   remember (vars eqn). icase l0.
   assert (forall {A : Type} (l' : list A) a, l' = a::l' -> False).
    induction l'; repeat intro. inv H0.
    spec IHl' a. apply IHl'. inversion H0. subst a;trivial.
   elimtype False.
   icase (UF.find uf v). 
   icase o;inversion H;
   apply H0 with A l eqn;trivial.
  Qed.

  Lemma add_equation2RBT_spec6 : forall {A : Type} `{VAB : varsable A var} (eqn : A) rbt uf l l' v,
   find_var_v uf eqn = Some v -> l' <> nil ->
   RBT.MapsTo v (eqn::l') (add_equation2RBT_rbt eqn uf rbt l) ->
   RBT.MapsTo v l' rbt.
  Proof.
   intros.
   unfold add_equation2RBT_rbt,add_equation2RBT in H1.
   remember (find_var_v uf eqn). icase o. inv H.
   unfold find_add in H1.
   remember (RBT.find v rbt). icase o. simpl in H1.
   assert (eqn::l' = eqn::l0). 
    eapply RBT.MapsTo_spec2. apply H1. apply RBT.add_spec1.
   inv H.
   symmetry in Heqo0. apply RBT.find_spec. trivial.
   assert (eqn::l' = eqn::nil).
    eapply RBT.MapsTo_spec2. apply H1. apply RBT.add_spec1.
   inv H. tauto.
  Qed.

  Lemma eqnlist2RBT_rewrite: forall {A} `{VAB : varsable A var} (l l' : list A) uf rbt,
   (l',rbt) = eqnlist2RBT l uf ->
   l' = eqnlist2RBT_l l uf/\
   rbt = eqnlist2RBT_rbt l uf.
  Proof.
   intros.
   unfold eqnlist2RBT_l,eqnlist2RBT_rbt.
   rewrite <- H. simpl. tauto.
  Qed.

  Lemma eqnlist2RBT_step_rewrite: forall {A} `{VAB : varsable A var} (eqn : A) l uf,
   eqnlist2RBT (eqn::l) uf = add_equation2RBT eqn uf (eqnlist2RBT_rbt l uf) (eqnlist2RBT_l l uf).
  Proof.
   intros. simpl. trivial.
  Qed.

  Lemma eqnlist2RBT_spec1: forall {A} `{VAB : varsable A var} l (eqn : A) uf v,
   UF_in_cond uf l-> 
   In eqn l -> find_var_v uf eqn = Some v -> 
   exists l', RBT.MapsTo v l' (eqnlist2RBT_rbt l uf) /\ In eqn l'.
  Proof.
   induction l;intros. inv H0.
   destruct H0. subst a.
   simpl.
   exists (eqn::(find_list_rbt v (eqnlist2RBT_rbt l uf))).
   split.
   apply add_equation2RBT_spec1;trivial.
   left;trivial.
   rewrite UF_in_cond_prop1 in H.
   destruct H.
   spec IHl eqn uf v H2 H0.
   spec IHl H1.
   destruct IHl as [? [? ?]].
   simpl. 
   unfold eqnlist2RBT_rbt. rewrite eqnlist2RBT_step_rewrite.
   generalize (list_eq_dec e_eq_dec (vars a) nil);intros.
   (*a is in list*)
   destruct H5.
   rewrite add_equation2RBT_spec4;trivial. simpl.
   exists x. tauto.
   (*a is in rbt*)
   generalize (find_var_v_spec1 _ _ H n);intro.
   destruct H5.
   generalize (e_eq_dec v x0);intro.
   (*Same principle element*)
   destruct H6. subst x0.
   assert (find_list_rbt v (get_rbt (eqnlist2RBT l uf)) = x).
    apply find_list_rbt_spec;trivial.
   exists (a::x).
   rewrite<-H6.
   split. apply add_equation2RBT_spec1;trivial.
   right. congruence.
   (*Different principle elements*)
   exists x. eapply add_equation2RBT_spec2 in n0; trivial.
   unfold add_equation2RBT_rbt in n0. rewrite n0.
   split;trivial. apply H5.
  Qed.

  Lemma list2RBT_spec2 : forall {A} `{VAB : varsable A var} (l l' : list A) uf v,
   UF_in_cond uf l ->
   RBT.MapsTo v l' (eqnlist2RBT_rbt l uf) ->
   sublist l' l.
  Proof.
   induction l;repeat intro.
   simpl in H.
   assert (RBT.Empty (emptyRBT (list A))).
    apply RBT.empty_spec.
   spec H2 v l'. contradiction.
   simpl in H0.
   generalize (list_eq_dec e_eq_dec (vars a) nil);intro.
   rewrite UF_in_cond_prop1 in H. destruct H.
   unfold eqnlist2RBT_rbt in H0.
   rewrite eqnlist2RBT_step_rewrite in H0.
   (*a is in list*)
   destruct H2. 
   rewrite add_equation2RBT_spec4 in H0;trivial.
   spec IHl l' uf v H3 H0.
   right. apply IHl. trivial.
   (*a is in rbt*)
   generalize (find_var_v_spec1 _ _ H n);intro.
   destruct H2. 
   generalize (e_eq_dec v x);intro.
   destruct H4.
   (*Same principle element*)
   subst x.
   assert (l' = a :: find_list_rbt v (get_rbt (eqnlist2RBT l uf))).
    eapply RBT.MapsTo_spec2. apply H0. apply add_equation2RBT_spec1;trivial.
   rewrite H4 in *.
   destruct H1. subst a. left;trivial.
   apply add_equation2RBT_spec6 in H0;trivial.
   spec IHl (find_list_rbt v (get_rbt (eqnlist2RBT l uf))) uf v H3 H0.
   right. apply IHl. trivial.
   intro. rewrite H5 in H1. inv H1.
   (*Different priciple elements*)
   generalize (add_equation2RBT_spec2 _ _ _ (eqnlist2RBT_rbt l uf) _ (eqnlist2RBT_l l uf) l' H2 n0);intro.
   rewrite H4 in H0.
   spec IHl l' uf v H3 H0.
   right. apply IHl;trivial.
  Qed.

  Lemma list2RBT_spec3: forall {A} `{VAB : varsable A var} (l : list A) eqn uf,
   UF_in_cond uf l -> 
   ((In eqn l /\ vars eqn = nil) <-> In eqn (eqnlist2RBT_l l uf)).
  Proof with try tauto.
   induction l;intros.
   simpl. tauto.
   rewrite UF_in_cond_prop1 in H. destruct H.
   spec IHl eqn uf H0. destruct IHl.
   simpl.
   unfold eqnlist2RBT_l. rewrite eqnlist2RBT_step_rewrite.
   generalize (list_eq_dec e_eq_dec (vars a) nil);intro.
   destruct H3.
   (*a is in list*)
   rewrite add_equation2RBT_spec4;trivial.
   simpl. split;intros... destruct H3... subst...
   (*a is in rbt*)
   apply find_var_v_spec1 in H;trivial.
   destruct H.
   remember (add_equation2RBT a uf (eqnlist2RBT_rbt l uf) (eqnlist2RBT_l l uf)).
   icase p. apply add_equation2RBT_rewrite in Heqp.
   destruct Heqp;subst.
   rewrite add_equation2RBT_spec3 with (v:=x);trivial.
   split;intros... destruct H3. destruct H3... subst...
  Qed.

  Lemma list2RBT_spec4: forall {A} `{VAB : varsable A var} (l l' :list A) uf eqn v,
   UF_in_cond uf l ->
   RBT.MapsTo v l' (eqnlist2RBT_rbt l uf) ->
   In eqn l' ->
   find_var_v uf eqn = Some v.
  Proof.
   induction l;intros. 
   simpl in H0. 
   assert (RBT.Empty (emptyRBT (list A))).
    apply RBT.empty_spec.
   spec H2 v l'. contradiction.
   simpl in H0. rewrite UF_in_cond_prop1 in H.
   destruct H.
   generalize (list_eq_dec e_eq_dec (vars a) nil);intro.
   unfold eqnlist2RBT_rbt in H0.
   rewrite eqnlist2RBT_step_rewrite in H0.
   destruct H3.
   rewrite add_equation2RBT_spec4 in H0;trivial.
   apply IHl with l';trivial.
   apply find_var_v_spec1 in H;trivial.
   destruct H.
   generalize (e_eq_dec v x);intro.
   destruct H3. subst x.
   assert ( l' = a::(find_list_rbt v (get_rbt (eqnlist2RBT l uf)))).
    eapply RBT.MapsTo_spec2. apply H0. apply add_equation2RBT_spec1;trivial.
   rewrite H3 in *.
   destruct H1. subst a. trivial.
   eapply IHl;trivial.
   eapply add_equation2RBT_spec6. apply H.
   assert (find_list_rbt v (get_rbt (eqnlist2RBT l uf)) <> nil).
    intro. rewrite H4 in H1. inversion H1.
   apply H4. apply H0. apply H1.
   remember (add_equation2RBT a uf (eqnlist2RBT_rbt l uf) (eqnlist2RBT_l l uf)).
   icase p. apply add_equation2RBT_rewrite in Heqp.
   destruct Heqp;subst. simpl in H0.
   rewrite add_equation2RBT_spec2 in H0;trivial.
   eapply IHl;trivial. apply H0. apply H1. apply H. apply n0.
  Qed.  

  Lemma list2RBT_spec5: forall {A} `{VAB : varsable A var} (l l' : list A) v uf,
   UF_in_cond uf l ->
   RBT.MapsTo v l' (eqnlist2RBT_rbt l uf) ->
   vars l' <> nil.
  Proof.
   induction l;intros.
   simpl in H0.
   unfold eqnlist2RBT_rbt in H0. simpl in H0.
   assert (RBT.Empty (emptyRBT (list A))).
    apply RBT.empty_spec.
   spec H1 v l'. contradiction.
   rewrite UF_in_cond_prop1 in H.
   destruct H.
   simpl in H0.
   unfold eqnlist2RBT_rbt in H0.
   rewrite eqnlist2RBT_step_rewrite in H0.
   generalize (list_eq_dec e_eq_dec (vars a) nil);intro.
   destruct H2.
   rewrite add_equation2RBT_spec4 in H0;trivial.
   eapply IHl. apply H1. apply H0.
   eapply find_var_v_spec1 in n;try apply H.
   destruct n.
   generalize (e_eq_dec v x);intro.
   destruct H3. subst x.
   assert (l' = a::(find_list_rbt v (get_rbt (eqnlist2RBT l uf)))).
    eapply RBT.MapsTo_spec2. apply H0. apply add_equation2RBT_spec1;trivial.
   intro. rewrite H3 in H4. simpl in H4.
   apply app_eq_nil in H4. destruct H4.
   unfold find_var_v,find_var in H2.
   unfold var in *. unfold t in *;rewrite H4 in H2. inversion H2.
   remember (add_equation2RBT a uf (eqnlist2RBT_rbt l uf) (eqnlist2RBT_l l uf)).
   icase p. apply add_equation2RBT_rewrite in Heqp.
   destruct Heqp;subst. simpl in H0.
   rewrite add_equation2RBT_spec2 in H0.
   eapply IHl. apply H1. apply H0.
   apply H2. apply n.
  Qed.

  Lemma list2RBT_spec6: forall {A} `{VAB : varsable A var} (l : list A) l1 l2 v1 v2 uf,
   UF_lcomponents_cond uf l ->
   RBT.MapsTo v1 l1 (eqnlist2RBT_rbt l uf) ->
   RBT.MapsTo v2 l2 (eqnlist2RBT_rbt l uf) ->
   (v1 <> v2 <-> disjoint (vars l1) (vars l2)).
  Proof.
   intros. split;repeat intro.
   destruct H3.
   copy H. apply UF_lcomponents_cond_prop3 in H5.
   copy H0. copy H1.
   apply list2RBT_spec2 in H0;trivial.
   apply list2RBT_spec2 in H1;trivial.
   apply var_list_exist in H3.
   apply var_list_exist in H4.
   destruct H3 as [? [? ?]]. destruct H4 as [? [? ?]].
   apply list2RBT_spec4 with (eqn:= x0) in H6;trivial.
   apply list2RBT_spec4 with (eqn:= x1) in H7;trivial.
   generalize (H x0 (H0 _ H3));intro.
   generalize (H x1 (H1 _ H4));intro.
   unfold UF_component_cond in *.
   detach H11. detach H10.
   destruct H11;destruct H10.
   unfold find_var_v,find_var in *.
   remember (vars x0). icase l0.
   remember (vars x1). icase l3.
   generalize (H10 x H8);intro.
   generalize (H11 x H9);intro.
   generalize (H11 v0);intro. detach H14.
   generalize (H10 v);intro. detach H15.
   unfold UF.find_e in *. unfold var in *. unfold t in *;congruence.
   left;trivial. left;trivial.
   intro. rewrite H10 in H8. inversion H8.
   intro. rewrite H11 in H9. inversion H9.
   (*The other direction*)
   subst v2.
   assert (l1 = l2).
    eapply RBT.MapsTo_spec2. apply H0. apply H1.
   subst l2.
   apply list2RBT_spec5 in H1. 
   icase (vars l1). spec H2 v. apply H2.
   split;left;trivial.
   apply UF_lcomponents_cond_prop3;trivial.
  Qed.

  Lemma list2RBT_spec7: forall {A} `{VAB : varsable A var} (l : list A) uf,
   UF_in_cond uf l ->
   vars (eqnlist2RBT_l l uf) = nil.
  Proof.
   intros.
   assert (forall eqn, In eqn (eqnlist2RBT_l l uf) -> vars eqn = nil).
    intros.
    generalize (list2RBT_spec3 l  eqn uf);intro.
    apply H1;trivial.
   remember (eqnlist2RBT_l l uf). clear Heql0 H.
   induction l0. trivial.
   simpl. simpl in IHl0;rewrite IHl0.
   rewrite H0. trivial.
   left;trivial.
   intros. apply H0. right;trivial.
  Qed.


  (*Other Lemmas section*)
  
  Lemma InA_Kvpeq_In: forall {A : Type} l k (val : A),
   InA RBT.Kvpeq (k,val) l <-> In (k,val) l.
  Proof.
   induction l;intros. simpl.
   apply InA_nil.
   simpl.
   rewrite InA_cons.
   split;intro. 
   destruct H. left.
   destruct a. compute in H. 
   destruct H;subst;trivial.
   right. apply IHl;trivial.
   destruct H. subst.
   left. compute. tauto.
   right. apply IHl;trivial.
  Qed.

  Lemma NoDupA_Kvpeq_NoDup: forall {A: Type} (l :list (var*A)),
   NoDupA RBT.Kvpeq l <-> NoDup l.
  Proof.
   induction l;intros.
   split;intros. apply NoDup_nil.
   apply NoDupA_nil.
   split;intros.
   inv H.
   apply NoDup_cons.
   intro. apply H2. destruct a. apply InA_Kvpeq_In;trivial.
   apply IHl;trivial.
   inv H.
   apply NoDupA_cons.
   intro. apply H2. destruct a. apply InA_Kvpeq_In;trivial.
   apply IHl;trivial.
  Qed.

  Lemma RBT_elements_diff: forall {A : Type} (rbt : RBT.map_of A) i j v v' a a',
   nth_op i (RBT.elements rbt) = Some (v,a) ->
   nth_op j (RBT.elements rbt) = Some (v',a') ->
   (i <> j <-> v <> v').
  Proof.
   intros.
   assert (InA RBT.Kvpeq (v,a) (RBT.elements rbt)).
    apply InA_Kvpeq_In. apply nth_op_In. exists i;trivial.
   assert (InA RBT.Kvpeq (v',a') (RBT.elements rbt)).
    apply InA_Kvpeq_In. apply nth_op_In. exists j;trivial.
   copy H1;copy H2.
   apply RBT.elements_spec1 in H1.
   apply RBT.elements_spec1 in H2.
   generalize (RBT.elements_spec3 rbt);intro.
   apply NoDupA_Kvpeq_NoDup in H5.
   apply InA_Kvpeq_In in H3.
   apply InA_Kvpeq_In in H4.
   generalize (NoDup_nth_op_diff _ _ _ _ _ H5 H H0);intro.
   split;repeat intro;subst.
   apply H6 in H7. apply H7. f_equal.
   eapply RBT.MapsTo_spec2.
   apply H1. apply H2.
   rewrite H0 in H. inv H. tauto.
  Qed.
   
  Lemma remove_1st_spec2: forall {A: Type} (rbt : RBT.map_of (list A)) l,
   (In l (remove_1st (RBT.elements rbt)) <-> 
   exists v, RBT.MapsTo v l rbt).
  Proof.
   intros.
   rewrite remove_1st_spec1.
   split;intros. destruct H.
   exists x. apply RBT.elements_spec1.
   apply InA_Kvpeq_In;trivial.
   destruct H. exists x.
   apply InA_Kvpeq_In.
   apply RBT.elements_spec1;trivial.
  Qed.

End Internal_Structures.                