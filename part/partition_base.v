Require Import List.
Require Import base.
Require Import partition_interface.

Definition remove_1st {A B : Type}(l : list (A*B)%type) : list B :=
  map (fun (e : (A*B)%type) => snd e) l.

  Lemma remove_1st_nth_op: forall {A B : Type} l (b:B) i,
   nth_op i (remove_1st l) = Some b <-> exists (a:A), nth_op i l = Some (a,b).
  Proof.
   induction l;intros;simpl;
   split;intros.
   icase i. destruct H. icase i.
   icase i;inv H; simpl.
   exists (fst a). destruct a;trivial.
   apply IHl;trivial.
   destruct H;icase i;inv H;simpl.
   trivial. apply IHl. exists x;trivial.
  Qed.

  Lemma remove_1st_spec1: forall {A B : Type} l (b : B),
   In b (remove_1st l) <-> exists (a : A), In (a,b) l.
  Proof.
   induction l;intros. firstorder.
   simpl.
   split;intros. destruct H.
   exists (fst a). left. destruct a. simpl in *.
   congruence.
   icase l.
   apply IHl in H. destruct H.
   exists x. right;trivial.
   destruct H. destruct H.
   left;rewrite H;trivial.
   icase l.
   right. apply IHl.
   exists x;apply H.
  Qed.
 
  Lemma nth_op_In: forall {A : Type} (l : list A) a,
   In a l <-> exists i , nth_op i l = Some a.
  Proof.
   induction l;intros. simpl.
   split;intros. tauto.
   destruct H. icase x.
   simpl. split;intros.
   destruct H. subst.
   exists 0. simpl. trivial.
   apply IHl in H. destruct H.
   exists (S x);simpl. trivial.
   destruct H. icase x;inv H.
   left;trivial.
   right. apply IHl. exists x;trivial.
  Qed.

  Lemma NoDup_nth_op_diff: forall {A : Type} l (a:A) a' i j,
   NoDup l -> nth_op i l = Some a -> nth_op j l = Some a' ->
   (i <> j <-> a <> a').
  Proof.
   induction l;intros.
   icase i.
   inv H.
   icase i;icase j;inv H0;inv H1.
   tauto. split;intros;try omega.
   intro. apply H4. subst.
   apply nth_op_In. exists j;trivial.
   split;intros;try omega.
   intro. apply H4. subst.
   apply nth_op_In. exists i;trivial.
   spec IHl a0 a' i j H5 H2 H0.
   split;intro.
   apply IHl;omega.
   apply IHl in H. omega.
  Qed.

  Lemma nth_op_equiv: forall {A : Type} l (d : A) i a,
  (nth i l d = a /\ i < length l )<-> nth_op i l = Some a.
  Proof. 
   induction l;intros. simpl.
   icase i;simpl.
   split;intros.
   destruct H;omega.
   inversion H.
   split;intros.
   destruct H;omega.
   inversion H.
   icase i;simpl. 
   split;intros. destruct H;subst;trivial.
   inversion H;split;trivial.
   omega.
   split;intros.
   destruct H. rewrite<- IHl.
   split. apply H. omega.
   rewrite<- IHl in H. destruct H.
   split. apply H. omega.
  Qed.

  Lemma disjoint_nil: forall {A : Type} (l :list A),
   disjoint nil l.
  Proof.
   firstorder.
  Qed.

  Lemma disjoint_comm: forall {A : Type} (l1 l2 : list A),
   disjoint l1 l2 -> disjoint l2 l1.
  Proof.
   unfold disjoint. firstorder. 
  Qed.

  Lemma disjoint_app_iff: forall {A : Type}(l l1 l2: list A),
   disjoint l (l1++l2) <-> disjoint l l1 /\ disjoint l l2.
  Proof.
   unfold disjoint. intros.
   firstorder.
   rewrite in_app_iff.
   firstorder.
  Qed.

  Lemma disjoint_in: forall {A : Type} (l1 l2 : list A) (a : A),
   disjoint l1 l2 -> In a l1 -> ~In a l2.
  Proof.
   firstorder.
  Qed. 

  Lemma sublist_nil: forall {A : Type} (l : list A),
  sublist l nil -> l = nil.
  Proof.
   induction l;intros. trivial.
   spec H a. detach H. inversion H.
   left;trivial.
  Qed.

  Lemma sublist_app_iff: forall {A : Type} (l l1 l2 : list A),
  sublist (l1++l2) l <-> sublist l1 l /\ sublist l2 l.
  Proof.
   intros.
   unfold sublist.
   split;intros.
   split;intros e H1;spec H e; rewrite in_app_iff in H;tauto.
   destruct H.
   rewrite in_app_iff in H0.
   firstorder.
  Qed.

  Open Scope part_scope.

  Lemma list_eval_rewrite: forall {A B : Type} `{Ev : evalable A B} (l : list B) (ctx : A),
  ctx |= l <-> forall e, In e l -> ctx |= e.
  Proof.
   induction l;intros.
   simpl. tauto.
   split;intros.
   destruct H.
   icase H0. subst a. trivial.
   simpl in IHl;rewrite IHl in H.
   apply H;trivial.
   split.
   apply IHl.
   intros. apply H.
   right;trivial.
   apply H.
   left;trivial.
  Qed.

  Lemma sublist_eval: forall {A B : Type} `{Ev : evalable A B} (l l' : list B) (ctx : A),
   sublist l l' -> ctx |= l' -> ctx |= l.
  Proof. 
   induction l;intros.
   simpl;trivial.
   split.
   simpl in IHl;apply IHl with l';trivial.
   unfold sublist in *.
   intros.
   apply H. right;trivial.
   rewrite list_eval_rewrite in H0.
   apply H0.
   unfold sublist in H.
   apply H. left;trivial.
  Qed.

  Close Scope part_scope.
  
  Lemma sublist_vars : forall {A B: Type} `{varsable A B} (l : list A) (e : A),
   In e l ->
   sublist (vars e) (vars l).
  Proof.
   induction l;intros.
   inversion H0.
   repeat intro.
   simpl.
   rewrite in_app_iff.
   destruct H0. subst.
   left;trivial.
   spec IHl e H0 e0 H1.
   right;trivial.
  Qed.

  Lemma sublist_disjoint: forall {A : Type} (l1 l2 l3 : list A),
  sublist l1 l2 ->
  disjoint l2 l3 ->
  disjoint l1 l3.
  Proof.
   repeat intro.
   spec H0 x.
   spec H x.
   tauto.
  Qed.

  Lemma nth_app_reduce: forall {A : Type} (l1 l2 : list A) i d,
  nth (length l1 + i) (l1 ++ l2) d = nth i l2 d.
  Proof.
   intros.
   assert (length l1 <= length l1 + i) by omega.
   apply app_nth2 with (l':=l2) (d:=d)in H.
   assert (length l1 + i - length l1 = i) by omega.
   rewrite H0 in H.
   trivial.
  Qed.

  Lemma disjoint_pwise_step_rewrite: forall {A : Type} (L : list (list A)) l,
  disjoint_pwise (l::L) <->
  (forall l', In l' L -> disjoint l l') /\ disjoint_pwise L.
  Proof.
   intros.
   split;intros.
   split;intros.
   apply in_split in H0.
   destruct H0 as [? [? ?]].
   spec H l l' 0 (S (length x)).
   apply H.
   omega.
   simpl;trivial.
   simpl. rewrite H0.
   apply nth_op_equiv with l'.
   assert (length x >= length x) by omega.
   generalize (app_nth2 x (l'::x0) l' H1);intro.
   rewrite H2. split.
   assert (length x -length x = 0) by omega.
   rewrite H3;trivial.
   rewrite app_length. simpl. omega.
   do 7 intro.
   spec H l0 l' (S i) (S j). simpl in H.
   apply H;trivial.
   omega.
   destruct H.
   do 7 intro.
   icase i;icase j;simpl in *. omega.
   inv H2.
   apply H;trivial.
   apply nth_op_equiv with (d:=l') in H3. destruct H3.
   apply nth_In with (d:=l')in H3.
   rewrite H2 in H3. apply H3.
   inv H3. apply disjoint_comm.
   apply H.
   apply nth_op_equiv with (d:=l0)in H2. destruct H2.
   apply nth_In with (d:=l0) in H3.
   rewrite H2 in H3. apply H3.
   spec H0 l0 l' i j.
   apply H0;trivial. omega.
  Qed.

  Lemma disjoint_pwise_equiv: forall {A : Type} (L : list (list A)),
  disjoint_pwise L <-> disjoint_pwise_fun L.
  Proof.
   induction L;intros.
   simpl.
   split;intros.
   simpl. trivial.
   unfold disjoint_pwise. intros.
   unfold disjoint. simpl.
   icase i;icase j;tauto.

   rewrite disjoint_pwise_step_rewrite.
   simpl. split;intros.
   split;intros.
   apply H;trivial.
   apply IHL. apply H.
   split;intros.
   apply H;trivial.
   apply IHL. apply H.
  Qed.
 
  Lemma disjoint_pwise_app_comm: forall {A : Type }(l1 l2 : list (list A)),
  disjoint_pwise (l1++l2) ->
  disjoint_pwise (l2++l1).
  Proof.
   intros A l1 l2.
   repeat rewrite disjoint_pwise_equiv.
   revert l2. induction l1. intros.
   induction l2;intros.
   simpl;trivial.
   simpl in H. destruct H.
   split. intros.
   apply H. rewrite app_nil_r in H1. trivial.
   apply IHl2. simpl. trivial.

   intros.
   destruct H.
   apply IHl1 in H0.
   clear IHl1.
   revert H0 H. revert a l1.
   induction l2;intros.
   simpl in *. split;intros;trivial.
   apply H. apply in_app_iff. left;trivial.
   destruct H0.
   split;intros.
   rewrite in_app_iff in H2.
   destruct H2.
   apply H0. rewrite in_app_iff;left;trivial.
   destruct H2. subst a0.
   spec H a. apply disjoint_comm. apply H.
   rewrite in_app_iff;right;left;trivial.
   apply H0;rewrite in_app_iff;right;trivial.
   apply IHl2;trivial.
   intros.
   apply H.
   rewrite in_app_iff. rewrite in_app_iff in H2. 
   destruct H2. left;trivial.
   right;right;trivial.
  Qed.

  Lemma var_list_extract_app: forall {A B: Type} `{varsable A B} (l1 l2 : list A),
  var_list_extract (l1++l2) = var_list_extract l1 ++ var_list_extract l2.
  Proof.
   induction l1;intros.
   simpl;trivial.
   spec IHl1 l2.
   simpl.
   rewrite IHl1;trivial.
  Qed.

  Lemma var_list_extract_length_eq: forall {A B: Type} `{varsable A B} (l : list A),
  length (var_list_extract l) = length l.
  Proof.
   induction l;intros.
   simpl;trivial.
   simpl. omega.
  Qed.

  Lemma var_list_exist: forall {A B : Type} `{VAB : varsable A B} (l : list A) b,
  In b (vars l) ->
  exists a, In a l /\ In b (vars a).
  Proof.
   induction l;intros.
   inversion H.
   simpl in H. rewrite in_app_iff in H.
   destruct H.
   exists a. split;trivial. left;trivial.
   spec IHl b H. destruct IHl as [? [? ?]].
   exists x. split;trivial. right;trivial.
  Qed.

  Lemma var_list_extract_nth_op: forall {A B: Type} `{VAB: varsable A B} 
  (L : list A) l i,
  nth_op i (var_list_extract L) = Some l <-> 
  exists l', nth_op i L = Some l' /\ vars l' = l.
  Proof.
   induction L;intros.
   simpl. split;intros.
   icase i.
   destruct H as [? [? ?]]. icase i.
   icase i;simpl.
   split;intros. inv H. exists a. tauto.
   destruct H as [? [? ?]]. inv H. trivial.
   apply IHL.
  Qed.

  Lemma vars_app_rewrite : forall {A B: Type} (VAB : varsable A B)(l1 l2 : list A),
   vars (l1++l2) = (vars l1) ++ (vars l2).
  Proof.
   induction l1;intros;simpl;trivial.
   simpl in IHl1;rewrite IHl1.
   apply app_assoc.
  Qed.

  Lemma sublist_listvars: forall {A B : Type} `{VAB : varsable A B}
                          (l1 l2 : list A),
   sublist l1 l2 -> sublist (vars l1) (vars l2).
  Proof.
   induction l1;repeat intro. inv H0.
   simpl in H0.
   rewrite in_app_iff in H0. destruct H0.
   spec H a. detach H.
   apply sublist_vars in H.
   apply H. trivial.
   left;trivial.
   apply IHl1;trivial. repeat intro.
   spec H e0. apply H. right. trivial.
  Qed.

  Lemma disjoint_pwise_case: forall {A : Type}L (l1 l2 : list A),
   disjoint_pwise L -> In l1 L -> In l2 L ->
   l1 = l2 \/ disjoint l1 l2.
  Proof. 
    induction L;intros. inv H0.
    rewrite disjoint_pwise_equiv in H.
    destruct H.
    destruct H0;destruct H1; subst.
    left;trivial.
    right. apply H;trivial.
    right. apply disjoint_comm;apply H;trivial.
    apply IHL;trivial.
    apply disjoint_pwise_equiv;trivial.
  Qed.

  Lemma In_split_length_eq: forall {A B: Type} (l: list A) (l' : list B) (e: A),
   length l = length l' ->
   In e l ->
   exists l1 l2 l3 l4 e',
   l = l1++e::l2 /\ l' = l3++e'::l4 /\ 
   length l1 = length l3 /\ length l2 = length l4.
  Proof.
   induction l;intros.
   inv H0.
   icase l'.
   inv H.
   icase H0.
   subst a.
   exists nil. exists l.
   exists nil. exists l'.
   exists b.
   simpl.
   tauto.
   spec IHl l' e H2 H.
   destruct IHl as [l1 [l2 [l3 [l4 [e' [H3 [H4 [H5 H6]]]]]]]].
   subst.
   exists (a::l1). exists l2.
   exists (b::l3). exists l4.
   exists e'.
   simpl;split;try tauto.
   split;try tauto.
   split;trivial.
   omega.
  Qed.

