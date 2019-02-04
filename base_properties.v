Require Import msl.msl_standard.
Require Import base.
Require Import share_dec_base.

 Definition sublist `{t : Type} (l l' : list t) : Prop :=
  forall e, In e l -> In e l'.

 Definition disjoint {A : Type} (L1 L2 : list A) : Prop :=
  forall x, ~(In x L1 /\ In x L2).

 Fixpoint nth_op {A : Type} (i : nat) (l : list A): option A :=
  match l with
  | nil => None
  | a::l' => match i with
             | 0 => Some a
             | S n => nth_op n l' 
             end
  end.

 Definition disjoint_pwise {A : Type} (L : list (list A)) : Prop :=
  forall l l' i j, i <> j -> nth_op i L = Some l -> nth_op j L = Some l' -> disjoint l l'.

 Fixpoint disjoint_pwise_fun {A : Type} (L : list (list A)) : Prop :=
  match L with
  | nil => True
  | l::L' => (forall l', In l' L' -> disjoint l l') /\ disjoint_pwise_fun L'
  end. 

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

 Lemma max_zero: forall a b, max a b = 0 <-> (a = 0 /\ b = 0).
 Proof.
  intros.
  split;intros.
  generalize (Max.le_max_l a b);intro.
  generalize (Max.le_max_r a b);intro.
  omega.
  destruct H;subst;trivial.
 Qed.

 Lemma sublist_trans: forall {A} (l1 l2 l3 : list A),
  sublist l1 l2 -> sublist l2 l3 -> sublist l1 l3.
 Proof. firstorder. Qed.

 Lemma max_nonzero : forall n m,
 max n m <> 0 <-> n  <> 0 \/ m <> 0. 
 Proof with tauto.
  intros.
  split;intros.
  icase n. icase n. icase m. omega. 
  simpl. icase m;omega.
 Qed.

 Lemma exist_lt: forall n, exists m, n < m.
 Proof. intros. exists (S n). omega. Qed.

 Lemma exists_le: forall n, exists m, le n m.
 Proof. intros. exists n. omega. Qed.

 Lemma nat_acc: forall i j,
  i <> j -> exists n, i = j + S n \/ j = i + S n.
 Proof with try tauto.
  induction i;intros.
  icase j. omega.
  exists j...
  icase j. exists i...
  spec IHi j. spec IHi. omega.
  destruct IHi. exists x. omega.
 Qed. 

 Lemma le_exist: forall n n',
  n <= n' ->
  exists k, n' = n + k.
  Proof with try tauto. 
   induction n;intros.
   exists n'...
   icase n'. omega.
   spec IHn n'. spec IHn. omega.
   destruct IHn. exists x. omega.
  Qed.

 Lemma NoDup_length {A}: forall (l1 l2 : list A),
  NoDup l1 -> NoDup l2 -> sublist l1 l2 ->
  length l1 <= length l2.
 Proof with try tauto. 
  induction l1;intros. simpl. omega.
  assert (List.In a l2).
   apply H1. left...
  apply In_split in H2.
  destruct H2 as [lh [lt H2]]. subst.
  rewrite app_length. simpl.
  apply NoDup_remove_1 in H0. inv H. 
  assert (sublist l1 (lh++lt)).
   repeat intro.
   spec H1 e. spec H1. right...
   rewrite in_app_iff in *.
   destruct H1... destruct H1;subst...
  spec IHl1 (lh++lt) H5 H0 H. 
  rewrite app_length in IHl1;omega.
 Qed.

 Lemma nth_op_NoDup {A}: forall (l : list A),
  NoDup l <-> 
  (forall i j a a', i <> j -> 
   nth_op i l = Some a -> nth_op j l = Some a' -> a <> a'). 
 Proof with try tauto.
  intros.
  split;intros.
  eapply NoDup_nth_op_diff;eauto.
  induction l;intros. apply NoDup_nil.
  apply NoDup_cons. intro.
  apply nth_op_In in H0. destruct H0 as [i H0].
  spec H 0 (S i) a a.
  eapply H... omega.
  apply IHl. intros.
  apply H with (i:=S i) (j:=S j);eauto.
 Qed.

 Lemma NoDup_app: forall {A} (l1 l2 : list A),
  NoDup (l1++l2) -> NoDup l1 /\ NoDup l2.
 Proof with try tauto.
  induction l1;simpl;intros... split... apply NoDup_nil.
  inv H. apply IHl1 in H3. split...
  apply NoDup_cons... intro. apply H2.
  rewrite in_app_iff...
 Qed.

 Lemma NoDup_comm: forall {A} (l1 l2 : list A),
  NoDup (l1++l2) -> NoDup (l2++l1).
 Proof with try tauto.
  induction l1;simpl;intros...
  rewrite app_nil_r...
  inv H. apply IHl1 in H3.
  revert H3 H2. clear IHl1.
  revert a l1. induction l2;simpl;intros.
  apply NoDup_cons... rewrite app_nil_r in H2...
  inv H3. apply NoDup_cons.
  rewrite in_app_iff in *;simpl in *.
  intro. destruct H. apply H1... destruct H;subst...
  apply IHl2... intro. apply H2. 
  rewrite in_app_iff in *... simpl...
 Qed.

 Lemma not_disjoint_case: forall {A} `{EqDec A} (l : list A) l',
  ~disjoint l l'->
  exists d l1 l2, l = l1++(d::l2) /\ List.In d l' /\ disjoint l1 l'.
 Proof with try tauto.
  induction l;intros.
  elimtype False. apply H0. repeat intro...
  destruct (in_dec H a l').
  exists a,nil,l. simpl. split... split... intro...
  assert (~disjoint l l').
   intro. apply H0. repeat intro.
   destruct H2. destruct H2;subst...
   spec H1 x...
  apply IHl in H1. destruct H1 as [? [? [? [? [? ?]]]]].
  subst. exists x,(a::x0),x1. split... split...
  repeat intro. simpl in H1. spec H3 x2.
  destruct H1. destruct H1;subst...
 Qed.


 Definition var_list_extract {A B: Type} `{varsable A B} (l : list A) :
  list (list B) := map (fun e => vars e) l.

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

 Lemma override_reduce {A} {B} `{EqDec A}: forall (ctx : A->B) ctx' l,
  [l => ctx'] ([l => ctx'] ctx) = [l => ctx'] ctx.
 Proof with try tauto.
  intros. extensionality v.
  destruct (in_dec eq_dec v l).
  repeat rewrite override_in...
  repeat rewrite override_not_in...
 Qed.

 Lemma disjoint_override_comm: forall {A B : Type} `{Eq: EqDec A} l1 l2 (ctx : A -> B) ctx1 ctx2,
  disjoint l1 l2 ->
  [l2=>ctx2]([l1 => ctx1] ctx) = [l1=>ctx1]([l2=>ctx2] ctx).
 Proof.
   induction l1;intros.
   simpl;trivial.
   simpl.
   assert (~In a l2) by firstorder. 
   assert (disjoint l1 l2) by firstorder. 
   spec IHl1 l2 ctx ctx1 ctx2 H1.
   rewrite<- IHl1.
   apply override_absorb_not_in.
   trivial.
 Qed.

Module ClassicalProps.

 Require Import Classical.

 Lemma neg_impl: forall (P Q : Prop),
  (~(P -> Q)) <-> P /\ ~Q.
 Proof. intros. tauto. Qed.
 Lemma neg_ex: forall (A : Type) (P : A -> Prop),
  (~exists x, P x) <-> forall x, ~P x.
 Proof. intros. firstorder. Qed.
 Lemma neg_forall: forall (A : Type) (P : A -> Prop), 
 ((~forall x, P x) <-> exists x,~P x).
 Proof with try tauto.
  intros. firstorder.
  icase (classic (exists x : A, ~P x)).
  elimtype False. apply H. intro.
  icase (classic (P x)).
  elimtype False. apply H0. exists x...
 Qed.
 Lemma or_equiv: forall P Q,
  P \/ Q <-> ~(~P /\ ~Q).
 Proof. intros. tauto. Qed.
 Lemma neg_or: forall P Q,
  ~(P \/ Q) <-> ~P /\ ~Q.
 Proof. intros. tauto. Qed.
 Lemma neg_equiv: forall P Q,
  (P <-> Q) <-> (~P <->~Q).
 Proof. intros. tauto. Qed.

End ClassicalProps.


