Add LoadPath "..".
Require Import List.
Require Import Classical.
Require Import base.
Require Import rbt.MMapRBT.
Require Import rbt.MMapInterface.
Require Import UF_interface.

Module Union_Find_Base (Import Input : INPUT) 
                       (Import ot : OrderedType with Definition t := Input.e
                                                with Definition eq := @Logic.eq Input.e).

 Module RBT := Make ot.
 Import RBT.

 (*
  SECTION 0 : Useful definitions and functions
 *)

 Class EqDec (A : Type) : Type := 
  eq_dec : forall a a' : A, {a = a'} + {a <> a'}.

 Definition sublist `{t : Type} (l l' : list t) : Prop :=
  forall e, List.In e l -> List.In e l'.

 Definition disjoint {A : Type} (L1 L2 : list A) : Prop :=
  forall x, ~(List.In x L1 /\ List.In x L2).

 Fixpoint nth_op {A : Type} (i : nat) (l : list A): option A :=
  match l with
  | nil => None
  | a::l' => match i with
             | 0 => Some a
             | S n => nth_op n l' 
             end
  end.

  Lemma nth_op_In: forall {A : Type} (l : list A) a,
   List.In a l <-> exists i , nth_op i l = Some a.
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
   disjoint l1 l2 -> List.In a l1 -> ~List.In a l2.
  Proof.
   firstorder.
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
   spec H1 e0. spec H1. right...
   rewrite in_app_iff in *.
   destruct H1... destruct H1;subst...
  spec IHl1 (lh++lt) H5 H0 H. 
  rewrite app_length in IHl1;omega.
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


 (*
  SECTION 1: Define heap, reachable and some basic properties
 *)

 Inductive pointer : Type :=
 |null    : pointer
 |addr    : t -> pointer.

 Instance pointer_dec: EqDec pointer.
 Proof with try tauto.
  repeat intro.
  icase a;icase a'.
  right;intro;disc.
  right;intro;disc.
  destruct (e_eq_dec t0 t1);subst...
  right;intro H;inv H;apply n...
 Defined.
  
 Record heap_node : Type := Heap_node {
  pt : pointer;
  size : nat
 }.

 Definition fresh_node := Heap_node null 0.

 Definition heap : Type := map_of heap_node.

 Definition check_root d hp :=
  match find d hp with
  |Some hn => match pt hn with null => true | _ => false end
  |_ => false
  end.

 Definition is_root := fun r hp =>
  exists hn, find r hp = Some hn /\ pt hn = null.

 Inductive reachable : heap -> t -> nat -> t -> Prop :=
 |zero_step: forall hp d, In d hp -> reachable hp d 0 d
 |succ_step: forall hp d d' d'' n hn, 
             find d hp = Some hn -> pt hn = addr d' -> 
             reachable hp d' n d'' -> 
             reachable hp d (S n) d''.
 Hint Constructors reachable.

 Lemma In_dec: forall {A} (hp : @map_of A) d,
  In d hp \/ ~In d hp.
 Proof. intros. tauto. Qed.

 Lemma find_In: forall {A} (hp : @map_of A) d,
  In d hp <-> exists hn, find d hp = Some hn.
 Proof with try tauto.
  intros. split;intros.
  destruct H as [hn H].
  exists hn. apply find_spec...
  destruct H. apply find_spec in H.
  exists x...
 Qed.

 Lemma find_add_id: forall {A} (hp : @map_of A) d hn,
  find d (add d hn hp) = Some hn.
 Proof. 
  intros.
  apply find_spec.
  apply add_spec1.
 Qed.

 Lemma find_not_In: forall {A} (hp : @map_of A) d,
  find d hp = None <-> ~In d hp.
 Proof with try tauto.
  intros. rewrite find_In.
  split;repeat intro. destruct H0;congruence.
  case_eq (find d hp);intros... elimtype False.
  apply H. exists a...
 Qed.

 Lemma find_add_diff: forall {A} (hp : @map_of A) d d' hn,
  d <> d' ->
  find d (add d' hn hp) = find d hp.
 Proof with try tauto. 
  intros.
  case_eq (find d hp);intros.
  rewrite find_spec.
  rewrite find_spec in H0.
  apply add_spec2...
  rewrite find_not_In. rewrite find_not_In in H0.
  intro. apply H0.
  destruct H1 as [hn' H1].
  apply add_spec2 in H1...
  exists hn'...
 Qed.

 Lemma In_add_id: forall {A} (hp : @map_of A) d hn,
  In d (add d hn hp).
 Proof.
  intros.
  exists hn.
  apply add_spec1...
 Qed.

 Lemma In_add_diff: forall {A} (hp : @map_of A) d d' hn,
  d <> d' ->
  (In d (add d' hn hp) <-> In d hp).
 Proof with try tauto.
  intros. repeat rewrite find_In.
  split;intro H1;destruct H1 as [hn' H1];exists hn';
  rewrite<- H1. symmetry.
  apply find_add_diff...
  apply find_add_diff...
 Qed.

 Lemma find_update_id: forall {A} (hp : @map_of A) d hn,
  In d hp ->
  find d (update d hn hp) = Some hn.
 Proof. 
  intros.
  apply find_spec.
  eapply update_spec1 in H;eauto.
 Qed.

 Lemma find_update_diff: forall {A} (hp : @map_of A) d d' hn,
  d' <> d ->
  find d (update d' hn hp) = find d hp.
 Proof with try tauto. 
  intros.
  case_eq (find d hp);intros.
  rewrite find_spec.
  rewrite find_spec in H0.
  apply update_spec3... intro;subst...
  apply find_not_In in H0.
  apply find_not_In. intro. apply H0.
  destruct H1. exists x.
  apply update_spec3 in H1... intro;subst...
 Qed.

 Lemma In_update_equiv: forall {A} (hp : @map_of A) d d' hn,
  In d (update d' hn hp) <-> In d hp. 
 Proof with try tauto.
  intros. repeat rewrite find_In.
  destruct (In_dec hp d').
  destruct (e_eq_dec d d');subst.
  split;intros;destruct H0. apply find_In...
  exists hn. rewrite find_update_id...
  split;intros;destruct H0.
  rewrite find_update_diff in H0. eauto.
  intro;subst... rewrite find_update_diff. eauto.
  intro;subst...
  split;intros;destruct H0 as [hn' H0];exists hn';
  apply find_spec;apply find_spec in H0.
  apply update_spec2 in H0...
  apply update_spec2...
 Qed.

 Lemma InA_keq_In: forall l k,
   InA keq k l <-> List.In k l.
 Proof.
  induction l;intros. simpl.
  apply InA_nil.
  simpl.
  rewrite InA_cons.
  split;intro. 
  destruct H. left.
  compute in H. 
  destruct H;subst;trivial.
  right. apply IHl;trivial.
  destruct H. subst.
  left. compute. tauto.
  right. apply IHl;trivial.
 Qed.

 Lemma NoDupA_keq_NoDup: forall (l :list key),
  NoDupA keq l <-> NoDup l.
 Proof.
  induction l;intros.
  split;intros. apply NoDup_nil.
  apply NoDupA_nil.
  split;intros.
  inv H.
  apply NoDup_cons.
  intro. apply H2. apply InA_keq_In;trivial.
  apply IHl;trivial.
  inv H.
  apply NoDupA_cons.
  intro. apply H2. apply InA_keq_In;trivial.
  apply IHl;trivial.
 Qed.

 Lemma kelements_update : forall {A} (hp : @map_of A) d hn,
  length (kelements (update d hn hp)) = length (kelements hp).
 Proof with try tauto.
  intros.
  generalize (kelements_spec3 hp);intro.
  generalize (kelements_spec3 (update d hn hp));intro.
  apply NoDupA_keq_NoDup in H.
  apply NoDupA_keq_NoDup in H0.
  assert (sublist (kelements hp) (kelements (update d hn hp))).
   repeat intro.
   apply InA_keq_In in H1.
   apply InA_keq_In.
   apply kelements_spec1.
   apply kelements_spec1 in H1.
   apply In_update_equiv...
  assert (sublist (kelements (update d hn hp)) (kelements hp) ).
   repeat intro.
   apply InA_keq_In in H2.
   apply InA_keq_In.
   apply kelements_spec1.
   apply kelements_spec1 in H2.
   apply In_update_equiv in H2...
  apply NoDup_length in H1...
  apply NoDup_length in H2...
  omega.
 Qed.

 Lemma check_root_correct: forall d hp,
  check_root d hp = true <-> is_root d hp.
 Proof with try tauto.
  intros.
  unfold check_root,is_root.
  split.
  case_eq (find d hp);disc.
  intros ? ?. case_eq (pt h);disc.
  intros. exists h...
  intros. destruct H as [? [? ?]].
  rewrite H. rewrite H0...
 Qed.

 Lemma root_In: forall hp d,
  is_root d hp -> In d hp.
 Proof with try tauto.
  intros.
  destruct H as [hn [? ?]].
  apply find_In. exists hn...
 Qed.

 Lemma is_root_dec: forall hp d,
  is_root d hp \/ ~is_root d hp.
 Proof with try tauto.
  intros. unfold is_root.
  case_eq (find d hp);intros.
  case_eq (pt h);intros.
  left. exists h...
  right. intro. destruct H1 as [? [? ?]].
  inv H1. rewrite H0 in H2. inv H2.
  right. intro. destruct H0 as [? [? ?]]. inv H0.
 Qed.

 (*End support*)

 Lemma reachable_det : forall n hp d d' d'',
  reachable hp d n d' -> reachable hp d n d'' -> d' = d''.
 Proof with try tauto.
  induction n;intros.
  inv H. inv H0...
  inv H. inv H0.
  rewrite H2 in H1. inv H1.
  rewrite H4 in H3. inv H3.
  generalize (IHn _ _ _ _ H6 H8);intro...
 Qed.

 Lemma reachable_zero: forall hp d d',
  reachable hp d 0 d' <-> d = d' /\ In d hp.
 Proof with try tauto.
  intros. split;repeat intro.
  inv H...
  destruct H;subst. apply zero_step...
 Qed.

 Lemma reachable_succ: forall n hp d d',
  reachable hp d (S n) d' <-> 
  exists d'' hn, reachable hp d n d'' /\ find d'' hp = Some hn /\ pt hn = addr d' /\ In d' hp.
 Proof with try tauto.
  induction n;intros.
  split;repeat intro.
  inv H.
  exists d,hn.
  rewrite reachable_zero in H5. destruct H5;subst.
  split... rewrite reachable_zero. split...
  rewrite find_In. exists hn...
  destruct H as [d'' [hn [H [H1 H2]]]].
  apply reachable_zero in H. destruct H;subst.
  apply succ_step with (d':=d') (hn:=hn)...
  apply zero_step...

  split;intros.
  inv H. apply IHn in H5.
  destruct H5 as [d'' [hn' [H5 [H6 [H7 H8]]]]].
  exists d'',hn'.
  split... eapply succ_step;eauto.

  destruct H as [d'' [hn [H [H1 [H2 H3]]]]].
  inv H.
  apply succ_step with (hn := hn0) (d' := d'0)...
  eapply IHn;eauto.
  exists d'',hn...
 Qed.

 Lemma reachable_two_ends: forall n hp d d',
  reachable hp d n d' -> In d hp /\ In d' hp.
 Proof with try tauto.
  induction n;intros.
  apply reachable_zero in H. destruct H;subst...
  inv H. apply IHn in H5. split...
  apply find_In. exists hn...
 Qed.

 Lemma reachable_app: forall n1 n2 hp d d',
  reachable hp d (n1+n2) d' <-> exists d'', reachable hp d n1 d'' /\ reachable hp d'' n2 d'.
 Proof with try tauto.
  intros n1 n2. revert n1. 
  induction n2;intros;simpl.
  assert (n1+0 = n1) by omega. rewrite H;clear H.
  split;intros. exists d'.
  split... apply reachable_zero. split...
  apply reachable_two_ends in H...
  destruct H as [d'' [H H1]].
  apply reachable_zero in H1. destruct H1;subst...

  assert (n1 + S n2 = S n1 + n2) by omega.
  rewrite H;clear H. split;intros.

  apply IHn2 in H.
  destruct H as [d'' [H H1]].
  rewrite reachable_succ in H.
  destruct H as [d1 [hn [H2 [H3 [H4 H5]]]]].
  exists d1;split...
  eapply succ_step;eauto.

  destruct H as [d'' [H H1]].
  apply IHn2. inv H1.
  exists d'0. split...
  rewrite reachable_succ.
  exists d'',hn.
  split... split... split...
  apply reachable_two_ends in H6...
 Qed.

 Lemma reachable_add: forall n hp d d' d'',
   ~In d hp -> d'' <> d ->
  (reachable (add d fresh_node hp) d' n d'' <-> reachable hp d' n d'').
 Proof with try tauto.
  induction n;intros.
  split;intros H1;inv H1;apply zero_step.
  rewrite In_add_diff in H2... rewrite In_add_diff...

  split;intros H1;inv H1.
  apply IHn in H7...
  rewrite find_add_diff in H3;eauto.
  intro;subst. rewrite find_add_id in H3. inv H3. inv H4.
  rewrite <-IHn with (d:=d)in H7...
  eapply succ_step;eauto.
  rewrite find_add_diff... intro;subst.
  apply H. apply find_In. exists hn...
 Qed.

 Lemma reachable_root: forall hp d n d',
  is_root d hp ->
  (reachable hp d n d' <-> n = 0 /\ d' = d).
 Proof with try tauto.
  intros.
  destruct H as [hn [H1 H2]].
  split;intros.
  icase n;inv H... congruence.
  destruct H;subst. apply zero_step.
  apply find_In. exists hn...
 Qed.

 (*
  SECTION 2: Define valid heap
 *)


 Definition no_cycle := fun (hp : heap) => 
  forall d n, reachable hp d (S n) d-> False.

 Definition valid_pointers := fun (hp : heap) =>
  forall d d' hn, find d hp = Some hn -> 
  pt hn = addr d' -> In d' hp.

 Definition valid_heap := fun hp => no_cycle hp /\ valid_pointers hp.

 Definition vheap := {h : heap | valid_heap h}.
 Definition get_h := fun (hp : vheap) => projT1 hp.

 Fixpoint find_parents_aux (hp : heap) (d : t) (n : nat) (l : list t) :=
  match n with
  |0 => match find d hp with
        |None => None
        |Some hn => Some (d,l)
        end
  |S n' => match find d hp with
           |None => None
           |Some hn => match pt hn with
                       |null => Some (d,l)
                       |addr d' => 
                        match find_parents_aux hp d' n' l with
                        |Some (d',l') => Some (d',d::l')
                        |None => None
                        end
                       end
           end
  end.

 Lemma find_parents_aux_prefix: forall n l l' hp d d',
  find_parents_aux hp d n l = Some (d',l') ->
  exists l'', l' = l''++l.
 Proof with try tauto.
  induction n;intros ? ? ? ? ?;simpl;
  case_eq (find d hp);disc.
  intros. inv H0. exists nil...

  intros ? ?. case_eq (pt h).
  intros. inv H1. exists nil...
  intros ? ?. case_eq (find_parents_aux hp t0 n l);disc.
  intros. destruct p. inv H2.
  apply IHn in H1. destruct H1;subst.
  exists (d::x)...
 Qed.

 Lemma find_parents_aux_list_irr: forall n l1 l2 l' hp d d',
  find_parents_aux hp d n l1 = Some (d',l'++l1) ->
  find_parents_aux hp d n l2 = Some (d',l'++l2).
 Proof with try tauto. 
  induction n;intros ? ? ? ? ? ?;simpl;
  case_eq (find d hp);disc.
  intros. inversion H0.
  assert (l' = nil).
   assert (length l1 = length (l'++l1)) by (rewrite <-H3;trivial).
   rewrite app_length in H1. icase l'. simpl in H1. omega.
  rewrite H1...
  intros ? ?. case_eq (pt h).
  intros. inversion H1.
  assert (l' = nil).
   assert (length l1 = length (l'++l1)) by (rewrite <-H4;trivial).
   rewrite app_length in H2. icase l'. simpl in H2. omega.
  rewrite H2...
  intros ? ?. case_eq (find_parents_aux hp t0 n l1);disc.
  intros. destruct p. inv H2. 
  generalize (find_parents_aux_prefix _ _ _ _ _ _ H1);intro.
  destruct H2. subst l.
  change (d::x++l1) with ((d::x)++l1) in H5.
  apply app_inv_tail in H5. subst.
  eapply IHn in H1. rewrite H1...
 Qed.

 Lemma find_parents_aux_list_irr2: forall n l1 l2  hp d ,
  find_parents_aux (get_h hp) d n l1 = None ->
  find_parents_aux (get_h hp) d n l2 = None.
 Proof with try tauto.
  induction n;intros ? ? ? ?;simpl;
  case_eq (find d (get_h hp));disc...
  intros ? ?. case_eq (pt h);disc.
  intros ? ?. case_eq (find_parents_aux (get_h hp) t0 n l1).
  intros. destruct p. inv H2.
  intros. apply IHn with (l2:=l2) in H1.
  rewrite H1...
 Qed.
 
 Lemma find_parents_aux_In1 : forall n l hp d d',
  find_parents_aux hp d n nil = Some (d',l) -> 
  List.In d (l++d'::nil).
 Proof with try tauto.
  intros ? ? ? ? ?; 
  icase n;simpl;
  case_eq (find d hp);disc.
  intros. inv H0. simpl. left...
  intros ? ?. case_eq (pt h).
  intros. inversion H1. simpl. left...
  intros ? ?. case_eq (find_parents_aux hp t0 n nil);intros;disc.
  destruct p. inv H2.
  generalize (find_parents_aux_prefix _ _ _ _ _ _ H1);intros.
  destruct H2;subst. left...
 Qed.

 Lemma find_parents_aux_In2: forall n l  hp d d' d'',
  find_parents_aux hp d n nil = Some (d',l) ->
  List.In d'' (l++d'::nil) -> In d'' hp.
 Proof with try tauto.
  induction n;intros ? ? ? ?;simpl;
  case_eq (find d hp);disc.
  intros. inv H0. simpl in H1. destruct H1;subst...
  apply find_In. exists h...

  intros ? ? ?.
  case_eq (pt h).
  intros. inv H1. simpl in H2. destruct H2;subst...
  apply find_In. exists h...
 
  intros ? ?. case_eq (find_parents_aux hp t0 n nil);disc.
  intros. destruct p. inv H2.
  destruct H3;subst. apply find_In. exists h...
  eapply IHn in H1;eauto.
 Qed.

 Lemma find_parents_aux_iff: forall n hp d,
  In d (get_h hp) <->
  exists d' l, find_parents_aux (get_h hp) d n nil = Some (d',l).
 Proof with try tauto.
  induction n;simpl;intros;
  rewrite find_In;
  case_eq (find d (get_h hp));intros.
  split;intros H1;inv H1;inv H0.
  exists d,nil... exists h...
  split;intros H1;inv H1;inv H0. inv H1.

  case_eq (pt h);intros.
  split;intros H1;destruct H1 as [? H1];inv H1.
  exists d,nil... exists h...
  case_eq (find_parents_aux (get_h hp) t0 n nil);intros.
  destruct p.
  split;intros H2;destruct H2 as [? H2];inv H2.
  2: exists h...
  assert (In t0 (get_h hp)).
   generalize (find_parents_aux_prefix _ _ _ _ _ _ H1);intros.
   destruct H2;subst. copy H1.
   apply find_parents_aux_In1 in H1.
   eapply find_parents_aux_In2 in H1;eauto...
  rewrite IHn in H2.
  destruct H2 as [? [? H2]].
  rewrite H2 in H1. inv H1.
  exists t1,(d::l)...

  split;intros H2;destruct H2 as [? H2];inv H2.
  2:exists h...
  spec IHn hp t0.
  destruct hp as [hp [pf1 pf2]];unfold get_h in *;simpl in *.
  generalize (pf2 d t0 x H H0);intros.
  rewrite IHn in H2. rewrite H1 in H2. destruct H2 as [? [? H2]];inv H2.

  split;intros H1;destruct H1 as [? H1];inv H1;disc.
 Qed.

 Lemma find_parents_aux_None: forall n hp d l,
  find_parents_aux (get_h hp) d n l = None <-> ~In d (get_h hp).
 Proof with try tauto.
  intros.
  case_eq (find_parents_aux (get_h hp) d n l);intros.
  split;intros. inv H0. elimtype False. apply H0.
  destruct p. copy H.
  apply find_parents_aux_prefix in H.
  destruct H;subst.
  apply find_parents_aux_list_irr with (l2:=nil) in H1.
  eapply find_parents_aux_iff;eauto.
  split;intros... intro.
  apply find_parents_aux_iff with (n:=n) in H1.
  destruct H1 as [? [? ?]].
  apply find_parents_aux_list_irr2 with (l2:=nil) in H.
  congruence.
 Qed.

 Lemma find_parents_aux_reachable1: forall n l hp d d' d'' i,
  find_parents_aux hp d n nil = Some (d',l) ->
  nth_op i (l++d'::nil) = Some d'' -> 
  reachable hp d i d''.
 Proof with try tauto.
  induction n;intros ? ? ? ? ? ?;simpl;
  case_eq (find d hp);disc.
  intros. inv H0. icase i;inv H1.
  apply zero_step. apply find_In. exists h...
  icase i;inv H2.

  intros ? ?.
  case_eq (pt h). intros.
  inv H1. icase i;inv H2.
  apply zero_step. apply find_In. exists h...
  icase i;inv H3.

  intros ? ?. case_eq (find_parents_aux hp t0 n nil);disc;intros.
  destruct p. inv H2. icase i. simpl in H3. inv H3.
  apply zero_step. apply find_In. exists h...
  eapply IHn in H1;eauto.
 Qed.

 Lemma find_parents_aux_reachable2: forall n l l' hp d1 d2,
  find_parents_aux hp d1 n l' = Some (d2,l) ->
  exists n', reachable hp d1 n' d2 /\ n' <= n.
 Proof with try tauto.
  induction n;intros;
  simpl in H; revert H;
  case_eq (find d1 hp);disc.
  intros. inv H0. exists 0. split;try omega.
  apply reachable_zero. split... apply find_In. exists h...

  intros ? ?. case_eq (pt h). intros.
  inv H1. exists 0. split;try omega. apply zero_step. apply find_In. exists h...
  intros ? ?. case_eq (find_parents_aux hp t0 n l');disc;intros.
  destruct p;inv H2.
  apply IHn in H1. destruct H1 as [n' H1]. exists (S n').
  split;try omega.
  destruct H1.
  eauto.
 Qed.

 Lemma find_parents_aux_reachable3: forall n l' hp d1 d2,
  reachable hp d1 n d2 ->
  exists l, find_parents_aux hp d1 n l' = Some (d2,l).
 Proof with try tauto.
  induction n;intros.
  inv H. exists l';simpl.
  case_eq (find d2 hp);intros...
  rewrite find_In in H0. destruct H0. rewrite H0 in H. inv H.

  inv H. apply IHn with (l':=l') in H5. destruct H5 as [l H5].
  exists (d1::l). simpl.
  rewrite H1. rewrite H2. rewrite H5...
 Qed.

 Lemma find_parents_aux_reachable4: forall n l hp d d1 d2,
  find_parents_aux hp d1 n nil = Some (d2,l) ->
  List.In d l -> exists n', reachable hp d (S n') d2.
 Proof with try tauto. 
  induction n;intros ? ? ? ? ?;simpl;
  case_eq (find d1 hp);disc.
  intros. inv H0. inv H1.
  intros ? ?. case_eq (pt h). intros. inv H1. inv H2.
  intros ? ?. case_eq (find_parents_aux hp t0 n nil);disc.
  intros. destruct p. inv H2. destruct H3. subst.
  icase l0. revert H1. icase n;simpl;
  case_eq (find t0 hp);disc.
  intros. inv H2. exists 0.
  eapply succ_step;eauto. 
  apply zero_step. apply find_In;eauto.
  intros ? ?. case_eq (pt h0).
  intros. inv H3. exists 0.
  eapply succ_step;eauto. 
  apply zero_step. apply find_In;eauto.
  intros ? ?. case_eq (find_parents_aux hp t1 n nil);disc.
  intros. destruct p. inv H4. 
  apply IHn with (d:= t0)in H1. destruct H1.
  exists (S x). eapply succ_step;eauto. 
  apply find_parents_aux_reachable1 with (d'':=t1) (i:=0) in H1...
  inv H1. left...
  eapply IHn in H1;eauto.
 Qed.

 Lemma find_parents_aux_NoDup: forall l hp d d' n,
  find_parents_aux (get_h hp) d n nil = Some (d',l) -> 
  NoDup (l++d'::nil).
 Proof with try tauto.
  intros.
  rewrite nth_op_NoDup.
  repeat intro;subst.
  generalize (find_parents_aux_reachable1 _ _ _ _ _ _ _ H H1);intro.
  generalize (find_parents_aux_reachable1 _ _ _ _ _ _ _ H H2);intro.
  destruct (nat_acc i j H0) as [k H5].
  destruct H5;subst.
  
  rewrite reachable_app in H3.
  destruct H3 as [d'' [H5 H6]].
  generalize (reachable_det _ _ _ _ _ H4 H5);intro;subst.
  destruct hp as [hp [pf pf']];unfold get_h in *;simpl in *.
  apply pf in H6...

  rewrite reachable_app in H4.
  destruct H4 as [d'' [H5 H6]].
  generalize (reachable_det _ _ _ _ _ H3 H5);intro;subst.
  destruct hp as [hp pf];unfold get_h in *;simpl in *.
  apply pf in H6...
 Qed.

 Lemma find_parents_aux_length: forall n l hp d d',
  find_parents_aux hp d n nil = Some (d',l) ->
  length l <= n.
 Proof with try tauto.
  induction n;intros ? ? ?;simpl;
  case_eq (find d hp);disc.
  intros. inv H0. simpl;omega.
  intros ? ?. case_eq (pt h).
  intros. inv H1. simpl;omega.
  intros ? ?. case_eq (find_parents_aux hp t0 n nil);intros;disc.
  destruct p. inv H2. apply IHn in H1. simpl. omega.
 Qed.

 Lemma find_parents_aux_root: forall n l hp d d',
  find_parents_aux (get_h hp) d n nil = Some (d',l) ->
  length l < n -> 
  is_root d' (get_h hp).
 Proof with try tauto.
  induction n;intros ? ? ?;simpl; unfold is_root;
  case_eq (find d (get_h hp));disc.
  intros. inv H0. inv H1...
  intros ? ? ?. case_eq (pt h).
  intros. inv H1. exists h...
  intros ? ?. case_eq (find_parents_aux (get_h hp) t0 n nil);intros;disc.
  destruct p; inv H2. simpl in H3. assert (length l0 < n) by omega.
  apply IHn in H1...
 Qed.

 Lemma find_parents_aux_limit: forall n l hp d d',
  find_parents_aux (get_h hp) d n nil = Some (d',l) ->
  length (l++d'::nil) <= length (kelements (get_h hp)).
 Proof with try tauto.
  intros. apply NoDup_length.
  eapply find_parents_aux_NoDup;eauto.
  apply NoDupA_keq_NoDup.
  apply kelements_spec3.
  repeat intro.
  apply InA_keq_In.
  apply kelements_spec1.
  eapply find_parents_aux_In2 in H;eauto.
 Qed.

 Lemma find_parents_aux_root_id: forall n l hp d,
  is_root d hp ->
  find_parents_aux hp d n l = Some (d,l).
 Proof with try tauto.
  intros.
  destruct H as [hn [? ?]].
  icase n;simpl;rewrite H...
  rewrite H0...
 Qed.

 Lemma find_parents_aux_reachable_iff: forall n hp d d',
  reachable hp d n d' <-> 
  exists l, find_parents_aux hp d n nil = Some (d',l) /\ length l = n.
 Proof with try tauto.
  induction n;intros.
  split;intros. inv H.
  exists nil. simpl;split;try omega.
  rewrite find_In in H0.
  destruct H0. rewrite H...
  destruct H as [l [H H1]].
  simpl in H. revert H.
  case_eq (find d hp);disc.
  intros. inv H0. apply zero_step.
  apply find_In. exists h...

  split;intros.
  inv H. apply IHn in H5.
  destruct H5 as [l [H5 H6]].
  exists (d::l).
  split. 2: simpl;omega.
  simpl. rewrite H1,H2,H5...
  destruct H as [l [H H1]].
  simpl in H. revert H.
  case_eq (find d hp);disc.
  intros ? ?. case_eq (pt h).
  intros. inv H2. inv H1.
  intros ? ?. case_eq (find_parents_aux hp t0 n nil);disc;intros.
  destruct p. inv H3.
  simpl in H1. 
  assert (length l0 = n) by omega.
  eapply succ_step;eauto.
  apply IHn. exists l0...
 Qed.
 
 Lemma find_parents_aux_root_limit: forall n n' l l' hp d d',
  find_parents_aux hp d n l = Some (d',l') ->
  is_root d' hp -> n <= n' ->
  find_parents_aux hp d n' l = Some (d',l').
 Proof with try tauto.
  induction n;intros ? ? ? ? ? ?;simpl;
  case_eq (find d hp);disc.
  intros. inv H0. apply find_parents_aux_root_id...
  intros ? ?. case_eq (pt h).
  intros. inv H1. apply find_parents_aux_root_id...
  intros ? ?. case_eq (find_parents_aux hp t0 n l);intros;disc.
  destruct p. inv H2. icase n'. omega.
  apply IHn with (n':=n')in H1;try omega...
  simpl. rewrite H. rewrite H0. rewrite H1...
 Qed.

 Lemma find_parents_aux_reduce: forall n hp d d' l,
  find_parents_aux hp d n nil = Some (d',l) ->
  find_parents_aux hp d (length l) nil = Some (d',l).
 Proof with try tauto.
  induction n;intros ? ? ? ?;simpl;
  case_eq (find d hp);disc.
  intros. inv H0. simpl. rewrite H...
  intros ? ?. case_eq (pt h).
  intros. inv H1. simpl. rewrite H...
  intros ? ?. case_eq (find_parents_aux hp t0 n nil);disc.
  intros. destruct p. inv H2.
  apply IHn in H1.
  simpl. rewrite H,H0. rewrite H1...
 Qed.

 Lemma find_parents_aux_split: forall l1 l2 hp d d' d'',
  find_parents_aux hp d (length (l1++(d''::l2))) nil = Some (d',l1++(d''::l2)) ->
  find_parents_aux hp d (length l1) nil = Some (d'',l1) /\
  find_parents_aux hp d'' (S (length l2)) nil = Some (d',d''::l2).
 Proof with try tauto.
  induction l1;intros ? ? ? ? ?;simpl;
  case_eq (find d hp);disc.
  intros ? ?. case_eq (pt h);disc.
  intros ? ?. case_eq (find_parents_aux hp t0 (length l2) nil);disc.
  intros. destruct p. inv H2. rewrite H,H0,H1...
  
  intros ? ?. case_eq (pt h);disc.
  intros ? ?. 
  case_eq (find_parents_aux hp t0 (length (l1 ++ d'' :: l2)) nil);disc.
  intros . destruct p. inv H2. apply IHl1 in H1.
  split... destruct H1. rewrite H1...
 Qed.

 Lemma find_parents_aux_combine: forall l1 l2 hp d d' d'',
  find_parents_aux hp d (length l1) nil = Some (d'',l1) ->
  find_parents_aux hp d'' (S (length l2)) nil = Some (d',d''::l2) ->
  find_parents_aux hp d (length (l1++(d''::l2))) nil = Some (d',l1++(d''::l2)).
 Proof with try tauto.
  induction l1;intros ? ? ? ? ?; simpl;
  case_eq (find d hp);disc.
  intros ? ? ?. inv H0. rewrite H...

  intros ? ?. case_eq (pt h).
  intros ? ?. inv H1.
  intros ? ?. case_eq (find_parents_aux hp t0 (length l1) nil);disc.
  intros ? ? ?. destruct p. inv H2.
  intros. erewrite IHl1...
 Qed.

 Lemma find_parents_aux_root_not_In: forall n l hp d d1 d2,
  find_parents_aux hp d1 n nil = Some (d2,l) ->
  is_root d hp -> ~List.In d l.
 Proof with try tauto.
  induction n;intros ? ? ? ? ?;simpl;
  case_eq (find d1 hp);disc.
  intros. inv H0. intro. inv H0.
  intros ? ?. case_eq (pt h).
  intros. inv H1. intro. inv H1.
  intros ? ?. case_eq (find_parents_aux hp t0 n nil);disc.
  intros. destruct p. inv H2.
  eapply IHn in H1;eauto. intro.
  apply H1. destruct H2;subst...
  destruct H3 as [? [? ?]];congruence.
 Qed.


 (*
  SECTION 3: Define h_find to find root, i.e. find without path compression
 *)

 Definition find_parents (hp : heap) (d : t) :=
  find_parents_aux hp d (length (kelements hp)) nil.

 Definition h_find (hp : vheap) (d : t):=
  match find_parents (get_h hp) d with
  |Some (d',l) => Some d'
  |None => None
  end.

 Program Definition h_empty : vheap := empty.
 Next Obligation.
  split;repeat intro.
  inv H. inv H1. inv H.
 Defined.

 Lemma h_find_empty: forall d,
  h_find h_empty d = None.
 Proof with try tauto.
  intros. compute...
 Qed.

 Lemma h_find_root: forall hp d d',
  h_find hp d = Some d' -> is_root d' (get_h hp).
 Proof with try tauto.
  intros ? ? ?.
  unfold h_find,find_parents.
  case_eq (find_parents_aux (get_h hp) d (length (kelements (get_h hp))) nil);intros;disc.
  destruct p. inv H0.
  apply find_parents_aux_root in H... 
  apply find_parents_aux_limit in H.
  rewrite app_length in H. simpl in H. omega.
 Qed.
  
 Lemma h_find_root_id: forall hp d,
  is_root d (get_h hp) ->
  h_find hp d = Some d.
 Proof with try tauto.
  intros.
  unfold h_find,find_parents.
  rewrite find_parents_aux_root_id...
 Qed.
 
 Lemma h_find_idempotent: forall hp d d',
  h_find hp d = Some d' ->
  h_find hp d' = Some d'.
 Proof with try tauto.
  intros.
  apply h_find_root_id.
  eapply h_find_root;eauto.
 Qed.

 Lemma h_find_exist: forall hp d,
  In d (get_h hp) <->
  exists d', h_find hp d = Some d'.
 Proof with try tauto.
  intros. split;intros.
  eapply find_parents_aux_iff in H.
  destruct H as [d' [l' H]].
  exists d'. unfold h_find,find_parents.
  rewrite H...
  destruct H as [d' H].
  unfold h_find,find_parents in H.
  revert H. case_eq (find_parents_aux (get_h hp) d (length (kelements (get_h hp))) nil);disc;intros.
  destruct p. inv H0.
  eapply find_parents_aux_iff;eauto. 
 Qed.

 Lemma h_find_Some_equiv: forall hp d d',
  h_find hp d = Some d' <-> 
  is_root d' (get_h hp) /\ (exists n, reachable (get_h hp) d n d').
 Proof with try tauto.
  intros. split;intros.
  split. eapply h_find_root;eauto.
  unfold h_find,find_parents in H.
  revert H.
  case_eq (find_parents_aux (get_h hp) d (length (kelements (get_h hp))) nil);disc;intros.
  destruct p. inv H0.
  apply find_parents_aux_reachable2 in H.
  destruct H as [n H]. exists n...

  destruct H as [H [n H1]].
  unfold h_find,find_parents.
  case_eq (find_parents_aux (get_h hp) d (length (kelements (get_h hp))) nil);intros.
  destruct p.
  assert (is_root t0 (get_h hp)).
   apply h_find_root with (d:=d).
   unfold h_find,find_parents.
   rewrite H0...
  apply find_parents_aux_reachable3 with (l':=nil) in H1.
  destruct H1 as [l' H1].
  destruct (Compare_dec.le_dec n (length (kelements (get_h hp)))).
  apply find_parents_aux_root_limit with (n':=length (kelements (get_h hp))) in H1...
  rewrite H1 in H0. inv H0...
  assert (length (kelements (get_h hp)) <= n) by omega.
  apply find_parents_aux_root_limit with (n':=n) in H0...
  rewrite H0 in H1. inv H1...
  apply reachable_two_ends in H1.
  destruct H1.
  rewrite find_parents_aux_iff in H1.
  destruct H1 as [? [? ?]].
  rewrite H1 in H0. inv H0.
 Qed.

 Lemma h_find_None_equiv: forall hp d,
  h_find hp d = None <-> ~In d (get_h hp).
 Proof with try tauto.
  intros;split;repeat intro.
  apply h_find_exist in H0.
  destruct H0. rewrite H0 in H. inv H.
  unfold h_find,find_parents.
  case_eq (find_parents_aux (get_h hp) d (length (kelements (get_h hp))) nil);intros...
  destruct p.
  elimtype False.
  apply H. eapply find_parents_aux_iff.
  exists t0,l. apply H0.
 Qed.

 Lemma is_root_id_iff: forall hp d,
  is_root d (get_h hp) <-> h_find hp d = Some d.
 Proof with try tauto.
  intros.
  split;intros.
  apply h_find_root_id in H...
  apply h_find_root in H...
 Qed.

 Lemma find_parents_spec: forall hp d d' l,
  find_parents (get_h hp) d = Some (d',l) ->
  is_root d' (get_h hp) /\ (forall k, List.In k l -> In k (get_h hp) /\ k <> d').
 Proof with try tauto.
  intros.
  split. apply h_find_root with (d:=d).
  unfold h_find. rewrite H...
  intros. split. 
  eapply find_parents_aux_In2 in H;eauto.
  rewrite in_app_iff...
  apply find_parents_aux_NoDup in H.
  apply NoDup_comm in H. inv H.
  intro. subst...
 Qed.

 (*
   SECTION 4: Definition singleton operator
 *)

 Definition find_add (hp : heap) (d : t) hn: heap :=
  match find d hp with
  |None => add d hn hp
  |_ => hp
  end.

 Lemma find_add_spec1: forall hp d hn,
  ~In d hp ->
  find_add hp d hn = add d hn hp.
 Proof with try tauto. 
  intros.
  unfold find_add.
  case_eq (find d hp);intros...
  rewrite find_In in H.
  elimtype False. apply H. exists h...
 Qed.

 Lemma find_add_spec2: forall hp d hn,
  In d hp ->
  find_add hp d hn = hp.
 Proof with try tauto.
  intros.
  unfold find_add.
  case_eq (find d hp);intros...
  rewrite find_In in H. destruct H. rewrite H in H0. inv H0.
 Qed.

 Program Definition h_singleton (hp : vheap) (d : t) : vheap :=
  find_add (get_h hp) d fresh_node.
 Next Obligation with try tauto.
  destruct hp as [hp [pf pf']]. unfold find_add,get_h.
  simpl.
  case_eq (find d hp);intros... split...
  split;repeat intro.
  assert (~In d hp). 
   intro. rewrite find_In in H1. destruct H1. rewrite H in H1;inv H1.
  apply reachable_add in H0...
  apply pf in H0...
  destruct (e_eq_dec d0 d);subst...
  inv H0. rewrite find_add_id in H3. inv H3. inv H4.

  destruct (e_eq_dec d0 d);subst...
  rewrite find_add_id in H0. inv H0. inv H1.
  rewrite find_add_diff in H0...
  generalize (pf' _ _ _ H0 H1);intro.
  destruct (e_eq_dec d' d);subst...
  apply In_add_id.
  apply In_add_diff...
 Defined.

 Lemma h_singleton_rewrite1: forall hp d,
  ~In d (get_h hp) ->  
  get_h (h_singleton hp d) = add d fresh_node (get_h hp).
 Proof with try tauto.
  intros. destruct hp as [hp pf].
  unfold h_singleton,get_h in *;simpl in *. simpl.
  rewrite find_add_spec1...
 Qed.

 Lemma h_singleton_rewrite2: forall hp d,
  In d (get_h hp) ->  
  get_h (h_singleton hp d) = get_h hp.
 Proof with try tauto.
  intros. destruct hp as [hp pf].
  unfold h_singleton,get_h in *;simpl in *.
  rewrite find_add_spec2...
 Qed.

 Lemma h_singleton_reachable1: forall n hp d d',
  ~In d (get_h hp) ->
  (reachable (get_h (h_singleton hp d)) d' n d <-> d' = d /\ n = 0).
 Proof with try tauto.
  intros. rewrite h_singleton_rewrite1...
  split;intro.
  Focus 2. destruct H0;subst...
  apply zero_step. apply In_add_id.

  icase n. inv H0...
  apply reachable_succ in H0.
  destruct H0 as [d'' [hn [? [? [? ?]]]]].
  apply reachable_two_ends in H0.
  destruct H0 as [_ H0].
  destruct (e_eq_dec d'' d);subst...
  rewrite find_add_id in H1. inv H1. inv H2.
  rewrite find_add_diff in H1...
  destruct hp as [hp [pf1 pf2]];unfold get_h in *;simpl in *.
  eapply pf2 in H1. spec H1 H2...
 Qed.

 Lemma h_singleton_reachable2: forall n hp d d1 d2,
  ~In d (get_h hp) -> d2 <> d ->
  (reachable (get_h hp) d1 n d2 <->
   reachable (get_h (h_singleton hp d)) d1 n d2).
 Proof with try tauto.
  intros.
  rewrite h_singleton_rewrite1...
  destruct hp as [hp [pf1 pf2]];unfold get_h in *;simpl in *.
  rewrite reachable_add...
 Qed.

 Lemma h_singleton_root: forall hp d,
  ~In d (get_h hp) -> is_root d (get_h (h_singleton hp d)).
 Proof with try tauto.
  intros. unfold is_root.
  exists fresh_node.
  split... rewrite h_singleton_rewrite1...
  rewrite find_add_id...
 Qed.

 Lemma h_singleton_find1: forall hp d d',
  ~In d (get_h hp) ->
  (h_find (h_singleton hp d) d' = Some d <-> d' = d).
 Proof with try tauto.
  intros. rewrite h_find_Some_equiv.
  split;intros.
  destruct H0 as [H0 [n H1]].
  rewrite h_singleton_reachable1 in H1...
  subst. split. apply h_singleton_root...
  exists 0. eapply h_singleton_reachable1 in H.
  destruct H as [_ H].
  apply H. split...
 Qed.

 Lemma h_singleton_find2: forall hp d d',
  ~In d (get_h hp) -> d' <> d ->
  (h_find (h_singleton hp d) d' = h_find hp d').
 Proof with try tauto.
  intros.
  case_eq (h_find hp d');intros.
  apply h_find_Some_equiv in H1.
  destruct H1 as [H1 [n H2]].
  assert (t0 <> d). 
   intro;subst.
   apply reachable_two_ends in H2...
  eapply h_singleton_reachable2 in H2;eauto.
  apply h_find_Some_equiv.
  split.
  2:exists n...
  destruct H1 as [hn [H4 H5]].
  exists hn. split...
  rewrite h_singleton_rewrite1...
  rewrite find_add_diff...
  rewrite h_find_None_equiv in H1.
  rewrite h_find_None_equiv.
  rewrite h_singleton_rewrite1...
  intro. apply H1. apply In_add_diff in H2...
 Qed.

 Lemma h_singleton_find3: forall hp d,
  ~In d (get_h hp) ->
  h_find (h_singleton hp d) d = Some d.
 Proof with try tauto. 
  intros. apply h_singleton_find1...
 Qed.

 (*
  SECTION 5: Define the function h_update_pt to update the pointer.
             This function is used to define find with path compression as well as union
 *)

 (*Only succeeds if d' is root and d and d' different*)
 Definition update_pt hp d d':=
  match find d hp with
   |Some hn => 
    if check_root d' hp then
     if e_eq_dec d d' then hp 
     else update d (Heap_node (addr d') (size hn)) hp
    else hp
   |None => hp
  end.

 Lemma update_pt_spec1: forall hp hn d d',
  find d hp = Some hn -> is_root d' hp -> d' <> d ->
  update_pt hp d d' = update d (Heap_node (addr d') (size hn)) hp.
 Proof with try tauto .
  intros.
  unfold update_pt.
  rewrite H. apply check_root_correct in H0.
  rewrite H0. destruct (e_eq_dec d d');subst...
 Qed.

 Lemma update_pt_spec2: forall hp d d',
  find d hp = None \/ ~is_root d' hp \/ d' = d -> 
  update_pt hp d d' = hp.
 Proof with try tauto. 
  intros. unfold update_pt.
  case_eq (find d hp);intros...
  rewrite<- check_root_correct in H.
  case_eq (check_root d' hp);intros...
  destruct (e_eq_dec d d');subst...
  rewrite H0,H1 in H.
  destruct H;inv H...
 Qed.

 Definition not_reachable := fun hp d n d' =>
  forall n', n' <= n -> reachable hp d n' d' -> False.

 Lemma update_not_reachable: forall n hp hn d d1 d2,
  In d hp ->
  not_reachable (update d hn hp) d1 n d ->
  (reachable (update d hn hp) d1 (S n) d2 <-> reachable hp d1 (S n) d2).
 Proof with try tauto.
  induction n;intros. spec H0 0. spec H0;try omega.
  assert (d1 <> d).
   intro;subst. apply H0;apply zero_step. 
   apply In_update_equiv...
  split;intros;inv H2;
  eapply succ_step;eauto.
  rewrite find_update_diff in H4... intro;subst...
  inv H8. apply zero_step... rewrite In_update_equiv in H2...
  rewrite find_update_diff... intro;subst...
  inv H8. apply zero_step... rewrite In_update_equiv...

  split;intros;inv H1.
  apply IHn in H7...
  eapply succ_step;eauto. rewrite find_update_diff in H3...
  intro;subst. spec H0 0. spec H0;try omega.
  apply H0. apply zero_step. apply In_update_equiv...
  clear - H0 H3 H4.
  repeat intro.
  spec H0 (S n'). apply H0;try omega...
  eapply succ_step;eauto.
  assert (d1 <> d).
   intro;subst. spec H0 0. spec H0;try omega.
   apply H0. apply zero_step. apply In_update_equiv...
  eapply IHn in H7;eauto...
  eapply succ_step;eauto. erewrite<- find_update_diff in H3;eauto...
  repeat intro.
  spec H0 (S n'). apply H0;try omega...
  eapply succ_step;eauto. rewrite find_update_diff... intro;subst...
 Qed.

 Program Definition h_update_pt (hp : vheap) d d' : vheap := 
  update_pt (get_h hp) d d'.
 Next Obligation with try tauto.
  destruct (is_root_dec (get_h hp) d').
  2: rewrite update_pt_spec2;destruct hp...
  case_eq (find d (get_h hp));intros.
  2:rewrite update_pt_spec2;destruct hp...
  destruct (e_eq_dec d' d);subst.
  rewrite update_pt_spec2;destruct hp...
  rewrite update_pt_spec1 with (hn := h)...

  split;repeat intro.
  destruct (classic (exists n', n' <= n0 /\ 
  reachable (update d (Heap_node (addr d') (size h)) (get_h hp)) d0 n' d)).
  destruct H2 as [n' [H2 H3]].
  apply le_exist in H2. destruct H2 as [n1 H2].
  subst. replace (S (n' + n1)) with (n' + S n1) in H1 by omega.
  apply reachable_app in H1.
  destruct H1 as [s1 [H1 H2]].
  generalize (reachable_det _ _ _ _ _ H1 H3);intro;subst.
  inv H2. rewrite find_update_id in H5... inv H5. inv H6.
  apply reachable_root in H9.
  destruct H9;subst. destruct H as [? [? ?]].
  icase n';inv H3... rewrite find_update_diff in H5... congruence. intro;subst...
  destruct H as [hn' [H4 H5]].
  exists hn'. split...
  rewrite find_update_diff... intro;subst...
  apply find_In. exists h...
  assert (not_reachable (update d {| pt := addr d'; size := (size h) |} (get_h hp)) d0 n0 d ).
  repeat intro. apply H2. exists n'...  clear H2.
  rewrite update_not_reachable in H1...
  destruct hp as [hp [pf1 pf2]].
  apply pf1 in H1... apply find_In. exists h...

  rewrite In_update_equiv.
  destruct (e_eq_dec d d0);subst.
  rewrite find_update_id in H1...
  inv H1. inv H2.
  apply root_In... apply find_In. exists h...
  rewrite find_update_diff in H1...
  destruct hp as [hp [pf1 pf2]].
  unfold get_h in *;simpl in *. eapply pf2;eauto.
 Defined.

 Lemma h_update_pt_rewrite: forall hp d d',
  get_h (h_update_pt hp d d') = update_pt (get_h hp) d d'.
 Proof with try tauto.
  intros.
  unfold get_h,h_update_pt.
  simpl...
 Qed.

 Lemma h_update_pt_In: forall hp d d1 d2,
  In d (get_h (h_update_pt hp d1 d2)) <-> In d (get_h hp).
 Proof with try tauto.
  intros. 
  unfold h_update_pt,get_h in *.
  simpl in *. destruct hp as [hp [pf1 pf2]];simpl in *.
  repeat rewrite find_In.
  destruct (In_dec hp d1).
  2: rewrite update_pt_spec2; try rewrite find_not_In...
  destruct (is_root_dec hp d2).
  2: rewrite update_pt_spec2...
  destruct (e_eq_dec d1 d2);subst.
  rewrite update_pt_spec2...
  apply find_In in H. destruct H as [hn H].
  erewrite update_pt_spec1;eauto...
  destruct (e_eq_dec d d1);subst.
  rewrite find_update_id...
  split;intros. exists hn...
  exists ({| pt := addr d2; size := size hn |})...
  apply find_In. eauto.
  rewrite find_update_diff... intro;subst...
 Qed.

 Lemma h_update_pt_find1: forall hp d1 d2 hn,
  find d1 (get_h hp) = Some hn -> is_root d2 (get_h hp) -> d1 <> d2 ->
  find d1 (get_h (h_update_pt hp d1 d2)) = Some (Heap_node (addr d2) (size hn)).
 Proof with try tauto.
  intros. rewrite h_update_pt_rewrite.
  erewrite update_pt_spec1;eauto.
  rewrite find_update_id... apply find_In;eauto.
 Qed.

 Lemma h_update_pt_find2: forall hp d1 d2 d,
  d <> d1 ->
  find d (get_h (h_update_pt hp d1 d2)) = find d (get_h hp).
 Proof with try tauto.
  intros. rewrite h_update_pt_rewrite.
  destruct (classic (In d1 (get_h hp) /\ is_root d2 (get_h hp) /\ d2 <> d1)).
  destruct H0 as [? ?]. apply find_In in H0.
  destruct H0.
  erewrite update_pt_spec1;eauto...
  rewrite find_update_diff... intro;subst...
  rewrite update_pt_spec2...
  assert (~In d1 (get_h hp) <-> find d1 (get_h hp) = None).
  rewrite find_not_In...
  tauto.
 Qed.
 
 Lemma h_update_pt_root1: forall hp d d1 d2,
  d1 <> d ->
  (is_root d (get_h (h_update_pt hp d1 d2)) <-> is_root d (get_h hp)).
 Proof with try tauto.
  intros.
  rewrite h_update_pt_rewrite.
  destruct (classic (In d1 (get_h hp) /\ is_root d2 (get_h hp) /\ d2 <> d1)).
  destruct H0 as [H0 H1]. apply find_In in H0. destruct H0.
  erewrite update_pt_spec1;eauto...
  split;intros;destruct H2 as [? [? ?]].
  rewrite find_update_diff in H2... exists x0...
  exists x0. split... rewrite find_update_diff...
  rewrite update_pt_spec2...
  assert (~In d1 (get_h hp) <-> find d1 (get_h hp) = None).
   rewrite find_not_In...
  tauto.
 Qed.

 Lemma h_update_pt_root2: forall hp d1 d2,
  (is_root d2 (get_h (h_update_pt hp d1 d2)) <-> is_root d2 (get_h hp)).
 Proof with try tauto.
  intros.
  rewrite h_update_pt_rewrite.
  destruct (classic (In d1 (get_h hp) /\ is_root d2 (get_h hp) /\ d2 <> d1)).
  destruct H as [H H0]. apply find_In in H. destruct H.
  erewrite update_pt_spec1;eauto...
  split;intros;destruct H1 as [? [? ?]].
  rewrite find_update_diff in H1... intro;subst...
  exists x0. split... rewrite find_update_diff... intro;subst...
  rewrite update_pt_spec2...
  assert (~In d1 (get_h hp) <-> find d1 (get_h hp) = None).
   rewrite find_not_In...
  tauto.
 Qed.

 Lemma h_update_pt_find_parents_aux1: forall n hp d1 d2 l1 l2 d d',
  In d1 (get_h hp) -> is_root d2 (get_h hp) -> d1 <> d2 ->
  find_parents_aux (get_h hp) d n nil = Some (d',l1++(d1::l2)) ->
  find_parents_aux (get_h (h_update_pt hp d1 d2)) d n nil = Some (d2,l1++(d1::nil)).
 Proof with try tauto.
  induction n;intros ? ? ? ? ? ? ? ? ? ?;simpl;
  case_eq (find d (get_h hp));disc.
  intros. inv H3. icase l1;inv H6.
  intros ? ?. case_eq(pt h).
  intros. inv H4. icase l1;inv H7.
  intros ? ?. case_eq(find_parents_aux (get_h hp) t0 n nil);disc;intros.
  destruct p. inv H5. 
  icase l1. inv H8. 
  assert (find d1 (get_h (h_update_pt hp d1 d2)) = Some (Heap_node (addr d2) (size h))).
   apply h_update_pt_find1...
  rewrite H5. simpl.
  assert (find_parents_aux (get_h (h_update_pt hp d1 d2)) d2 n nil = Some (d2,nil)).
   apply find_parents_aux_root_id.
   apply h_update_pt_root1...
  rewrite H6...
  symmetry in H8;inv H8.
  assert (d <> d1). 
   intro;subst.
   assert (nth_op (length l1) ((l1++(d1::l2))++(d'::nil)) = Some d1).
    clear. induction l1;simpl...
   eapply find_parents_aux_reachable1 in H5;eauto.
   assert (reachable (get_h hp) d1 (S (length l1)) d1).
    eapply succ_step;eauto.
   destruct hp as [hp [pf1 pf2]]. apply pf1 in H6...
  rewrite h_update_pt_find2...
  rewrite H2,H3. apply IHn with (d2:=d2) in H4...
  rewrite H4...
 Qed.

 Lemma h_update_pt_find_parents_aux2: forall n hp d1 d2 l d,
  In d1 (get_h hp) -> is_root d2 (get_h hp) -> d1 <> d2 ->
  find_parents_aux (get_h hp) d n nil = Some (d1,l) ->
  find_parents_aux (get_h (h_update_pt hp d1 d2)) d (S n) nil = Some (d2,l++(d1::nil)).
 Proof with try tauto.
  induction n;intros ? ? ? ? ? ? ? ?;simpl;
  case_eq (find d (get_h hp));disc.
  intros. inv H3. apply find_In in H.
  destruct H as [hn H].
  erewrite h_update_pt_find1;eauto. simpl.
  rewrite h_update_pt_find2. 2: intro;subst...
  destruct H0 as [? [? ?]]. rewrite H0...
  intros ? ?. case_eq (pt h). intros. inv H4.
  apply find_In in H. destruct H as [hn H].
  erewrite h_update_pt_find1;eauto. simpl.
  rewrite h_update_pt_find2. 2: intro;subst...
  destruct H0 as [? [? ?]]. rewrite H0, H4...
  intros ? ?. case_eq (find_parents_aux (get_h hp) t0 n nil);disc.
  intros. destruct p. inv H5.
  assert (d <> d1). 
   intro;subst.
   assert (nth_op (length l0) (l0++(d1::nil)) = Some d1).
    clear. induction l0;simpl...
   eapply find_parents_aux_reachable1 in H5;eauto.
   assert (reachable (get_h hp) d1 (S (length l0)) d1).
    eapply succ_step;eauto.
   destruct hp as [hp [pf1 pf2]]. apply pf1 in H6...
  rewrite h_update_pt_find2... rewrite H2,H3.
  destruct (e_eq_dec t0 d1);subst...
  apply find_In in H. destruct H as [hn H].
  erewrite h_update_pt_find1;eauto... simpl.
  assert (l0 = nil).
   clear - H4 H H0 H1.
   revert H H0 H1 H4.
   revert hp d1 d2 hn l0.
   induction n; simpl;intros ? ? ? ? ? ? ? ?;
   rewrite H. intros. inv H4...
   case_eq (pt hn). intros. inv H4...
   intros ? ?. case_eq (find_parents_aux (get_h hp) t0 n nil);disc.
   intros. destruct p. inv H4. 
   apply find_parents_aux_reachable2 in H3.
   destruct H3 as [? [? ?]].
   assert (reachable (get_h hp) d1 (S x) d1).
    eapply succ_step;eauto.
   destruct hp as [hp [pf1 pf2]]. apply pf1 in H5...
  subst.
  assert (find_parents_aux (get_h (h_update_pt hp d1 d2)) d2 n nil = Some (d2,nil)).
   apply find_parents_aux_root_id.
   apply h_update_pt_root1...
  rewrite H6...
  rewrite h_update_pt_find2...
  case_eq (find t0 (get_h hp)). intros.
  case_eq (pt h0). intros. 
  revert H4.
  icase n;simpl. rewrite H6.
  intros. inv H4...
  rewrite H6,H7... intros. inv H4...

  intros. apply IHn with (d2:=d2) in H4...
  revert H4. simpl.
  rewrite h_update_pt_find2...
  rewrite H6,H7.
  case_eq (find_parents_aux (get_h (h_update_pt hp d1 d2)) t1 n nil);disc.
  intros. destruct p. inv H8. rewrite H11...
  intros. 
  assert (In t0 (get_h hp)).
   eapply find_parents_aux_In2;eauto.
   eapply find_parents_aux_In1;eauto.
  apply find_In in H7. destruct H7;congruence.
 Qed.

 Lemma h_update_pt_find_parents_aux3: forall n hp d1 d2 l d d',
  In d1 (get_h hp) -> is_root d2 (get_h hp) -> d1 <> d2 ->
  ~List.In d1 l -> d' <> d1 ->  
  find_parents_aux (get_h hp) d n nil = Some (d',l) ->
  find_parents_aux (get_h (h_update_pt hp d1 d2)) d n nil = Some (d',l).
 Proof with try tauto.
  induction n;intros ? ? ? ? ? ? ? ? ? ? ?;simpl;
  case_eq (find d (get_h hp));disc.
  intros. inv H5. rewrite h_update_pt_find2...
  rewrite H4...
  intros ? ?. case_eq (pt h).
  intros. inv H6. rewrite h_update_pt_find2...
  rewrite H4,H5...
  intros ? ?.
  case_eq (find_parents_aux (get_h hp) t0 n nil);disc.
  intros. destruct p. inv H7.
  assert (d <> d1 /\ ~List.In d1 l0).
   simpl in H2. tauto.
  rewrite h_update_pt_find2...
  rewrite H4,H5. 
  erewrite IHn;eauto...
 Qed.

 Lemma h_update_pt_kelements: forall hp d1 d2,
  length (kelements (get_h (h_update_pt hp d1 d2))) = length (kelements (get_h hp)).
 Proof with try tauto.
  intros.
  rewrite h_update_pt_rewrite.
  destruct hp as [hp pf]. unfold get_h;simpl.
  destruct (classic (In d1 hp /\ is_root d2 hp /\ d2 <> d1)).
  destruct H as [H H1]. apply find_In in H.
  destruct H.
  erewrite update_pt_spec1;eauto...
  apply kelements_update.
  rewrite update_pt_spec2...
  assert (~In d1 hp <-> find d1 hp = None).
   rewrite find_not_In...
  tauto.
 Qed.

 Lemma h_update_pt_find_parents1: forall hp d1 d2 l1 l2 d d',
  In d1 (get_h hp) -> is_root d2 (get_h hp) -> d1 <> d2 ->
  find_parents (get_h hp) d = Some (d',l1++(d1::l2)) ->
  find_parents (get_h (h_update_pt hp d1 d2)) d = Some (d2,l1++(d1::nil)).
 Proof with try tauto.
  intros.
  unfold find_parents in *.
  apply h_update_pt_find_parents_aux1 with (l2:=l2) (d':=d')...
  rewrite h_update_pt_kelements...
 Qed.

 Lemma h_update_pt_find_parents2: forall hp d1 d2 l d,
  In d1 (get_h hp) -> is_root d2 (get_h hp) -> d1 <> d2 ->
  find_parents (get_h hp) d = Some (d1,l) ->
  find_parents (get_h (h_update_pt hp d1 d2)) d = Some (d2,l++(d1::nil)).
 Proof with try tauto.
  intros.
  unfold find_parents in *.
  apply h_update_pt_find_parents_aux2 with (d2:=d2) in H2...
  rewrite<- h_update_pt_root2 with (d1:=d1) in H0.
  apply find_parents_aux_reduce in H2.
  eapply find_parents_aux_root_limit;eauto.
  apply find_parents_aux_limit in H2.
  rewrite app_length in H2. omega.
 Qed.

 Lemma h_update_pt_find_parents3: forall hp d1 d2 l d d',
  In d1 (get_h hp) -> is_root d2 (get_h hp) -> d1 <> d2 ->
  ~List.In d1 l -> d' <> d1 ->  
  find_parents (get_h hp) d = Some (d',l) ->
  find_parents (get_h (h_update_pt hp d1 d2)) d = Some (d',l).
 Proof with try tauto.
  intros. unfold find_parents in *.
  apply h_update_pt_find_parents_aux3...
  rewrite h_update_pt_kelements...
 Qed.

 Lemma h_update_pt_h_find1: forall hp d1 d2 l d d',
  In d1 (get_h hp) -> is_root d2 (get_h hp) -> d1 <> d2 ->
  find_parents (get_h hp) d = Some (d',l) ->
  List.In d1 (d'::l) ->
  h_find (h_update_pt hp d1 d2) d = Some d2.
 Proof with try tauto.
  intros. unfold h_find.
  destruct H3;subst.
  eapply h_update_pt_find_parents2 in H2;eauto.
  rewrite H2...
  apply In_split in H3. destruct H3 as [l1 [l2 H3]].
  subst l.
  eapply h_update_pt_find_parents1 in H2;eauto.
  rewrite H2...
 Qed.

 Lemma h_update_pt_h_find2: forall hp d1 d2 l d d',
  In d1 (get_h hp) -> is_root d2 (get_h hp) -> d1 <> d2 ->
  find_parents (get_h hp) d = Some (d',l) ->
  ~List.In d1 (d'::l) ->
  h_find (h_update_pt hp d1 d2) d = Some d'.
 Proof with try tauto.
  intros. unfold h_find. simpl in H3.
  eapply h_update_pt_find_parents3 in H2;eauto...
  rewrite H2...
 Qed.

 Lemma h_update_pt_h_find3: forall hp d d1 d2,
  is_root d1 (get_h hp) -> is_root d2 (get_h hp) -> d1 <> d2 ->
  (h_find (h_update_pt hp d1 d2) d = Some d2 <->
   h_find hp d = Some d1 \/ h_find hp d = Some d2).
 Proof with try tauto.
  intros. split;intros.
 
  assert (In d (get_h hp)).
   rewrite<- h_update_pt_In.
   apply h_find_exist. eauto.
  apply h_find_exist in H3. destruct H3 as [d' H3].
  destruct (e_eq_dec d' d1);subst...
  destruct (e_eq_dec d' d2);subst...
  unfold h_find in H3.
  revert H3. case_eq (find_parents (get_h hp) d);disc.
  intros. destruct p. inv H4.
  assert (~List.In d1 (d'::l)).
   apply find_parents_aux_root_not_In with (d:=d1) in H3...
   intro. apply H3. destruct H4;subst...
  apply h_update_pt_h_find2 with (d1:=d1) (d2:=d2)in H3...
  rewrite H2 in H3. inv H3...
  apply root_In...

  destruct H2;unfold h_find in H2; revert H2;
  case_eq (find_parents (get_h hp) d);disc;intros;
  destruct p; inv H3.
  eapply h_update_pt_h_find1;eauto;simpl;
  try apply root_In...
  eapply h_update_pt_h_find2;eauto;simpl.
  apply root_In...
  intro. destruct H3;subst...
  unfold find_parents in H2. 
  eapply find_parents_aux_root_not_In in H2;eauto.
 Qed. 

 Lemma h_update_pt_h_find4: forall hp d d' d1 d2,
  is_root d1 (get_h hp) -> is_root d2 (get_h hp) ->
  d1 <> d2 -> d' <> d1 -> d' <> d2 ->
  (h_find (h_update_pt hp d1 d2) d = Some d' <->
  h_find hp d = Some d').
 Proof with try tauto.
  intros.
  split;intros.

  assert (In d (get_h hp)).
   rewrite<- h_update_pt_In.
   apply h_find_exist. eauto.
  apply h_find_exist in H5. destruct H5 as [d'' H5].
  generalize (h_update_pt_h_find3 _ d _ _ H H0 H1);intro.
  destruct H6 as [_ H6].
  destruct (e_eq_dec d'' d1);subst...
  spec H6... congruence.
  destruct (e_eq_dec d'' d2);subst...
  spec H6... congruence.
  unfold h_find in H5.
  revert H5. case_eq (find_parents (get_h hp) d);disc;intros.
  destruct p. inv H7.
  assert (~List.In d1 (d''::l)).
   apply find_parents_aux_root_not_In with (d:=d1) in H5;eauto.
   intro. destruct H7;subst...
  copy H5.
  apply h_update_pt_h_find2 with (d1:=d1) (d2:=d2)in H5...
  rewrite H5 in H4. inv H4.
  unfold h_find. rewrite H8...
  apply root_In...

  unfold h_find in H4.
  revert H4. case_eq (find_parents (get_h hp) d);disc.
  intros. destruct p. inv H5.
  eapply h_update_pt_h_find2 in H4;eauto.
  apply root_In...
  intro. destruct H5;subst...
  eapply find_parents_aux_root_not_In in H4;eauto.
 Qed.

 Lemma h_update_pt_reduce:forall hp d1 d2 ,
  ~(In d1 (get_h hp) /\ is_root d2 (get_h hp) /\ d2 <> d1) ->
  h_update_pt hp d1 d2 = hp.
 Proof with try tauto.
  intros.
  unfold h_update_pt.
  destruct hp as [hp pf].
  apply exist_ext. unfold get_h;simpl.
  rewrite update_pt_spec2...
  unfold get_h in *;simpl in *.
  assert (~In d1 hp <-> find d1 hp = None).
   rewrite find_not_In...
  tauto.
 Qed.

 (*
   SECTION 6 : Define find with path compression
 *)

 Definition path_compress hp r l :=
  fold_right (fun d' hp' => h_update_pt hp' d' r) hp l.

 Definition h_cfind hp d :=
  match find_parents (get_h hp) d with
  |None => (None,hp)
  |Some (r,l) => (Some r, path_compress hp r l)
  end.

 Definition h_cfind_r := fun hp d => fst (h_cfind hp d).
 Definition h_cfind_hp := fun hp d => snd (h_cfind hp d).

 Lemma path_compress_In: forall l hp r d,
  In d (get_h (path_compress hp r l)) <-> In d (get_h hp).
 Proof with try tauto.
  induction l;intros;simpl...
  rewrite h_update_pt_In...
  rewrite IHl... 
 Qed.

 Lemma path_compress_root1: forall l hp r d,
  ~List.In d l ->
  (is_root d (get_h (path_compress hp r l)) <-> is_root d (get_h hp)).
 Proof with try tauto.
  induction l;intros;simpl... simpl in H.
  rewrite h_update_pt_root1...
  rewrite IHl...
 Qed.

 Lemma path_compress_root2: forall l hp r,
  (is_root r (get_h (path_compress hp r l)) <-> is_root r (get_h hp)).
 Proof with try tauto.
  induction l;intros;simpl...
  rewrite h_update_pt_root2...
  rewrite IHl...
 Qed.

 Lemma path_compress_find1: forall l hp r d,
  ~List.In d l ->
  find d (get_h (path_compress hp r l)) = find d (get_h hp).
 Proof with try tauto.
  induction l;intros;simpl... simpl in H.
  rewrite h_update_pt_find2...
  rewrite IHl...
  intro;subst...
 Qed.

 Lemma path_compress_find2: forall l hp r d hn,
  find d (get_h hp) = Some hn -> (is_root r (get_h hp)) -> d <> r ->
  List.In d l ->
  find d (get_h (path_compress hp r l)) = Some (Heap_node (addr r) (size hn)).
 Proof with try tauto.
  induction l;intros;simpl...
  destruct H2;subst.
  destruct (in_dec e_eq_dec d l).
  rewrite h_update_pt_find1 with (hn:={| pt := addr r; size := size hn |})...
  apply IHl... apply path_compress_root2...
  erewrite h_update_pt_find1;eauto...
  rewrite path_compress_find1...
  apply path_compress_root2...
  destruct (e_eq_dec d a) ;subst.
  rewrite h_update_pt_find1 with (hn:={| pt := addr r; size := size hn |})...
  apply IHl... apply path_compress_root2... 
  erewrite h_update_pt_find2;eauto...
 Qed.
  
 Lemma path_compress_find_parents_aux1: forall l' l hp r d1 d2,
  is_root r (get_h hp) ->
  (forall d, List.In d l -> In d (get_h hp) /\ d <> r /\ ~List.In d l') ->
  find_parents_aux (get_h hp) d1 (length l') nil = Some (d2,l') ->
   find_parents_aux (get_h (path_compress hp r l)) d1 (length l') nil = Some (d2,l').
 Proof with try tauto.
  induction l';intros ? ? ? ? ? ? ?;simpl;
  case_eq (find d1 (get_h hp));disc.
  intros. inv H2.
  case_eq (find d2 (get_h (path_compress hp r l)));intros...
  apply find_not_In in H2. 
  rewrite path_compress_In in H2.
  apply find_not_In in H2. congruence.
  
  intros ? ?. case_eq  (pt h).
  intros. inv H3. intros ? ?.
  case_eq (find_parents_aux (get_h hp) t0 (length l') nil);disc.
  intros. destruct p. inv H4.
  rewrite path_compress_find1.
  rewrite H1,H2... erewrite IHl';eauto.
  intros. spec H0 d H4. simpl in *...
  intro. spec H0 a H4. simpl in *...
 Qed.

 Lemma path_compress_find_parents_aux2: forall l hp r d,
  is_root r (get_h hp) -> List.In d l -> In d (get_h hp) -> d <> r ->
  find_parents_aux (get_h (path_compress hp r l)) d 1 nil = Some (r,d::nil).
 Proof with try tauto.
  intros. simpl.
  apply find_In in H1. destruct H1 as [hn H1].
  erewrite path_compress_find2;eauto. simpl.
  case_eq (find r (get_h (path_compress hp r l)));intros...
  apply find_not_In in H3.  rewrite path_compress_In in H3.
  apply root_In in H...
 Qed.

 Lemma path_compress_find_parents1: forall l l' hp r d1 d2,
  find_parents (get_h hp) d1 = Some (d2,l') ->
  is_root r (get_h hp) ->
  (forall d, List.In d l -> In d (get_h hp) /\ d <> r /\ ~List.In d (d2::l')) ->
   find_parents (get_h (path_compress hp r l)) d1 = Some (d2,l').
 Proof with try tauto.
  induction l;intros;simpl... simpl in H1.
  generalize (H1 a);intros. spec H2...
  eapply h_update_pt_find_parents3;eauto...
  apply path_compress_In...
  apply path_compress_root2...
 Qed.

 Lemma path_compress_find_parents2:  forall l l1 l2 hp r d1 d2 d',
  find_parents (get_h hp) d1 = Some (d2,l1++(d'::l2)) -> List.In d' l -> 
  NoDup l -> is_root r (get_h hp) ->
  (forall d, List.In d l -> In d (get_h hp) /\ d <> r /\ ~List.In d l1) ->
  find_parents (get_h (path_compress hp r l)) d1 = Some (r,l1++(d'::nil)).
 Proof with try tauto.
  intros. apply find_parents_aux_reduce in H.
  apply find_parents_aux_split in H. destruct H.
  apply path_compress_find_parents_aux1 with (l:=l) (r:=r) in H...
  spec H3 d' H0. destruct H3 as [? [? ?]].
  generalize (path_compress_find_parents_aux2 _ _ _ _ H2 H0 H3 H5);intros.
  change 1 with (S (length (@nil t))) in H7.
  generalize (find_parents_aux_combine _ _ _ _ _ _ H H7);intro.
  eapply find_parents_aux_root_limit;eauto.
  apply path_compress_root2...
  apply find_parents_aux_limit in H8.
  rewrite app_length in H8. omega.
 Qed.

 (*Reduce h_cfind to h_find which is much easier to reason*)

 Lemma h_cfind_reduce1: forall hp d,
  h_cfind_r hp d = h_find hp d.
 Proof with try tauto.
  intros.
  unfold h_cfind_r,h_cfind,h_find.
  case_eq (find_parents (get_h hp) d);simpl...
  intros. destruct p...
 Qed.

 Lemma h_cfind_reduce2: forall hp d d',
  h_find (h_cfind_hp hp d) d' = h_find hp d'.
 Proof with try tauto.
  intros.
  unfold h_cfind_hp,h_cfind,h_find.
  case_eq (find_parents (get_h hp) d)...
  intros. destruct p. simpl.
  case_eq (find_parents (get_h hp) d')...
  copy H. apply find_parents_spec in H0.
  destruct H0 as [H0 H1].
  intros. destruct p.
  destruct (classic (disjoint l l0)).
  erewrite path_compress_find_parents1;eauto.
  intros. spec H1 d0 H4. split... split...
  eapply disjoint_in;eauto.
  change (t1::l0) with ((t1::nil)++l0).
  rewrite disjoint_app_iff. split...
  repeat intro. simpl in H5.
  destruct H5. destruct H6;subst... 
  apply find_parents_aux_reachable4 with (d:=x) in H...
  destruct H. apply find_parents_spec in H2.
  destruct H2 as [H2 _]. destruct H2 as [? [? ?]].
  inv H. congruence.

  assert (~disjoint l0 l).
   intro. apply H3. apply disjoint_comm...
  clear H3.
  generalize (@not_disjoint_case _ e_eq_dec _ _ H4);intro.
  destruct H3 as [d''[l1 [l2 [H5 [H6 H7]]]]]. subst.
  assert (t0 = t1).
    copy H2.
    apply find_parents_aux_reachable4 with (d:=d'') in H2.
    destruct H2. apply find_parents_spec in H3. destruct H3 as [H3 _].
    apply find_parents_aux_reachable4 with (d:=d'') in H...
    destruct H. destruct (Compare_dec.le_dec x x0).
    apply le_exist in l0. destruct l0. subst.
    replace (S(x+x1)) with (S x + x1) in H by omega.
    apply reachable_app in H. destruct H as [? [? ?]].
    apply reachable_det with (d':=x0) in H2... subst.
    icase x1; inv H5... destruct H3 as [? [? ?]];congruence.
    assert (x0 <= x) by omega.
    apply le_exist in H5. destruct H5. subst.
    replace (S(x0+x1)) with (S x0 + x1) in H2 by omega.
    apply reachable_app in H2. destruct H2 as [? [? ?]].
    apply reachable_det with (d':=x) in H... subst.
    icase x1; inv H5... destruct H0 as [? [? ?]];congruence.
    rewrite in_app_iff. simpl...
  subst.
  eapply path_compress_find_parents2 in H2;eauto.
  rewrite H2... 
  apply find_parents_aux_NoDup in H...
  apply NoDup_app in H...
  intros. spec H1 d0 H3. split... split...
  spec H7 d0... unfold find_parents.
  rewrite find_parents_aux_None. intros.
  case_eq (find_parents_aux (get_h (path_compress hp t0 l)) d'
    (length (kelements (get_h (path_compress hp t0 l)))) nil)...
  intros. destruct p.
  erewrite <-path_compress_In in H0.
  eapply find_parents_aux_None in H0.
  rewrite H0 in H1. inv H1.
 Qed.

 Lemma h_cfind_reduce3: forall hp d d',
  In d' (get_h (h_cfind_hp hp d)) <-> In d' (get_h hp).
 Proof with try tauto.
  intros.
  repeat rewrite h_find_exist.
  split;intros;destruct H;exists x.
  rewrite h_cfind_reduce2 in H...
  rewrite h_cfind_reduce2...
 Qed.

 Lemma h_cfind_reduce4: forall hp d d',
  is_root d' (get_h (h_cfind_hp hp d)) <-> is_root d' (get_h hp).
 Proof with try tauto.
  intros. repeat rewrite is_root_id_iff.
  split;intros. rewrite h_cfind_reduce2 in H...
  rewrite h_cfind_reduce2...
 Qed.

 Lemma h_cfind_rewrite: forall hp hp' d d',
  h_cfind hp d = (d',hp') ->
  h_cfind_hp hp d = hp' /\ h_cfind_r hp d = d'.
 Proof.
  intros.
  unfold h_cfind_hp,h_cfind_r;rewrite H.
  tauto.
 Qed.

 (*
  SECTION 7: Definition update_size which is useful for update rank in union
 *)

 Definition update_size hp d s:=
  match find d hp with
   |Some hn => update d (Heap_node (pt hn) (s + (size hn))) hp
   |None => hp
  end.

 Lemma update_size_spec1: forall hp d hn s,
  find d hp = Some hn -> 
  update_size hp d s = update d (Heap_node (pt hn) (s + (size hn))) hp.
 Proof with try tauto. 
  intros.
  unfold update_size.
  rewrite H...
 Qed.

 Lemma update_size_spec2: forall hp d s,
  find d hp = None -> 
  update_size hp d s = hp.
 Proof with try tauto.
  intros.
  unfold update_size.
  rewrite H...
 Qed.

 Lemma find_update_size1: forall hp d d' s,
  d' <> d ->
  find d (update_size hp d' s) = find d hp.
 Proof with try tauto.
  intros.
  unfold update_size.
  case_eq (find d' hp);intros...
  rewrite find_update_diff...
 Qed.

 Lemma find_update_size2: forall hp d hn s,
  find d hp = Some hn <->
  find d (update_size hp d s) = Some (Heap_node (pt hn) (s + (size hn))).
 Proof with try tauto.
  intros.
  unfold update_size.
  case_eq (find d hp);intros...
  rewrite find_update_id...
  split;intros;inv H0... destruct h. destruct hn.
  f_equal. f_equal... simpl in *. omega.
  apply find_In;eauto... rewrite H.
  split;intros;inv H0.
 Qed.

 Lemma find_parents_aux_update_size: forall n l hp d d' s,
  find_parents_aux (update_size hp d s) d' n l = find_parents_aux hp d' n l.
 Proof with try tauto. 
  induction n;intros ? ? ? ? ?;simpl.
  destruct (e_eq_dec d' d);subst.
  unfold update_size.
  case_eq (find d hp);intros. rewrite find_update_id...
  apply find_In;eauto. rewrite H...
  rewrite find_update_size1... intro;subst...
  case_eq (find d' hp);intros.
  case_eq (find d' (update_size hp d s));intros.
  assert (pt h0 = pt h).
   destruct (e_eq_dec d' d);subst...
   unfold update_size in H0. rewrite H in H0.
   rewrite find_update_id in H0... inv H0...
   apply find_In;eauto.
   rewrite find_update_size1 in H0. congruence. intro;subst...
  rewrite H1.
  case_eq (pt h)... intros.
  rewrite IHn... destruct (e_eq_dec d' d);subst.
  unfold update_size in H0. rewrite H in H0.
  rewrite find_update_id in H0;inv H0. apply find_In;eauto.
  rewrite find_update_size1 in H0. congruence. intro;subst...
  case_eq (find d' (update_size hp d s));intros...
  destruct (e_eq_dec d' d);subst...
  unfold update_size in H0. rewrite H in H0. congruence.
  rewrite find_update_size1 in H0... congruence. intro;subst...
 Qed. 

 Lemma update_size_reachable: forall n hp hn s d d1 d2,
  find d hp = Some hn ->
  (reachable (update d (Heap_node (pt hn) (s + (size hn))) hp) d1 n d2 <-> reachable hp d1 n d2).
 Proof with try tauto. 
  induction n;intros.
  split;intros. inv H0. apply zero_step.
  rewrite In_update_equiv in H1...
  inv H0. apply zero_step. rewrite In_update_equiv...

  split;intros;inv H0.

  apply IHn in H6...
  destruct (e_eq_dec d1 d);subst.
  rewrite find_update_id in H2... inv H2. inv H3.
  eapply succ_step;eauto.
  apply find_In. exists hn...
  rewrite find_update_diff in H2. 2: intro;subst...
  eapply succ_step;eauto...

  eapply IHn with (s:=s) in H6;eauto...
  destruct (e_eq_dec d1 d);subst.
  rewrite H2 in H. inv H.
  eapply succ_step with (hn:= {| pt := pt hn; size := s + size hn |});eauto...
  rewrite find_update_id... apply find_In. exists hn...
  eapply succ_step;eauto.
  rewrite find_update_diff... intro;subst...
  apply IHn...
  apply IHn in H6...
 Qed.

 Lemma kelements_update_size: forall hp d s,
  length (kelements (update_size hp d s)) = length (kelements hp).
 Proof with try tauto.
  intros.
  unfold update_size.
  case_eq (find d hp);intros...
  rewrite kelements_update...
 Qed.

 Program Definition h_update_size (hp : vheap) d s : vheap := 
  update_size (get_h hp) d s.
 Next Obligation with try tauto.
  case_eq (find d (get_h hp));intros.
  2:rewrite update_size_spec2;destruct hp...
  rewrite update_size_spec1 with (hn := h)...

  split;repeat intro.
  rewrite update_size_reachable in H0...
  destruct hp as [hp [pf1 pf2]];eauto.
  
  rewrite In_update_equiv.
  destruct (e_eq_dec d d0);subst.
  rewrite find_update_id in H0. inv H0. inv H1.
  destruct hp as [hp [pf1 pf2]];eauto.
  apply find_In. exists h...
  rewrite find_update_diff in H0... 
  destruct hp as [hp [pf1 pf2]];eauto.
 Qed.

 Lemma h_update_size_reduce: forall hp d d' s,
  h_find (h_update_size hp d s) d' = h_find hp d'.
 Proof with try tauto.
  intros.
  unfold h_update_size.
  unfold h_find,get_h;simpl.
  destruct hp as [hp pf];simpl.
  unfold find_parents.
  rewrite find_parents_aux_update_size.
  rewrite kelements_update_size...
 Qed.

 (*
  SECTION 8: Define union
 *)  

 Definition h_union (hp : vheap) (d1 d2 : t) : vheap :=
  match (h_cfind hp d1) with
  |(Some d1', hp') => 
   match (h_cfind hp' d2) with
   |(Some d2',hp'') => 
     if e_eq_dec d1' d2' then hp'' 
     else 
       match (find d1' (get_h hp''),find d2' (get_h hp'')) with
        |(Some hn1,Some hn2) => 
          if Compare_dec.le_dec (size hn1) (size hn2) then
           let hp1 := h_update_pt hp'' d1' d2' in
             h_update_size hp1 d2' (S (size hn1))
          else
           let hp2 := h_update_pt hp'' d2' d1' in
             h_update_size hp2 d1' (S (size hn2))
        |_ => hp''
       end
   |_ => hp'
   end
  | _ => hp
  end.

End Union_Find_Base.

