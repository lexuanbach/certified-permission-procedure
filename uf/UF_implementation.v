Add LoadPath "..".
Require Import base.
Require Import Classical.
Require Import rbt.MMapInterface.
Require Import UF_interface.
Require Import UF_base.

Module Union_Find (Import Input : INPUT) 
                  (Import ot : OrderedType with Definition t := Input.e
                                           with Definition eq := @Logic.eq Input.e) <:
                   UNION_FIND Input.

 Module UFB := Union_Find_Base Input ot.
 Import UFB.

 Definition t := vheap.
 
 Definition empty : t := h_empty.
  (* Create a new singleton element *)
 Definition singleton : t -> e -> t := h_singleton.
  (* Union two elments *)
 Definition union : t -> e -> e -> t := h_union.
  (* Find the principal element *)
 Definition find : t -> e -> option e * t := h_cfind.

 Definition find_e s el :=
   fst (find s el).
 Definition find_t s el :=
   snd (find s el).

 Definition In (s : t) (el : e) : Prop :=
   is_Some (find_e s el).

 Definition set_in (s : t) (S : @set e) : Prop :=
   S = empty_set \/ exists rt, S rt /\ forall x, S x <-> find_e s x = Some rt.

 Definition equiv_e (s : t) (e1 e2 : e) : Prop :=
   find_e s e1 = find_e s e2.
 
 Definition set_of (s : t) (el : e) : e -> Prop :=
   fun el' => equiv_e s el el'.

 Definition subset_t (s1 s2 : t) : Prop :=
   forall S, set_in s1 S -> set_in s2 S.

 Definition equiv_t (s1 s2 : t) : Prop :=
   subset_t s1 s2 /\ subset_t s2 s1.

 Lemma find_empty : forall el,
  find_e empty el = None.
 Proof with try tauto.
  intros. rewrite h_cfind_reduce1.
  apply h_find_empty.
 Qed.

 Lemma find_idempotent : forall s el el',
   find_e s el = Some el' ->
   find_e s el' = Some el'.
 Proof with try tauto.
  intros. repeat rewrite h_cfind_reduce1 in *.
  apply h_find_root_id.
  apply h_find_root with (d:=el)...
 Qed.
 
 Lemma find_equiv : forall s el,
   equiv_t s (find_t s el).
 Proof with try tauto.
  repeat intro.
  unfold equiv_t;split;repeat intro.
  destruct H;subst. left...
  destruct H as [d' [H H1]].
  right. exists d'. split... intros.
  rewrite H1. repeat rewrite h_cfind_reduce1...
  rewrite h_cfind_reduce2...
  destruct H. subst. left...
  destruct H as [d' [H1 H2]].
  right. exists d'. split... intros.
  rewrite H2. repeat rewrite h_cfind_reduce1...
  rewrite h_cfind_reduce2...
 Qed.

 Lemma In_equiv: forall hp d,
  In hp d <-> RBT.In d (get_h hp).
 Proof with try tauto. 
  intros. unfold In,is_Some.
  unfold find_e,find. unfold t in *.
  change (fst (h_cfind hp d)) with (h_cfind_r hp d).
  case_eq (h_cfind_r hp d);intros;
  rewrite h_cfind_reduce1 in H.
  split;intros...
  apply h_find_exist;eauto.
  split;intros...
  apply h_find_exist in H0. destruct H0. congruence.
 Qed.

 Definition set_in' hp (S : @set RBT.key) : Prop :=
   S = empty_set \/ exists d', S d' /\ forall d, S d <-> h_find hp d = Some d'. 

 Lemma set_in_equiv: forall hp S,
  set_in hp S <-> set_in' hp S.
 Proof with try tauto.
  intros.
  unfold set_in,set_in'.
  split;intros;destruct H...
  destruct H as [d' [? ?]].
  right. exists d'. split... intros...
  rewrite H0. rewrite h_cfind_reduce1...
  destruct H as [d' [? ?]].
  right. exists d'. split... intros...
  rewrite H0. rewrite h_cfind_reduce1...
 Qed.
  
 Lemma singleton_set_in_refl: forall s el,
   ~In s el -> set_in (singleton s el) (set_singleton el).
 Proof with try tauto.
  intros. rewrite In_equiv in H. 
  rewrite set_in_equiv. right.
  exists el. split. unfold set_singleton...
  intros. unfold set_singleton.
  rewrite h_singleton_find1...
  split;intro;subst...
 Qed.
 
 Lemma singleton_set_in: forall s el,
   ~In s el -> forall S,
    set_in s S -> set_in (singleton s el) S.
 Proof with try tauto.
  intros.
  rewrite In_equiv in H.
  rewrite set_in_equiv in *.
  destruct H0. subst. left...
  destruct H0 as [d' [H0 H1]].
  right. exists d'. split... intros.
  assert (~S el).
   intro. apply H1 in H2.
   apply H. apply h_find_exist. eauto.
  destruct (e_eq_dec d el);subst;intros.
  split;intros...
  rewrite h_singleton_find3 in H3... inv H3...
  rewrite H1.
  rewrite h_singleton_find2...
 Qed.

 Lemma set_in_singleton: forall s el,
   ~In s el -> forall S, 
   set_in (singleton s el) S -> (S = set_singleton el \/ set_in s S).
 Proof with try tauto.
  intros.
  rewrite In_equiv in H.
  rewrite set_in_equiv in *.
  destruct H0. right. left...
  destruct H0 as [d' [H0 H1]].
  destruct (e_eq_dec d' el);subst.
  left. extensionality d'.
  apply prop_ext. unfold set_singleton.
  rewrite H1.
  rewrite h_singleton_find1... split;intro;subst...
  right. right. exists d'. split... intros.
  split;intros.
  assert (d <> el).
   intro;subst. apply H1 in H2.
   rewrite h_singleton_find3 in H2...
   inv H2...
  apply H1 in H2.
  rewrite h_singleton_find2 in H2...
  apply H1. rewrite h_singleton_find2...
  intro;subst. apply H. apply h_find_exist. eauto.
 Qed.

 Lemma union_set_in_refl: forall s S1 S2 e1 e2,
    set_in s S1 -> set_in s S2 ->
    S1 e1 -> S2 e2 -> 
    set_in (union s e1 e2) (set_union S1 S2).
 Proof with try tauto.
  intros. rewrite set_in_equiv in *.
  destruct H;subst. inv H1.
  destruct H0;subst. inv H2.
  destruct H as [d1' [H3 H4]].
  destruct H0 as [d2' [H5 H6]].
  right. unfold union,h_union.
  case_eq (h_cfind s e1);intros.
  apply h_cfind_rewrite in H. destruct H.
  rewrite h_cfind_reduce1 in *.
  icase o;subst.
  assert (e0 = d1') by (apply H4 in H1;congruence). subst.
  case_eq (h_cfind (h_cfind_hp s e1) e2);intros.
  apply h_cfind_rewrite in H. destruct H. 
  rewrite h_cfind_reduce1 in *.
  rewrite h_cfind_reduce2 in *.
  icase o;subst.
  assert (e0 = d2') by (apply H6 in H2;congruence). subst.
  destruct (e_eq_dec d1' d2');subst... unfold set_union.
  - exists d2'. split... 
    intros. repeat rewrite h_cfind_reduce2.
    split;intros. destruct H. apply H4... apply H6...
    apply H6 in H...
  - assert (RBT.In d1' (get_h s)).
     apply root_In. eapply h_find_root;eauto.
    assert (RBT.In d2' (get_h s)).
     apply root_In. eapply h_find_root;eauto.
    rewrite <- h_cfind_reduce3  with (d:=e1)in H,H8.
    rewrite <- h_cfind_reduce3  with (d:=e2)in H,H8.
    apply find_In in H. apply find_In in H8.
    destruct H as [hn1 H]. destruct H8 as [hn2 H8].
    rewrite H,H8.
    assert (is_root d1' (get_h s)).
      eapply h_find_root;eauto...
    assert (is_root d2' (get_h s)).
      eapply h_find_root;eauto...
    destruct (Compare_dec.le_dec (size hn1) (size hn2)).
     * exists d2'. unfold set_union. split... intros.
       rewrite h_update_size_reduce.
       split;intros. destruct H11.
       apply H4 in H11.
       rewrite<- h_cfind_reduce2 with (d:=e1) in H11.
       rewrite<- h_cfind_reduce2 with (d:=e2) in H11.
       unfold h_find in H11. revert H11.
       case_eq (find_parents (get_h (h_cfind_hp (h_cfind_hp s e1) e2)) d);disc.
       intros. destruct p. inv H12.
       eapply h_update_pt_h_find1;eauto.
       repeat rewrite h_cfind_reduce3...
       apply root_In...
       repeat rewrite h_cfind_reduce4... simpl...

       apply H6 in H11.
       rewrite<- h_cfind_reduce2 with (d:=e1) in H11.
       rewrite<- h_cfind_reduce2 with (d:=e2) in H11.
       unfold h_find in H11. revert H11.
       case_eq (find_parents (get_h (h_cfind_hp (h_cfind_hp s e1) e2)) d);disc.
       intros. destruct p. inv H12.
       eapply h_update_pt_h_find2;eauto.
       repeat rewrite h_cfind_reduce3...
       apply root_In. eapply h_find_root;eauto.
       repeat rewrite h_cfind_reduce4...
       intro. destruct H12;subst...
       eapply find_parents_aux_root_not_In in H11;eauto.
       repeat rewrite h_cfind_reduce4.
       eapply h_find_root;eauto.

       apply h_update_pt_h_find3 in H11...
       destruct H11. left. apply H4.
       repeat rewrite h_cfind_reduce2 in H11...
       right. apply H6.
       repeat rewrite h_cfind_reduce2 in H11...
       repeat rewrite h_cfind_reduce4...
       repeat rewrite h_cfind_reduce4...
     * exists d1'. unfold set_union. split... intros.
       rewrite h_update_size_reduce.
       split;intros. destruct H11.
       apply H4 in H11.
       rewrite<- h_cfind_reduce2 with (d:=e1) in H11.
       rewrite<- h_cfind_reduce2 with (d:=e2) in H11.
       unfold h_find in H11. revert H11.
       case_eq (find_parents (get_h (h_cfind_hp (h_cfind_hp s e1) e2)) d);disc.
       intros. destruct p. inv H12.
       eapply h_update_pt_h_find2;eauto.
       repeat rewrite h_cfind_reduce3...
       apply root_In...
       repeat rewrite h_cfind_reduce4...
       intro. destruct H12;subst...
       eapply find_parents_aux_root_not_In in H11;eauto.
       repeat rewrite h_cfind_reduce4.
       eapply h_find_root;eauto.

       apply H6 in H11.
       rewrite<- h_cfind_reduce2 with (d:=e1) in H11.
       rewrite<- h_cfind_reduce2 with (d:=e2) in H11.
       unfold h_find in H11. revert H11.
       case_eq (find_parents (get_h (h_cfind_hp (h_cfind_hp s e1) e2)) d);disc.
       intros. destruct p. inv H12.
       eapply h_update_pt_h_find1;eauto.
       repeat rewrite h_cfind_reduce3...
       apply root_In...
       repeat rewrite h_cfind_reduce4... simpl...

       apply h_update_pt_h_find3 in H11...
       destruct H11. right. apply H6.
       repeat rewrite h_cfind_reduce2 in H11...
       left. apply H4.
       repeat rewrite h_cfind_reduce2 in H11...
       repeat rewrite h_cfind_reduce4...
       repeat rewrite h_cfind_reduce4...
       intro;subst...
  - apply H6 in H2. congruence.
  - apply H4 in H1. congruence.
 Qed.
  
 Lemma union_set_in: forall s S1 S2 e1 e2,
   set_in s S1 -> set_in s S2 ->
   S1 e1 -> S2 e2 -> 
   forall S, S <> S1 -> S <> S2 -> set_in s S -> set_in (union s e1 e2) S.
 Proof with try tauto.
  intros. rewrite set_in_equiv in *.
  destruct H5; subst... left...
  destruct H5 as [d' [H5 H6]].
  right. exists d'.
  destruct H. subst;inv H1.
  destruct H0. subst;inv H2.
  destruct H as [d1' [H7 H8]].
  destruct H0 as [d2' [H9 H10]].
  assert (d' <> d1' /\ d' <> d2').
   split;intro;subst...
   apply H3. extensionality. apply prop_ext.
   rewrite H6,H8...
   apply H4. extensionality. apply prop_ext.
   rewrite H6,H10...
  destruct H as [H11 H12].
  split... intros.
  unfold union,h_union.
  case_eq (h_cfind s e1);intros.
  apply h_cfind_rewrite in H. destruct H.
  rewrite h_cfind_reduce1 in *.
  icase o;subst.
  assert (e0 = d1') by (apply H8 in H1;congruence). subst.
  case_eq (h_cfind (h_cfind_hp s e1) e2);intros.
  apply h_cfind_rewrite in H. destruct H. 
  rewrite h_cfind_reduce1 in *.
  rewrite h_cfind_reduce2 in *.
  rewrite H6.
  icase o;subst.
  assert (e0 = d2') by (apply H10 in H2;congruence). subst.
  destruct (e_eq_dec d1' d2');subst...
  repeat rewrite h_cfind_reduce2...
  case_eq (RBT.find d1' (get_h (h_cfind_hp (h_cfind_hp s e1) e2)));intros.
  case_eq (RBT.find d2' (get_h (h_cfind_hp (h_cfind_hp s e1) e2)));intros.
  destruct (Compare_dec.le_dec (size h) (size h0));rewrite h_update_size_reduce.
  - rewrite h_update_pt_h_find4...
    repeat rewrite h_cfind_reduce2...
    repeat rewrite h_cfind_reduce4.
    eapply h_find_root;eauto.
    repeat rewrite h_cfind_reduce4.
    eapply h_find_root;eauto.
  - rewrite h_update_pt_h_find4...
    repeat rewrite h_cfind_reduce2...
    repeat rewrite h_cfind_reduce4.
    eapply h_find_root;eauto.
    repeat rewrite h_cfind_reduce4.
    eapply h_find_root;eauto. intro;subst...
  - repeat rewrite h_cfind_reduce2...
  - repeat rewrite h_cfind_reduce2...
  - repeat rewrite h_cfind_reduce2...
 Qed.   

 Lemma set_eq: forall hp S1 S2 d,
  set_in hp S1 -> set_in hp S2 -> S1 d -> S2 d -> S1 = S2.
 Proof with try tauto.
  repeat intro. rewrite set_in_equiv in *.
  destruct H;subst. inv H1.
  destruct H0;subst. inv H2.
  destruct H as [d1' [H3 H4]].
  destruct H0 as [d2' [H5 H6]].
  apply H4 in H1. apply H6 in H2.
  rewrite H1 in H2;inv H2.
  extensionality. apply prop_ext.
  rewrite H4,H6...
 Qed.
 
 Lemma set_in_union: forall s S1 S2 e1 e2,
  set_in s S1 -> set_in s S2 ->
  S1 e1 -> S2 e2 -> 
  forall S, set_in (union s e1 e2) S -> S = set_union S1 S2 \/ set_in s S.
 Proof with try tauto.
  intros.
  generalize (union_set_in_refl _ _ _ _ _ H H0 H1 H2);intro Ha.
  rewrite set_in_equiv in *.
  destruct H;subst. inv H1.
  destruct H0;subst. inv H2.
  destruct H3;subst. right. left...
  destruct H as [d1' [H4 H5]].
  destruct H0 as [d2' [H6 H7]].
  destruct H3 as [d' [H8 H9]].
  destruct (classic (S = set_union S1 S2))...
  assert (d' <> d1' /\ d' <> d2'). unfold set_union in H.
   split;intro H10;symmetry in H10;subst;apply H;
   apply set_eq with (d:=d') (hp:= union s e1 e2);
   try rewrite set_in_equiv in *...
   right;eauto. right;eauto.
  destruct H0.
  right. right.
  exists d'. split... intros.
  rewrite H9. unfold union,h_union.
  case_eq (h_cfind s e1). intros.
  apply h_cfind_rewrite in H10. destruct H10.
  rewrite h_cfind_reduce1 in *.
  icase o;subst.
  Focus 2 . rewrite H5 in H1. congruence.
  assert (e0 = d1') by (apply H5 in H1;congruence). subst.
  case_eq (h_cfind (h_cfind_hp s e1) e2). intros ? ? ?.
  apply h_cfind_rewrite in H10. destruct H10. 
  rewrite h_cfind_reduce1 in *.
  rewrite h_cfind_reduce2 in *.
  icase o;subst.
  Focus 2. rewrite H7 in H2. congruence.
  assert (e0 = d2') by (apply H7 in H2;congruence). subst.
  destruct (e_eq_dec d1' d2');subst...
  repeat rewrite h_cfind_reduce2...
  case_eq (RBT.find d1' (get_h (h_cfind_hp (h_cfind_hp s e1) e2)));intros.
  case_eq (RBT.find d2' (get_h (h_cfind_hp (h_cfind_hp s e1) e2)));intros.
  destruct (Compare_dec.le_dec (size h) (size h0));
  rewrite h_update_size_reduce;intros.
  - rewrite h_update_pt_h_find4...
    repeat rewrite h_cfind_reduce2...
    repeat rewrite h_cfind_reduce4...
    eapply h_find_root;eauto.
    repeat rewrite h_cfind_reduce4...
    eapply h_find_root;eauto.
  - rewrite h_update_pt_h_find4...
    repeat rewrite h_cfind_reduce2...
    repeat rewrite h_cfind_reduce4...
    eapply h_find_root;eauto.
    repeat rewrite h_cfind_reduce4...
    eapply h_find_root;eauto. intro;subst...
  - apply find_not_In in H13.
    repeat rewrite h_cfind_reduce3 in H13.
    apply h_find_root in H12. apply root_In in H12...
  - apply find_not_In in H10.
    repeat rewrite h_cfind_reduce3 in H10.
    apply h_find_root in H11. apply root_In in H11...
 Qed.

End Union_Find. 