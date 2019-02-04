Require Import base.
Require Import Classical.

(* For RBT we'll need an ordering *)
Module Type INPUT.
  Parameter e : Type.
(*  Parameter an_e : e. *)
  Parameter e_eq_dec : 
    forall e1 e2 : e, {e1 = e2} + {e1 <> e2}.
End INPUT.

Module An_Input : INPUT.
  Definition e : Type := nat.
(*  Definition an_e : e := 0. *)
  Definition e_eq_dec : 
    forall e1 e2 : e, {e1 = e2} + {e1 <> e2}.
  unfold e. induction e1.
  destruct e2. left. trivial. right. intro. discriminate.
  destruct e2. right. intro. discriminate.
  destruct (IHe1 e2). subst. left. trivial.
  right. intro. inversion H. subst. apply n. trivial.
  Defined.
End An_Input.

Module Type UNION_FIND(Import i : INPUT).
  Parameter t : Type.
  
  (* Empty structure *)
  Parameter empty : t.
  (* Create a new singleton element *)
  Parameter singleton : t -> e -> t.
  (* Union two elments *)
  Parameter union : t -> e -> e -> t.
  (* Find the principal element *)
  Parameter find : t -> e -> option e * t.
  
  Definition find_e s el :=
    fst (find s el).
  Definition find_t s el :=
    snd (find s el).
  
  Definition In (s : t) (el : e) : Prop :=
    is_Some (find_e s el).

  Definition set_in (s : t) (S : @set e) : Prop :=
    S = empty_set \/ exists rt, S rt /\ forall x, S x <-> find_e s x = Some rt.
(*
rhs can still have empty set:
  Definition set_in (s : t) (S : @set e) : Prop :=
    S = empty_set \/ exists rt, forall x, S x <-> find_e s x = Some rt.

Doesn't allow empty set:
  Definition set_in (s : t) (S : @set e) : Prop :=
    exists rt, S rt /\ forall x, S x <-> find_e s x = Some rt.

Don't remember:
  Definition set_in (s : t) (S : @set e) : Prop :=
    exists rt, forall x, S x <-> find_e s x = Some rt.

Don't remember:
  Definition set_in (s : t) (S : @set e) : Prop :=
    forall x, S x -> S = set_of s x
*)

  Definition equiv_e (s : t) (e1 e2 : e) : Prop :=
(* In s e1 /\ ?? *)
    find_e s e1 = find_e s e2.
  
  Definition set_of (s : t) (el : e) : e -> Prop :=
    fun el' => equiv_e s el el'.

  Definition subset_t (s1 s2 : t) : Prop :=
    forall S, set_in s1 S -> set_in s2 S.

  Definition equiv_t (s1 s2 : t) : Prop :=
    subset_t s1 s2 /\ subset_t s2 s1.

  (* Axioms about empty *)
  Axiom find_empty : forall el,
    find_e empty el = None.

  (* Axioms about find *)
  Axiom find_idempotent : forall s el el',
    find_e s el = Some el' ->
    find_e s el' = Some el'.
  
  Axiom find_equiv : forall s el,
    equiv_t s (find_t s el).
  
  (* Axioms about singleton *)
  Axiom singleton_set_in_refl: forall s el,
    ~In s el -> set_in (singleton s el) (set_singleton el).
  
  Axiom singleton_set_in: forall s el,
    ~In s el -> forall S,
      set_in s S -> set_in (singleton s el) S.
(* Equiv but doesn't follow the same pattern... better?
  Axiom singleton_set_in: forall s el,
    ~In s el -> subset_t s (singleton s el).
*)

  Axiom set_in_singleton: forall s el,
    ~In s el -> forall S, 
      set_in (singleton s el) S -> (S = set_singleton el \/ set_in s S).
  
  (* Axioms about union *)
  Axiom union_set_in_refl: forall s S1 S2 e1 e2,
    set_in s S1 -> set_in s S2 ->
    S1 e1 -> S2 e2 -> 
    set_in (union s e1 e2) (set_union S1 S2).
  
  (* Could state this with subsets maybe? *)
  Axiom union_set_in: forall s S1 S2 e1 e2,
    set_in s S1 -> set_in s S2 ->
    S1 e1 -> S2 e2 -> 
    forall S, S <> S1 -> S <> S2 -> set_in s S -> set_in (union s e1 e2) S.
    
  Axiom set_in_union: forall s S1 S2 e1 e2,
    set_in s S1 -> set_in s S2 ->
    S1 e1 -> S2 e2 -> 
    forall S, set_in (union s e1 e2) S -> S = set_union S1 S2 \/ set_in s S.
  (*This one may be useful*)
  (*
  Parameter elements : t -> list e.
  *)
(* An alternative:

  Axiom union_set_in_refl: forall s e1 e2,
    In s e1 -> In s e2 ->
    set_in (union s e1 e2) (set_union (set_of s e1) (set_of s e2)).

  Axiom union_set_in: forall s e1 e2,
    In s e1 -> In s e2 -> 
      forall S, set_in s S -> 
        S <> set_of s e1 -> S <> set_of s e2 ->
          set_in (union s e1 e2) S.

  Axiom set_in_union: forall s e1 e2,
    In s e1 -> In s e2 ->
      forall S, set_in (union s e1 e2) S ->
        (S = set_union (set_of s e1) (set_of s e2) \/ set_in s S).

*)
  
  
  (* Other axioms, up for discussion *)
  (*
  Axiom In_finite: forall s, exists L,
    forall el, List.In el L <-> In s el.
  *)
  
  (* Other operations, up for discussion *)
  (*
  Parameter elements : t -> list e.
  Parameter sets : t -> list (list e).
  *)


(* Alternative, stronger version: requires not
   only equal sets, but equal principal elements. *)
(*

  Definition equiv_t' (s1 s2 : t) : Prop :=
    forall el, find_e s1 el = find_e s2 el.
  
  Lemma equiv_t'_t: forall s1 s2,
    equiv_t' s1 s2 -> equiv_t s1 s2.
  Proof.
    intros.
    unfold equiv_t' in H. unfold equiv_t.
    unfold subset_t,set_in.
    split;intros. destruct H0. left;trivial.
    right. destruct H0 as [? [? ?]].
    exists x. split;trivial. intros. firstorder.
    rewrite<- H. apply H1. trivial.
    apply H1. rewrite H.  trivial.
    destruct H0. left;trivial.
    right. destruct H0 as [? [? ?]].
    exists x. split;trivial. intros. firstorder.
    rewrite H. apply H1. trivial.
    apply H1. rewrite<- H.  trivial.
  Qed.


  (* Axioms about find *)
  Axiom find_equiv' : forall s el,
    equiv_t' s (find_t s el).

  Lemma find_equiv2 : forall s el,
    equiv_t s (find_t s el).
  Proof.
    intros. apply equiv_t'_t.
    apply find_equiv'.
  Qed.

  (* Axiom about singeton *)
  Axiom find_singleton': forall s el,
    ~In s el ->
    (find_e (singleton s el) el = Some el) /\
    (forall el', el <> el' -> 
       find_e (singleton s el) el' = find_e s el').
(*This proof is broken so I temporarily change it to Axiom*)
  Axiom find_singleton: forall s el,
    ~In s el ->
    (find_e (singleton s el) el = Some el) /\
    (forall el', In s el' ->
       set_of (singleton s el) el' = set_of s el') /\
    (forall el', el' <> el -> ~In s el' -> 
       ~In (singleton s el) el').
  (*
  Proof.
    intros.
    copy H.
    apply find_singleton' in H.
    destruct H. split; trivial. (* clear H. *)
    split. intros.
    extensionality el''.
    unfold set_of, equiv_e.
    assert (el <> el') by (intro; subst; contr).
    rewrite H1; auto.
    case (e_eq_dec el el''); intros.
    2: rewrite H1; auto.
    subst el''. rewrite H.
    apply prop_ext; split; intro.
    apply find_trans in H4.
    destruct H0. red. rewrite H4. red. trivial.
    destruct H0. unfold In in *. rewrite <- H4; auto.
    intros.
    intro. apply H3.
    unfold In in H4.
    rewrite H1 in H4; auto.
  Qed.
  *)
*)

End UNION_FIND.

Module UnionFind_Lemmas(Import i : INPUT) (Import uf : UNION_FIND(i)).
  (* Facts about In *)
  Lemma In_dec: forall s el,
    {In s el} + {~In s el}.
  Proof.
    intros. unfold In.
    case find_e. left. red. trivial.
    right. intro. apply H.
  Qed.
  
  Lemma not_In: forall s el,
    ~In s el ->
    find_e s el = None.
  Proof.
    unfold In. intros ? ?. case find_e; auto; intros.
    destruct H. red. trivial.
  Qed.
  
  (* Facts about set_in and set_of *)
  Lemma set_in_unique: forall s S1 S2 e,
    set_in s S1 ->
    set_in s S2 ->
    S1 e ->
    S2 e ->
    S1 = S2.
  Proof.
    intros. extensionality x.
    destruct H; destruct H0; subst; contr.
    destruct H as [p1 [_ ?]]. destruct H0 as [p2 [_ ?]].
    rewrite H in H1. rewrite H0 in H2.
    rewrite H1 in H2. inv H2.
    apply prop_ext.
    rewrite H, H0.
    tauto.
  Qed.

  Lemma set_of_refl: forall s e,
    set_of s e e.
  Proof.
    unfold set_of, equiv_e. auto.
  Qed.
  
  Lemma set_of_nonempty: forall s e,
    set_of s e <> empty_set.
  Proof.
    intros ? ? ?.
    assert (empty_set e0); contr.
    rewrite <- H.
    apply set_of_refl.
  Qed.
  
  Lemma set_of_in: forall s e,
    In s e ->
    set_in s (set_of s e).
  Proof.
    intros. red in H.
    remember (find_e s e0). right. icase o. exists e1.
    unfold set_of, equiv_e. split.
    rewrite <- Heqo.
    symmetry in Heqo. apply find_idempotent in Heqo. auto.
    intro. rewrite <- Heqo. split; auto.
  Qed.
  
  Lemma in_set_of: forall s S e,
    set_in s S ->
    S e ->
    S = set_of s e.
  Proof.
    intros. extensionality x.
    destruct H. subst. contr.
    destruct H as [p [_ ?]].
    unfold set_of, equiv_e.
    apply prop_ext. split; intro.
    rewrite H in H0, H1.
    congruence.
    rewrite H in H0.
    rewrite H0 in H1.
    symmetry in H1.
    rewrite <- H in H1.
    trivial.
  Qed.

  Lemma equiv_e_set: forall s e1 e2,
    (In s e1 /\ equiv_e s e1 e2) <-> (exists S, S e1 /\ S e2 /\ set_in s S).
  Proof.
    split; intro.
    exists (set_of s e1).
    split. apply set_of_refl.
    split. apply H.
    apply set_of_in. apply H.
    destruct H as [S [? [? ?]]].
    destruct H1. subst. contr.
    destruct H1 as [p [_ ?]].
    destruct (H1 e1). destruct (H1 e2).
    spec H2 H. spec H4 H0.
    split; red. rewrite H2. red. trivial.
    congruence.
  Qed.
  
  (* Facts about equiv_t *)
  Lemma equiv_t_alt: forall s1 s2,
    equiv_t s1 s2 <-> (forall S, set_in s1 S <-> set_in s2 S).
  Proof.
    unfold equiv_t, subset_t.
    split; intros.
    split; intros; destruct H; auto.
    split; intros.
    rewrite H in H0. trivial.
    rewrite <- H in H0. trivial.
  Qed.

  Lemma equiv_t_not_in': forall s1 s2,
    equiv_t s1 s2 ->
    forall e, find_e s1 e = None <-> find_e s2 e = None.
  Proof.
    intros.
    case_eq (find_e s1 e0); case_eq (find_e s2 e0); intros;
    split; auto; disc; intros _; rewrite equiv_t_alt in H;
    [spec H (set_of s1 e0) | spec H (set_of s2 e0)];
    destruct H.
    spec H. apply set_of_in. red. red. rewrite H1. trivial.
    destruct H. apply set_of_nonempty in H. contr.
    destruct H as [p [_ ?]]. spec H e0.
    destruct H. rewrite H in H0. discriminate. apply set_of_refl.
    spec H2. apply set_of_in. red. red. rewrite H0. trivial.
    destruct H2. apply set_of_nonempty in H2. contr.
    destruct H2 as [p [_ ?]]. spec H2 e0.
    destruct H2. rewrite H2 in H1. discriminate. apply set_of_refl.
  Qed.

  Lemma equiv_t_not_in: forall s1 s2,
    equiv_t s1 s2 ->
    forall e, ~In s1 e <-> ~In s2 e.
  Proof.
    intros. generalize (equiv_t_not_in' _ _ H e0); intro.
    unfold In, is_Some.
    revert H0.
    case (find_e s1 e0); case (find_e s2 e0); intros; try tauto.
    destruct H0. spec H1; auto. inversion H1.
    destruct H0. spec H0; auto. inversion H0.
  Qed.

  (* This is very tedious but it's a kind of sanity check *)
  Lemma equiv_t_alt': forall s1 s2,
    equiv_t s1 s2 <-> 
(* This first conjunct is a bit annoying.  There are some ways to get around it,
   such as by pointing out all sets must be finite, but they are also annoying... *)
    (forall el, (In s1 el <-> In s2 el) /\ set_of s1 el = set_of s2 el).
  Proof.
    split; intros.
     case (In_dec s1 el); case (In_dec s2 el); intros.
       split. tauto.
        apply (set_in_unique s2 _ _ el).
        apply set_of_in in i0.
        rewrite equiv_t_alt in H.
        spec H (set_of s1 el). tauto.
        apply set_of_in. auto.
        apply set_of_refl.
        apply set_of_refl.
       rewrite <- equiv_t_not_in in n; eauto. contradiction.
       rewrite equiv_t_not_in in n; eauto. contradiction.
       split. tauto.
        apply not_In in n. apply not_In in n0.
        extensionality x.
        apply prop_ext. unfold set_of, equiv_e. split; intro.
         rewrite n0 in H0.
          case (In_dec s2 x); intro.
          rewrite equiv_t_alt in H.
          spec H (set_of s2 x). destruct H. spec H1.
          apply set_of_in; trivial.
          destruct H1. apply set_of_nonempty in H1. contr. 
          destruct H1 as [rt [_ ?]]. spec H1 x. destruct H1.
          spec H1. apply set_of_refl. rewrite H1 in H0. discriminate.
          rewrite n.
          apply not_In in n1. rewrite n1. trivial.
         rewrite n in H0.
          case (In_dec s1 x); intro.
          rewrite equiv_t_alt in H.
          spec H (set_of s1 x). destruct H. spec H.
          apply set_of_in; trivial.
          destruct H. apply set_of_nonempty in H. contr. 
          destruct H as [rt [_ ?]]. spec H x. destruct H.
          spec H. apply set_of_refl. rewrite H in H0. discriminate.
          rewrite n0.
          apply not_In in n1. rewrite n1. trivial.
     rewrite equiv_t_alt. split; intros.
       destruct H0. left. trivial.
        destruct H0 as [rt [? ?]].
        rewrite H1 in H0.
        generalize (H rt). intros [? ?].
        (* Here is where we need the annoying conjunct *)
        assert (In s2 rt) by (rewrite <- H2; red; rewrite H0; apply I).
        red in H4.
        remember (find_e s2 rt). icase o. clear H4.
        rename e0 into rt'. symmetry in Heqo.
        assert (find_e s2 rt' = Some rt'). eapply find_idempotent; eauto.
        assert (set_of s1 rt rt'). rewrite H3. red. red. congruence.
        red in H5. red in H5. rewrite H0 in H5. symmetry in H5.
        right. exists rt'. split.
        rewrite H1. trivial.
        intro. rewrite H1. clear H1 S.
        unfold set_of, equiv_e in H3.
        rewrite H0, Heqo in H3.
        split; intro.
        assert ((fun el' => Some rt = find_e s1 el') x) by auto. rewrite H3 in H6. auto.
        assert ((fun el' => Some rt' = find_e s2 el') x) by auto. rewrite <- H3 in H6. auto.
       destruct H0. left. trivial.
        destruct H0 as [rt [? ?]].
        rewrite H1 in H0.
        generalize (H rt). intros [? ?].
        (* Here is where we need the annoying conjunct *)
        assert (In s1 rt) by (rewrite H2; red; rewrite H0; apply I).
        red in H4.
        remember (find_e s1 rt). icase o. clear H4.
        rename e0 into rt'. symmetry in Heqo.
        assert (find_e s1 rt' = Some rt'). eapply find_idempotent; eauto.
        assert (set_of s2 rt rt'). rewrite <- H3. red. red. congruence.
        red in H5. red in H5. rewrite H0 in H5. symmetry in H5.
        right. exists rt'. split.
        rewrite H1. trivial.
        intro. rewrite H1. clear H1 S.
        unfold set_of, equiv_e in H3.
        rewrite H0, Heqo in H3.
        split; intro.
        assert ((fun el' => Some rt = find_e s2 el') x) by auto. rewrite <- H3 in H6. auto.
        assert ((fun el' => Some rt' = find_e s1 el') x) by auto. rewrite H3 in H6. auto.
  Qed.

  (* Facts about empty *)
  Lemma empty_set_in: forall s,
    set_in s empty_set.
  Proof. red. auto. Qed.
  
  Lemma set_in_empty: forall S,
    set_in empty S ->
    S = empty_set.
  Proof.
    intros.
    destruct H; auto.
    extensionality x. unfold empty_set. apply prop_ext. split; intro; contr.
    destruct H as [rt [_ ?]].
    rewrite H in H0. rewrite find_empty in H0.
    disc.
  Qed.

  Lemma set_singleton_find: forall uf e,
   set_in uf (set_singleton e) -> find_e uf e = Some e.
  Proof.
   intros.
   destruct H.
   assert (empty_set e0).
    rewrite <-H. congruence.
   assert (set_singleton e0 e0 = empty_set e0).
   inv H. trivial. inv H0.
   destruct H as [? [? ?]]. inv H.
   apply H0. unfold set_singleton. trivial.
  Qed.
  Lemma In_Some: forall uf e,
   In uf e <-> (exists e', find_e uf e = Some e').
  Proof with firstorder.
   intros.
   unfold In,is_Some.
   case (find_e uf e0)...
   exists e1...
   inv H.
  Qed.
  Lemma set_of_In: forall uf e,
   (set_of uf e) e.
  Proof with auto.
   intros. unfold set_of,equiv_e...
  Qed.
  Lemma set_in_set_of: forall uf S e1 e2,
   set_of uf e1 e2 ->
   set_in uf S ->
   S e1 -> S e2.
  Proof with (try tauto;try congruence).
   intros.
   destruct H0. rewrite H0 in H1. inv H1.
   destruct H0 as [? [? ?]].
   unfold set_of,equiv_e in H.
   apply H2. apply H2 in H1...
  Qed.
  Lemma Some_set_of: forall uf e e',
   find_e uf e = Some e' ->
   set_of uf e e'.
  Proof with auto.
   intros. 
   unfold set_of,equiv_e.
   rewrite H;symmetry.
   apply find_idempotent with e0...
  Qed.
  Lemma In_set_of: forall uf e,
   In uf e <-> set_in uf (set_of uf e).
  Proof with (try tauto;try congruence).
   intros. split;intros.
   right. copy H. apply In_Some in H.
   destruct H. exists x.
   split. apply Some_set_of...
   intros.  
   split;intros...
   unfold set_in in H.
   destruct H.
   assert (empty_set e0).
    rewrite<- H. congruence.
   inv H0.
   destruct H as [? [? ?]].
   apply In_Some.
   exists x. apply H0...
  Qed.
  Lemma In_set_in: forall uf e,
   In uf e <-> (exists S, set_in uf S /\ S e).
  Proof with auto.
   intros.
   split;intros.
   exists (set_of uf e0).
   split. apply In_set_of...
   apply set_of_refl.
   destruct H as [? [? ?]].
   destruct H. subst. inv H0.
   destruct H as [? [? ?]].
   apply H1 in H0.
   apply In_Some. exists x0...
  Qed.
  Lemma In_None: forall uf e,
   ~In uf e <-> find_e uf e = None.
  Proof with auto.
   intros.
   rewrite In_Some.
   split;intros.
   icase (find_e uf e0).
   elimtype False. apply H. exists e1...
   intro. destruct H0. congruence.
  Qed.
  Lemma singleton_set_of: forall uf e e1 e2,
   ~In uf e ->
   In uf e1 ->
   set_of uf e1 e2 ->
   In (singleton uf e) e1 /\ set_of (singleton uf e) e1 e2.
  Proof with (try tauto;try congruence).
   intros.
   apply singleton_set_in with (S:= (set_of uf e1))in H;
   try apply In_set_of...
   destruct H.
   assert (empty_set e1). rewrite <- H. apply set_of_refl.
   inv H2.
   destruct H as [? [? ?]].
   split. apply In_Some.
   exists x. apply H2...
   unfold set_of,equiv_e.
   apply H2 in H1.
   rewrite H1. apply H2. apply set_of_refl.
  Qed.
  Lemma equiv_relf: forall uf,
   equiv_t uf uf.
  Proof. firstorder. Qed.
  Lemma equiv_comm: forall uf uf',
   equiv_t uf uf' -> equiv_t uf' uf.
  Proof. firstorder. Qed.
  Lemma equiv_trans: forall uf uf' uf'',
   equiv_t uf uf' -> equiv_t uf' uf'' ->
   equiv_t uf uf''.
  Proof with auto. 
   intros.
   unfold equiv_t,subset_t in *.
   split;intros.
   apply H0. apply H...
   apply H. apply H0...
  Qed.
  Lemma set_of_comm: forall uf e e',
   set_of uf e e' -> set_of uf e' e.
  Proof. firstorder. Qed.
  Lemma set_of_trans: forall uf e e' e'',
   set_of uf e e' -> set_of uf e' e'' ->
   set_of uf e e''.
  Proof. congruence. Qed.
  Lemma set_in_equiv: forall uf uf',
   equiv_t uf uf' ->
   (forall S, set_in uf S <-> set_in uf' S).
  Proof.
   intros.
   destruct H.
   spec H S. spec H0 S. tauto.
  Qed.
  Lemma In_equiv: forall uf uf',
   equiv_t uf uf' ->
   (forall e, In uf e <-> In uf' e).
  Proof with tauto.
   intros.
   repeat rewrite In_set_in.
   split;intros;destruct H0 as [? [? ?]];
   apply set_in_equiv with (S:= x) in H; 
   exists x...
  Qed.
  Lemma set_of_In_rewrite: forall uf e e',
    In uf e ->
    (set_of uf e e' <-> (exists S, set_in uf S /\ S e /\ S e')).   
  Proof with auto.
   intros.
   split;intros. copy H.
   apply In_set_in in H.
   destruct H as [? [? ?]].
   generalize (set_in_set_of _ _ _ _ H0 H H2);intro.
   exists x...
   intros.
   destruct H0 as [? [? [? ?]]].
   destruct H0. rewrite H0 in H1. inv H1.
   destruct H0 as [? [? ?]].
   rewrite H3 in H1.
   rewrite H3 in H2.
   congruence.
  Qed.
  Lemma In_set_of_In: forall uf e e',
   In uf e -> set_of uf e e' -> In uf e'.
  Proof.
   intros.
   apply In_Some in H. destruct H.
   apply In_Some. exists x. congruence.
  Qed.
  Lemma set_of_not_In_rewrite: forall uf e e',
   ~In uf e ->
   (set_of uf e e' <-> ~In uf e').
  Proof with auto.
   intros.
   split;intros.
   intro. apply H.
   apply set_of_comm in H0.
   apply In_set_of_In in H0...
   apply In_None in H. apply In_None in H0.
   congruence.
  Qed.
  Lemma equiv_set_of: forall uf uf' e e',
   equiv_t uf uf' ->
   set_of uf e e' -> set_of uf' e e'.
  Proof with auto.
   intros.
   generalize (In_dec uf e0);intro.
   destruct H1.
   generalize (In_set_of_In _ _ _ i H0);intro.
   apply set_of_In_rewrite with (e':=e') in i.
   apply i  in H0.
   destruct H0 as [? [? [? ?]]].
   destruct H. unfold subset_t in H.
   spec H x H0.
   apply set_of_In_rewrite...
   destruct H. subst. inv H2.
   destruct H as [? [? ?]].
   apply H5 in H2.
   apply In_Some. exists x0...
   exists x...
   copy n.
   apply set_of_not_In_rewrite with (e':=e') in n.
   apply n in H0.
   apply In_None in H0.
   apply In_None in n0.
   copy H.
   eapply equiv_t_not_in'  in H.
   rewrite H in H0.
   eapply equiv_t_not_in' in H1.
   rewrite H1 in n0.
   congruence. 
  Qed.
  Lemma set_of_rewrite: forall uf e e',
   set_of uf e e' <-> 
   find_e uf e = find_e uf e'.
  Proof. firstorder. Qed.
  Lemma set_of_find_reduce: forall uf e e' e'',
   set_of (find_t uf e) e' e''<-> set_of uf e' e''.
  Proof.
   intros.
   split;intros.
   eapply equiv_set_of.
   apply equiv_comm. apply find_equiv.
   apply H. eapply equiv_set_of.
   apply find_equiv. apply H.
  Qed.
  Lemma find_In: forall uf e e',
   find_e uf e = Some e' -> In uf e'.
  Proof with auto.
   intros.
   apply In_Some.
   exists e'.
   apply find_idempotent with e0...
  Qed.
  Lemma In_find_reduce: forall uf e e',
   In (find_t uf e') e <-> In uf e.
  Proof.
   intros.
   apply In_equiv.
   apply equiv_comm.
   apply find_equiv.
  Qed.
  Lemma union_combine: forall uf e1 e2,
   In uf e1 -> In uf e2 ->
   In (union uf e1 e2) e1 /\ set_of (union uf e1 e2) e1 e2.
  Proof with auto.
   intros.
   apply In_set_in in H. destruct H as [? [? ?]].
   apply In_set_in in H0. destruct H0 as [? [? ?]].
   generalize (union_set_in_refl _ _ _ _ _ H H0 H1 H2);intro.
   destruct H3.
   assert (empty_set e1). rewrite <-H3. left... inv H4.
   destruct H3 as [? [? ?]]. split;intros.
   apply In_Some. exists x1.
   apply H4. left...
   assert (set_union x x0 e1). left...
   apply H4 in H5.
   assert (set_union x x0 e2). right...
   apply H4 in H6.
   congruence.
  Qed.

  Lemma set_union_refl: forall {A} (S:@set A),
   set_union S S = S.
  Proof.
   intros.
   extensionality x. unfold set_union.
   apply prop_ext. tauto.
  Qed.
  Lemma set_union_comm: forall {A} (S1 S2:@set A),
   set_union S1 S2 = set_union S2 S1.
  Proof.
   intros.
   extensionality x.
   unfold set_union.
   apply prop_ext. tauto.
  Qed.
  Lemma set_union_subset: forall {A} (S1 S2:@set A) x,
   S1 x -> set_union S1 S2 x.
  Proof. firstorder. Qed.

  Definition set_disjoint {A} (S1 S2:@set A) : Prop:=
   forall v, ~(S1 v /\ S2 v).
  Lemma set_disjoint_comm: forall {A} (S1 S2:@set A),
   set_disjoint S1 S2 -> set_disjoint S2 S1.
  Proof. firstorder. Qed.

  Lemma set_in_union_equiv: forall uf S1 S2 v1 v2,
   set_in uf S1 -> set_in uf S2 ->
   S1 v1 -> S2 v2 ->
   forall S, set_in (union uf v1 v2) S <-> 
   ((S = set_union S1 S2) \/ (set_in uf S /\ set_disjoint S (set_union S1 S2))).
  Proof with auto.
   intros.
   split;intros.
   copy H3. 
   apply set_in_union with(S1:=S1)(S2:=S2) in H3...
   destruct H3. left...
   destruct (classic (S = S1));subst.
   assert (set_union S1 S2 = S1).
    apply set_in_unique with (s:=union uf v1 v2) (e0:=v1)...
    apply union_set_in_refl...
    apply set_union_subset...
  left. congruence.
  destruct (classic (S = S2));subst.
  assert (set_union S1 S2 = S2).
    apply set_in_unique with (s:=union uf v1 v2) (e0:=v2)...
    apply union_set_in_refl...
    rewrite set_union_comm.
    apply set_union_subset...
  left. congruence.
  right. split...
  repeat intro. destruct H7.
  destruct H8.
  apply H5. apply set_in_unique with (s:=uf)(e0:=v)...
  apply H6. apply set_in_unique with (s:=uf)(e0:=v)...
  destruct H3;subst.
  apply union_set_in_refl...
  destruct H3.
  apply union_set_in with(S1:=S1)(S2:=S2)...
  intro. subst. spec H4 v1. apply H4.
  split... left...
  intro. subst. spec H4 v2. apply H4.
  split... right...
 Qed.
  Lemma union_subset: forall uf v1 v2,
   In uf v1 -> In uf v2 -> 
   subset_t (union uf v1 v2) (union uf v2 v1). 
  Proof with auto. 
   repeat intro.
   apply In_set_in in H.
   apply In_set_in in H0.
   destruct H as [? [? ?]].
   destruct H0 as [? [? ?]].
   rewrite set_in_union_equiv with (S1:=x0)(S2:=x)...
   rewrite set_in_union_equiv with (S1:=x)(S2:=x0) in H1...
   rewrite set_union_comm... 
  Qed.
  Lemma union_comm: forall uf v1 v2,
   In uf v1 -> In uf v2 ->
   equiv_t (union uf v1 v2) (union uf v2 v1).
  Proof with auto.
   intros;split;apply union_subset...
  Qed.
 
  Lemma union_self_equiv: forall uf v,
   In uf v ->
   equiv_t uf (union uf v v).
  Proof with auto.
   intros.
   apply In_set_in in H.
   destruct H as [? [? ?]].
   split;repeat intro.
   destruct (classic (S = x));subst. 
   rewrite<- set_union_refl.
   apply union_set_in_refl...
   apply union_set_in with (S1:=x)(S2:=x)...
   apply set_in_union with (S1:=x) (S2:=x) in H1...
   destruct (classic (S = x));subst...
   destruct H1...
   elimtype False. apply H2. rewrite H1. apply set_union_refl.
  Qed.

  Lemma union_subset_imply: forall uf uf' v1 v2,
   subset_t uf uf' ->
   In uf v1 -> In uf v2 ->
   subset_t (union uf v1 v2) (union uf' v1 v2).
  Proof with auto.
   repeat intro.
   apply In_set_in in H0.
   apply In_set_in in H1.
   destruct H0 as [? [? ?]].
   destruct H1 as [? [? ?]].
   rewrite set_in_union_equiv with (S1:=x)(S2:=x0)...
   rewrite set_in_union_equiv with (S1:=x)(S2:=x0) in H2...
   destruct H2;subst.
   left...
   destruct H2.
   right. split...
  Qed.

  Lemma union_equiv: forall uf uf' v1 v2 ,
   equiv_t uf uf' ->
   In uf v1 -> In uf v2 ->
   equiv_t (union uf v1 v2) (union uf' v1 v2).
  Proof with auto.
   intros.
   assert (In uf' v1). apply In_equiv with (uf:=uf)...
   assert (In uf' v2). apply In_equiv with (uf:=uf)...
   destruct H.
   generalize (union_subset_imply _ _ _ _ H H0 H1);intro.
   generalize (union_subset_imply _ _ _ _ H4 H2 H3);intro.
   split...
  Qed.

  Lemma union_set_of: forall uf e e' e1 e2,
   In uf e1 -> In uf e2 -> 
   In uf e -> set_of uf e e' ->
   In (union uf e1 e2) e /\ set_of (union uf e1 e2) e e'.
  Proof with auto.
   intros.
   apply set_of_In_rewrite in H2...
   destruct H2 as [? [? [? ?]]].
   apply In_set_in in H. destruct H as [? [? ?]].
   apply In_set_in in H0. destruct H0 as [? [? ?]].
   destruct (classic (set_disjoint x (set_union x0 x1))).
   assert (set_in (union uf e1 e2) x).
   rewrite set_in_union_equiv with (S1:=x0)(S2:=x1)...
   rewrite set_of_In_rewrite;
   rewrite In_set_in.
   split;exists x...
   exists x...
   destruct (classic (exists e, x e /\ set_union x0 x1 e)).
   destruct H8 as [? [? ?]].
   destruct H9.
   assert (x = x0). apply set_in_unique with (s:=uf) (e0:=x2)...
   subst.
   rewrite set_of_In_rewrite;
   rewrite In_set_in.
   split;exists (set_union x0 x1).
   split. apply union_set_in_refl...
   left...
   split. apply union_set_in_refl...
   split. left... left...
   exists (set_union x0 x1).
   split. apply union_set_in_refl...
   left...
   assert (x = x1). apply set_in_unique with (s:=uf) (e0:=x2)...
   subst.
   rewrite set_of_In_rewrite;
   rewrite In_set_in.
   split;exists (set_union x0 x1).
   split. apply union_set_in_refl...
   right...
   split. apply union_set_in_refl...
   split. right... right...
   exists (set_union x0 x1).
   split. apply union_set_in_refl...
   right...
   elimtype False.
   apply H7. repeat intro.
   destruct H9.
   apply H8.  exists v. split...
  Qed.  
  (* Ideas for other lemmas? *)
End UnionFind_Lemmas.



 