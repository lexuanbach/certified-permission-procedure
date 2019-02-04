Require Import msl.msl_standard.
Require Import share_dec_base.
Require Import borders.
Require Import bound_map.
Require Import share_dec_interface.
Require Import share_equation_system.

Module Bounder (sv : SV)
               (Import es : EQUATION_SYSTEM sv with Module dom := Share_Domain)
                <: BOUNDER sv es.

  Module sys_features := System_Features sv es.
  Import sys_features.

Open Scope ord.

 Opaque tree_shares.Share.BAF.bot tree_shares.Share.BAF.top
 tree_shares.Share.BAF.glb tree_shares.Share.BAF.lub.

Lemma height_glb : forall (s1 s2 : share) h, 
 (|s1|<h)%nat-> 
 (|s2|<h)%nat -> 
 (|glb s1 s2|<h)%nat.
Proof.
  intros.
  destruct (le_dec (|s1|) (|s2|)).
  generalize (Share.height_glb1 _ _ l);intro.
  unfold glb. compute in *; omega.
  assert ((|s2| <=|s1|)%nat) by omega.
  generalize (Share.height_glb1 _ _ H1);intro.
  rewrite Share.glb_commute in H2.
  unfold glb; compute in *; omega.
Qed.

Lemma height_lub : forall (s1 s2 : share) h, 
 (|s1|<h)%nat-> 
 (|s2|<h)%nat -> 
 (|lub s1 s2|<h)%nat.
Proof.
  intros.
  destruct (le_dec (|s1|) (|s2|)).
  generalize (Share.height_lub1 _ _ l);intro.
  unfold glb. compute in *; omega.
  assert ((|s2| <=|s1|)%nat) by omega.
  generalize (Share.height_lub1 _ _ H1);intro.
  rewrite Share.lub_commute in H2.
  unfold glb; compute in *; omega.
Qed.

Lemma share_metric_ord1 : forall (s1 s2 :share) n, 
 s1 <= s2 -> 
 (0<Share.share_metric n s1)%nat -> 
 (0<Share.share_metric n s2)%nat -> 
 (Share.share_metric n s1 <= Share.share_metric n s2)%nat.
Proof with try tauto.
  intros.
  destruct (eq_dec s1 s2). subst. omega.
  apply ord_spec1 in H. 
  rewrite Share.glb_commute in H.
  rewrite H in *. apply le_lt_or_eq_iff. left.
  apply Share.share_metric_glb...
  intro. rewrite H in H2. apply n0.
  apply Share.ord_antisym...
  apply Share.glb_lower1.
Qed.

Lemma share_metric_ord2 : forall s1 s2 n, 
 s1 < s2 -> 
 (0<Share.share_metric n s1)%nat -> 
 (0<Share.share_metric n s2)%nat -> 
 (Share.share_metric n s1 < Share.share_metric n s2)%nat.
Proof with try tauto.
  intros.
  destruct H.
  apply ord_spec1 in H. 
  rewrite Share.glb_commute in H.
  rewrite H in *. apply Share.share_metric_glb...
  intro. rewrite H in H3. apply H2.
  apply Share.ord_antisym...
  apply Share.glb_lower1.
Qed.

Definition proper_bound_height (h:nat) (a2:share) (a3:share) := (height a2<h)%nat/\(height a3<h)%nat.

Definition dec_bound_prop ol ou nl nu h := 
   ol<=nl /\ nu<=ou /\ proper_bound_height h nl nu.

(* BA facts *)

Lemma join_unfold: forall s1 s2 s3 : share,
  join s1 s2 s3 <->
  glb s1 s2 = bot /\ lub s1 s2 = s3.
Proof. split; auto. Qed.

Lemma lub_gbl_comp1 {A} `{BA A}: forall a b c, 
  a <= lub b c -> glb a (comp b) <= c.
Proof.
  intros.
  transitivity (glb (lub b c) (comp b)).
  apply glb_leq; auto. reflexivity.
  rewrite lub_commute. apply lub_sub.
Qed.

Lemma lub_glb_comp2 {A} `{BA A}: forall a b c, 
  glb a b = bot -> 
  lub a b <= c ->
  a <= glb c (comp b).
Proof.
  intros.
  transitivity (glb (lub a b) (comp b)).
  apply glb_greatest. apply lub_upper1.
  apply leq_comp_join. trivial.
  apply glb_leq; auto. reflexivity.
Qed.

Lemma join_rhs: forall l1 o1 u1 l2 o2 u2 l3 o3 u3 : share,
  l1 <= o1 <= u1 ->
  l2 <= o2 <= u2 ->
  l3 <= o3 <= u3 ->
  join o1 o2 o3 ->
  (lub l3 (lub l1 l2)) <= o3 <= (glb u3 (lub u1 u2)).
Proof with (auto with ord).
  intros ? ? ? ? ? ? ? ? ? [? ?] [? ?] [? ?] ?.
  rewrite join_unfold in H5. destruct H5. subst o3.
  split. apply lub_least... apply lub_leq...
  apply glb_greatest... apply lub_leq...
Qed.

Lemma join_rhs_eq: forall l1 o1 u1 l2 o2 u2 l3 o3 u3 : share,
  l1 <= o1 <= u1 ->
  l2 <= o2 <= u2 ->
  l3 <= o3 <= u3 ->
  join o1 o2 o3 ->
  (lub l3 (lub l1 l2))=(glb u3 (lub u1 u2)) -> o3=(lub l3 (lub l1 l2)).
Proof with (auto with ord).
  intros.  generalize (join_rhs _ _ _ _ _ _ _ _ _ H H0 H1 H2);intro.
  rewrite <-H3 in H4. destruct H4. simpl in *. apply join_sub_antisym';trivial.
Qed.

Lemma join_lhs: forall l1 o1 u1 l2 o2 u2 l3 o3 u3 : share,
  l1 <= o1 <= u1 ->
  l2 <= o2 <= u2 ->
  l3 <= o3 <= u3 ->
  join o1 o2 o3 ->
  lub l1 (glb l3 (comp u2)) <= o1 <= glb u1 (glb u3 (comp l2)).
Proof with (auto with ord).
  intros ? ? ? ? ? ? ? ? ? [? ?] [? ?] [? ?] ?.
  rewrite join_unfold in H5. destruct H5. subst o3.
  split.
  apply lub_least...
  rewrite <- (lub_bot o1).
  rewrite <- (comp2 u2).
  rewrite distrib2.
  apply glb_leq...
  transitivity (lub o1 o2)...
  apply lub_leq...
(* I feel as though the second half of the proof could be simplified... *)
  apply glb_greatest...
  apply glb_greatest.
  transitivity (lub o1 o2)...
  assert (glb o1 l2 <= glb o1 o2) by (apply glb_leq; auto with ord).
  rewrite H5 in H6.
  apply leq_bot in H6.
  assert (lub (glb o1 l2) (comp l2) = comp l2).
    rewrite H6, lub_commute, lub_bot...
  rewrite lub_commute, distrib2 in H7.
  rewrite (lub_commute _ l2), comp1, glb_top in H7.
  rewrite <- H7...
Qed.

Lemma join_lhs_eq: forall l1 o1 u1 l2 o2 u2 l3 o3 u3 : share,
  l1 <= o1 <= u1 ->
  l2 <= o2 <= u2 ->
  l3 <= o3 <= u3 ->
  join o1 o2 o3 ->
  lub l1 (glb l3 (comp u2)) = glb u1 (glb u3 (comp l2)) ->
  o1 = lub l1 (glb l3 (comp u2)).
Proof with (auto with ord).
  intros.  generalize (join_lhs _ _ _ _ _ _ _ _ _ H H0 H1 H2);intro.
  rewrite <-H3 in H4. destruct H4. simpl in *. apply join_sub_antisym';trivial.
Qed.

Definition bnd_sanity {A} `{O: Ord A} `{@BA A O} (l1 u1 l2 u2 l3 u3 : A) : Prop :=
  lub l1 l2 <= u3 /\
  l3 <= lub u1 u2 /\
  glb l1 l2 = bot.

Lemma bnd_sanity_sym {A} `{O: Ord A} `{@BA A O}: forall l1 u1 l2 u2 l3 u3,
  bnd_sanity l1 u1 l2 u2 l3 u3 ->
  bnd_sanity l2 u2 l1 u1 l3 u3.
Proof with auto.
  intros. destruct H0 as [Ha [Hb Hc]]. red.
  rewrite (lub_commute l2), (lub_commute u2), (glb_commute l2).
  tauto.
Qed.

Lemma lhs_bound_pf {A} `{O: Ord A} `{@BA A O}: forall l1 u1 l2 u2 l3 u3,
  l1 <= u1 ->
  l2 <= u2 ->
  l3 <= u3 ->
  bnd_sanity l1 u1 l2 u2 l3 u3 ->
    lub l1 (glb l3 (comp u2)) <= glb u1 (glb u3 (comp l2)).
Proof with (auto with ord).
  intros. destruct H3 as [Ha [Hb Hc]].
  apply lub_least.
  apply glb_greatest...
  apply glb_greatest.
  transitivity (lub l1 l2)...
  apply leq_comp_join...
  apply glb_greatest...
  2: apply glb_leq...
  2: apply comp_leq...
  transitivity (glb (lub u1 u2) (comp u2)).
  apply glb_leq...
  apply lub_sub.
Qed.

Lemma rhs_bound_pf {A} `{O: Ord A} `{@BA A O}: forall l1 u1 l2 u2 l3 u3,
  l1 <= u1 ->
  l2 <= u2 ->
  l3 <= u3 ->
  bnd_sanity l1 u1 l2 u2 l3 u3 ->
    lub l3 (lub l1 l2) <= glb u3 (lub u1 u2).
Proof with (auto with ord).
  intros. destruct H3 as [Ha [Hb Hc]].
  apply lub_least...
  apply glb_greatest...
  apply lub_leq...
Qed.  


Module BM := BoundMap(sv).
Import BM.

(*
Definition bcontext : Type := var -> (share * share)%type.
*)
Definition bcontext : Type := bmap.
Program Definition bound_object (bctx : bcontext) (o : object) : bound :=
  match o with
    | Cobject c => (c,c)
    | Vobject v => lookup bctx v
  end.
Next Obligation.
  red. reflexivity.
Defined.
Instance evalable_bound_object : getable bcontext object bound :=
  Getable bound_object.

Definition update_object (bctx : bcontext) (o : object) (b : bound) : bcontext :=
  match o with
   | Cobject _ => bctx
   | Vobject v => update bctx v b
  end.

Program Definition one_bound_size (n:nat) (l:share) (u:share): nat :=
  Share.share_metric n u - Share.share_metric n l. 

Definition o_bounds_size (n:nat) (bctx : bcontext) (o:object): nat :=
  match o with
   | Cobject _ => 0
   | Vobject v => 
      let (l,_) := (lookup bctx v) in
        one_bound_size n (fst l) (snd l)
  end.

Lemma get_update_neq: forall o b bm o',
  o <> o' ->
  get (update_object bm o b) o' = get bm o'.
Proof.
  intros. icase o. icase o'.
  simpl. apply lookup_update_neq. 
  intro. apply H. rewrite H0; trivial.
  (*simpl.
  apply exist_ext. trivial.*)
Qed.

Lemma get_update_eq: forall o o0 bm, 
  get (update_object bm o (get bm o)) o0 = get bm o0.
Proof.
    intros. 
    destruct o0;simpl;trivial. (*2:apply exist_ext;trivial.*)
    destruct o;simpl;trivial. case (eq_dec v v0);intro.
    subst. apply lookup_update_eq. 
    rewrite lookup_update_neq;trivial. auto.
Qed.

Lemma update_share_metric_strict_dec: forall v bctx s3 s4 s5 s6 h b2 b1 b6, 
 (forall o', get b2 o' = get (update_object bctx (Vobject v)
          (exist (fun b : bound_type => bound_prop b) (s5, s6) b6)) o')->
  proper_bound_height h s3 s4 -> dec_bound_prop s3 s4 s5 s6 h ->
  bound_object bctx (Vobject v) = 
     exist (fun b : bound_type => bound_prop b) (s3, s4) b1 ->
  exist (fun bt : bound_type => bound_prop bt) (s3, s4) b1 <>
    exist (fun b : bound_type => bound_prop b) (s5, s6) b6 ->
  bound_prop (s5, s6) -> 
   o_bounds_size h b2 (Vobject v) < o_bounds_size h bctx (Vobject v).
  Proof.
       intros. spec H (@Vobject var share v). simpl in *. rewrite lookup_update_eq in H.
       rewrite H,H2. simpl. 
       destruct H0. 
       destruct H1 as[? [? ?]]. destruct H7. 
       apply Share.share_metric_nerr in H0.
       apply Share.share_metric_nerr in H5.
       apply Share.share_metric_nerr in H8.
       apply Share.share_metric_nerr in H7.
       case (eq_dec s3 s5);intro.
         subst. case (eq_dec s6 s4);intro.
         subst. contradiction H3. apply exist_ext;trivial.
         assert (s6<s4) by (unfold sord;split;trivial).
         generalize (share_metric_ord2 _ _ _ H9 H8 H5);intro.
         unfold one_bound_size. unfold bound_prop,fst,snd in b6.
         generalize (share_metric_ord1 _ _ _ b6 H7 H8);intro. split.
         unfold ord. simpl.
         unfold sord in H10;simpl in H10.
         omega.
         unfold ord,sord in *;simpl in *.
         omega.
         assert (s3<s5) by (unfold sord;split;trivial).
         generalize (share_metric_ord2 _ _ _ H9 H0 H7);intro.   
         generalize (share_metric_ord1 _ _ _ H6 H8 H5);intro. 
         unfold one_bound_size. unfold bound_prop,fst,snd in b6.
         generalize (share_metric_ord1 _ _ _ b6 H7 H8);intro.
         unfold ord,sord in *;simpl in *.
         split;simpl;omega.
Qed.

Definition bounded_context (ctx : context) (bctx : bcontext) : Prop :=
  forall o : object, 
    match o_bound (get bctx o) with 
      (l,u) => l <= (get ctx o) /\ (get ctx o) <= u 
  end.
Definition initial_bcontext : bcontext := initial_bmap.
Lemma initial_bcontext_bounds_all : forall ctx, bounded_context ctx initial_bcontext.
Proof with (auto with ord).
  intros ? ?. icase o. 2: split... 
  simpl get. simpl bound_object. rewrite lookup_initial_bmap. split...
Qed.

Definition bound_sanity (lhs1 lhs2 rhs : bound) : Prop :=
  match (o_bound lhs1, o_bound lhs2, o_bound rhs) with
    ((l1,u1), (l2,u2), (l3,u3)) => bnd_sanity l1 u1 l2 u2 l3 u3
  end.

Program Definition lhs1_bound (l1 u1 : share) (bpf1 : l1 <= u1) 
                              (l2 u2 : share) (bpf2 : l2 <= u2) 
                              (l3 u3 : share) (bpf3 : l3 <= u3) 
                              (Ha : lub l1 l2 <= u3) 
                              (Hb : l3 <= lub u1 u2) 
                              (Hc : glb l1 l2 = bot) : bound :=
  (lub l1 (glb l3 (comp u2)), glb u1 (glb u3 (comp l2))).
Next Obligation.
Proof with auto.
  intros. 
  apply lhs_bound_pf...
  red. tauto.
Defined.

Program Definition lhs2_bound (l1 u1 : share) (bpf1 : l1 <= u1) 
                              (l2 u2 : share) (bpf2 : l2 <= u2) 
                              (l3 u3 : share) (bpf3 : l3 <= u3) 
                              (Ha : lub l1 l2 <= u3) 
                              (Hb : l3 <= lub u1 u2) 
                              (Hc : glb l1 l2 = bot) : bound :=
  (lub l2 (glb l3 (comp u1)), glb u2 (glb u3 (comp l1))).
Next Obligation.
Proof with auto.
  intros.
  apply lhs_bound_pf...
  apply bnd_sanity_sym...
  red. tauto.
Defined.

Program Definition rhs_bound (l1 u1 : share) (bpf1 : l1 <= u1) 
                              (l2 u2 : share) (bpf2 : l2 <= u2) 
                              (l3 u3 : share) (bpf3 : l3 <= u3) 
                              (Ha : lub l1 l2 <= u3) 
                              (Hb : l3 <= lub u1 u2) 
                              (Hc : glb l1 l2 = bot) : bound :=
    (lub l3 (lub l1 l2), glb u3 (lub u1 u2)).
Next Obligation.
Proof with auto.
  intros.
  apply rhs_bound_pf...
  red. tauto.
Defined.

Lemma lhs1_preserve_height: forall l1 l2 l3 u1 u2 u3 p1 p2 p3 p4 p5 p6 lr ur br h,
  proper_bound_height h l1 u1 ->  proper_bound_height h l2 u2 ->
  proper_bound_height h l3 u3 -> 
  lhs1_bound l1 u1 p1 l2 u2 p2 l3 u3 p3 p4 p5 p6=
    exist (fun b : bound_type => bound_prop b) (lr, ur) br->proper_bound_height h lr ur.
Proof.
 intros. inv H2. destruct H;destruct H0;destruct H1. split;simpl.
  apply height_lub;trivial. apply height_glb;trivial. rewrite Share.height_comp;trivial.
  apply height_glb;trivial. apply height_glb;trivial. rewrite Share.height_comp;trivial.
Qed.

Lemma lhs2_preserve_height: forall l1 l2 l3 u1 u2 u3 p1 p2 p3 p4 p5 p6 lr ur br h,
  proper_bound_height h l1 u1 ->  proper_bound_height h l2 u2 ->
  proper_bound_height h l3 u3 -> 
  lhs2_bound l1 u1 p1 l2 u2 p2 l3 u3 p3 p4 p5 p6=
    exist (fun b : bound_type => bound_prop b) (lr, ur) br ->
  proper_bound_height h lr ur.
Proof.
  intros. inv H2. destruct H;destruct H0;destruct H1. split;simpl.
  apply height_lub;trivial. apply height_glb;trivial. rewrite Share.height_comp;trivial.
  apply height_glb;trivial. apply height_glb;trivial. rewrite Share.height_comp;trivial.
Qed.

Lemma rhs_preserve_height: forall l1 l2 l3 u1 u2 u3 p1 p2 p3 p4 p5 p6 lr ur br h,
  proper_bound_height h l1 u1 ->  proper_bound_height h l2 u2 ->
  proper_bound_height h l3 u3 -> 
  rhs_bound l1 u1 p1 l2 u2 p2 l3 u3 p3 p4 p5 p6=
    exist (fun b : bound_type => bound_prop b) (lr, ur) br ->
  proper_bound_height h lr ur.
Proof.
  intros. inv H2. destruct H;destruct H0;destruct H1. split;simpl.
  apply height_lub;trivial. apply height_lub;trivial.
  apply height_glb;trivial. apply height_lub;trivial.
Qed.

(*Temp here*)
  Definition substitution : Type :=
    {p : (var * object)%type | snd p <> Vobject (fst p)}.
  Definition sbst_var (sbst : substitution) : var := fst (projT1 sbst).
  Definition sbst_object (sbst : substitution) : object := snd (projT1 sbst).
  Program Definition mkCsubstitution (x : var) (sh : share) : substitution :=
    (x, Cobject sh).
  Next Obligation. disc. Defined.
  Program Definition mkVsubstitution (x : var) (y : var) (pf : x <> y) : substitution :=
    (x, Vobject y).
  Next Obligation. unfold fst, snd. intro. apply pf. inv H. trivial. Defined.
  
  Instance dec_eq_substitution : EqDec substitution.
  Proof.
    repeat intro. destruct a. destruct a'.
    destruct x. destruct x0.
    case (eq_dec v v0). case (eq_dec o o0).
    left. subst. apply exist_ext. trivial.
    right. intro. inv H. apply n1. trivial.
    right. intro. inv H. apply n1. trivial.
  Defined.

  Definition eval_substitution (ctx : context) (subst : substitution) : Prop :=
    match subst with exist (x, fp) pf => ctx x = get ctx fp end.
  Instance evalable_substitution : evalable context substitution :=
    Evalable eval_substitution.
  Definition vars_subst (subst : substitution) : list var :=
   (sbst_var subst) :: (vars (sbst_object subst)).
  Instance varsable_subst : varsable substitution var :=
   Varsable vars_subst.

  Record equation_system : Type := Equation_system {
    eqs_nzvars       : list var;
    eqs_substitutions : list substitution;
    eqs_equations     : list equation
  }.
  Definition eval_equation_system (ctx : context) (eqs : equation_system) : Prop :=
    ctx |= (eqs_nzvars eqs) /\ ctx |= (eqs_substitutions eqs) /\ ctx |= (eqs_equations eqs).
  Instance evalable_equation_system : evalable context equation_system :=
    Evalable eval_equation_system.

 
 Program Definition eql2subst (eql : equality) : result substitution unit:=
  match eql with
  |(Vobject v, obj)
  |(obj, Vobject v)=> match eq_dec obj (Vobject v) with
                      |left _ => Simpler tt
                      |right _ => Same (v,obj)
                      end
  |(Cobject c1, Cobject c2) => match eq_dec c1 c2 with
                               |left _ => Simpler tt
                               |right _ => Absurd
                               end
  end.
  Next Obligation. intro. inv H. Defined.
  
 Fixpoint eql2subst_list (l : list equality) : option (list (substitution)) :=
  match l with
  |nil => Some nil
  |eql::l' => match eql2subst eql with
              |Same subst' => match eql2subst_list l' with 
                                    |Some l'' => Some (subst'::l'')
                                    |None => None
                                    end
              |Simpler tt => eql2subst_list l'
              |Absurd => None
              end
  end.

  Lemma eql2subst_Simpler: forall eql,
   eql2subst eql = Simpler tt ->
   forall rho, rho |= eql.
  Proof with try tauto.
   repeat intro.
   destruct eql as [obj1 obj2].
   icase obj1;icase obj2.
   compute in H.
   destruct (sv.t_eq_dec v0 v);subst;simpl...
   inv H. simpl in H.
   destruct (eq_dec s0 s1);subst;simpl;inv H...
  Qed.

  Opaque tree_shares.Share.canonTree_eq_dec.

  Lemma eql2subst_Absurd: forall eql,
   eql2subst eql = Absurd ->
   forall rho, ~rho|=eql.
  Proof with try tauto.
   repeat intro.
   destruct eql as [obj1 obj2].
   icase obj1;icase obj2;compute in H.
   destruct (sv.t_eq_dec v0 v);subst;simpl;inv H...
   destruct (tree_shares.Share.canonTree_eq_dec s0 s1);inv H.
   compute in H0...
  Qed.

  Lemma eql2subst_Same: forall eql subst,
    eql2subst eql = Same subst ->
    forall rho, rho |= eql <-> rho |= subst.
  Proof with try tauto.
   repeat intro.
   destruct eql as [obj1 obj2].
   icase obj1;icase obj2;compute in H;
   try destruct (sv.t_eq_dec v0 v);subst;simpl;inv H...
   compute. split;intros;subst...
   destruct (tree_shares.Share.canonTree_eq_dec s0 s1);inv H1.
  Qed.

  Lemma eql2subst_list_None: forall l,
   eql2subst_list l = None -> forall rho, ~rho |= l.
  Proof with try tauto.
   induction l;repeat intro;inv H.
   destruct H0.
   remember (eql2subst a). symmetry in Heqr.
   destruct r;inv H2.
   apply eql2subst_Absurd with (rho:=rho) in Heqr...
   icase u. spec IHl H3 rho...
   remember (eql2subst_list l).
   symmetry in Heqo. icase o.
   spec IHl... spec IHl rho...
  Qed.

  Lemma eql2subst_list_Some: forall l l',
   eql2subst_list l = Some l' -> 
   forall rho, rho |= l <-> rho |= l'.
  Proof with try tauto.
   induction l;repeat intro;inv H.
   simpl...
   remember (eql2subst a). symmetry in Heqr.
   destruct r;inv H1. icase u.
   apply eql2subst_Simpler with (rho:=rho) in Heqr...
   spec IHl l' H0 rho. simpl in *...
   remember (eql2subst_list l).
   symmetry in Heqo. icase o.
   inv H0. spec IHl l0. spec IHl...
   apply eql2subst_Same with (rho:=rho) in Heqr.
   spec IHl rho. simpl in *...
  Qed.

  Definition subst2eql (subst : substitution) : equality :=
   let (v,obj) := projT1 subst in (Vobject v,obj).
  Definition subst2eql_list := fun l =>
   fold_right (fun sbst l' => (subst2eql sbst)::l') nil l.

  Lemma subst2eql_eval: forall sbst,
   forall rho, rho |= sbst <-> rho|= (subst2eql sbst).
  Proof with try tauto.
   repeat intro.
   destruct sbst as [[? ?] ?].
   icase o;compute...
  Qed.
  Lemma subst2eql_list_eval: forall l,
   forall rho, rho |= l <-> rho |= (subst2eql_list l).
  Proof with try tauto.
   induction l;repeat intro;simpl...
   spec IHl rho.
   generalize (subst2eql_eval a rho);simpl;intro...
  Qed.

  Definition wrapped_ses:= fun (ses : sat_equation_system) =>
   let l1 := sat_nzvars ses in
   let l2 := sat_equalities ses in
   let l3 := sat_equations ses in
    match eql2subst_list l2 with
    |None => None
    |Some l2' => Some (Equation_system l1 l2' l3)
    end.
  Definition unwrapped_ses:= fun ses =>
   let l1 := eqs_nzvars ses in
   let l2 := eqs_substitutions ses in
   let l3 := eqs_equations ses in
    Sat_equation_system l1 (subst2eql_list l2) l3.

  Lemma wrapped_ses_None: forall ses,
   wrapped_ses ses = None -> forall rho, ~rho|=ses.
  Proof with try tauto.
   intros.
   destruct ses as [l1 l2 l3].
   unfold wrapped_ses in H. simpl in H.
   remember (eql2subst_list l2).
   symmetry in Heqo. icase o;inv H.
   apply eql2subst_list_None with (rho:=rho) in Heqo.
   intro;apply Heqo. simpl in *.
   unfold eval_sat_equation_system in *;simpl in *...
  Qed.

  Lemma wrapped_ses_Some: forall ses ses',
   wrapped_ses ses = Some ses' -> 
   forall rho, rho |= ses <-> rho |= ses'.
  Proof with try tauto.
   intros.
   destruct ses as [l1 l2 l3].
   unfold wrapped_ses in H. simpl in H.
   remember (eql2subst_list l2).
   symmetry in Heqo. icase o;inv H.
   apply eql2subst_list_Some with (rho:=rho) in Heqo.
   repeat intro; simpl in *;
   unfold eval_sat_equation_system,eval_equation_system in *;simpl in *...
  Qed.

  Lemma unwrapped_ses_eval: forall ses rho,
  rho |= ses <-> rho |= (unwrapped_ses ses).
  Proof with try tauto.
   repeat intro.
   destruct ses as [l1 l2 l3].
   generalize (subst2eql_list_eval l2 rho);simpl;intro.
   unfold eval_equation_system,eval_sat_equation_system...
  Qed.

Inductive bound_result : Type :=
  | br_narrower : list substitution -> bcontext -> bound_result
  | br_unchanged
  | br_absurd.

Definition bound_constant (b : bound) : Prop :=
  fst (projT1 b) = snd (projT1 b).

Definition bound_constant_dec (b : bound) : {bound_constant b} + {~bound_constant b} :=
  eq_dec (fst (projT1 b)) (snd (projT1 b)).

Definition bound_constant_preserved (b b' : bound) : Prop :=
  bound_constant b -> b = b'.

Lemma bound_constant_preserved_fact: forall b l u b' l' u',
  o_bound b = (l,u) ->
  o_bound b' = (lub l l', glb u u') ->
  bound_constant_preserved b b'.
Proof.
  repeat intro. 
  destruct b as [[l'' u''] ?]. red in H1. simpl in H1.
  destruct b' as [[l''' u'''] ?]. apply exist_ext.
  unfold o_bound in *. simpl in *. inv H. inv H0.
  red in b, b0. unfold fst, snd in b,b0. clear b.
  change Share.lub with (@lub share _ _) in *.
  change Share.glb with (@glb share _ _) in *.
  f_equal; apply ord_antisym; auto with ord.
  etransitivity; eauto with ord.
  eauto with ord.
Qed.

Lemma bound_constant_preserved_lhs1: forall l1 u1 bpf1 l2 u2 bpf2 l3 u3 bpf3 Ha Hb Hc,
  bound_constant_preserved (exist _ (l1, u1) bpf1) 
                           (lhs1_bound l1 u1 bpf1 l2 u2 bpf2 l3 u3 bpf3 Ha Hb Hc).
Proof.
  intros. unfold lhs1_bound. simpl. 
  eapply bound_constant_preserved_fact;
  unfold o_bound; simpl; reflexivity.
Qed.

Lemma bound_constant_preserved_lhs2: forall l1 u1 bpf1 l2 u2 bpf2 l3 u3 bpf3 Ha Hb Hc,
  bound_constant_preserved (exist _ (l2, u2) bpf2) 
                           (lhs2_bound l1 u1 bpf1 l2 u2 bpf2 l3 u3 bpf3 Ha Hb Hc).
Proof.
  intros. unfold lhs2_bound. simpl. 
  eapply bound_constant_preserved_fact;
  unfold o_bound; simpl; reflexivity.
Qed.

Lemma bound_constant_preserved_rhs: forall l1 u1 bpf1 l2 u2 bpf2 l3 u3 bpf3 Ha Hb Hc,
  bound_constant_preserved (exist _ (l3, u3) bpf3) 
                           (rhs_bound l1 u1 bpf1 l2 u2 bpf2 l3 u3 bpf3 Ha Hb Hc).
Proof.
  intros. unfold rhs_bound. simpl. 
  eapply bound_constant_preserved_fact;
  unfold o_bound; simpl; reflexivity.
Qed.

Inductive triple A B C : Type := Triple : A -> B -> C -> triple A B C.
Implicit Arguments Triple [[A] [B] [C]].

Definition process_bound (bctx : bcontext) (oldB newB : bound) (o : object) 
(oldConstL : list (object * bound)) : triple bcontext bool (list (object * bound)) :=
  match eq_dec oldB newB with
   | left _ => Triple bctx false oldConstL
   | _ => Triple (update_object bctx o newB) true 
           (if bound_constant_dec newB then (o,newB)::oldConstL else oldConstL)
  end.

Definition constListOK (bctx : bcontext) (oCL : list (object * bound)) : Prop :=
  forall o b, 
    In (o,b) oCL -> 
    get bctx o = b /\ bound_constant b.

Lemma constListOK_nil : forall bctx, constListOK bctx nil.
Proof. red. intros. inv H. Qed.

Lemma constListOK_decomp: forall o b l bctx,
    constListOK bctx ((o,b)::l) -> 
    constListOK bctx l /\ get bctx o = b /\ bound_constant b.
Proof.
   intros. split.
   unfold constListOK; intros;spec H o0 b0.
   apply H. right;trivial. 
   spec H o b. apply H. left;trivial.
Qed.

Definition tighter (b1:bound) (b2:bound) :=
match b1,b2 with exist (l1,u1) pf1 , exist (l2,u2) pf2 =>
  l1<=l2/\u2<=u1
end.

Lemma join_lhs1_wrap: forall l1 o1 u1 l2 o2 u2 l3 o3 u3 a14 a15 a16 a10 ctx bctx
  b1 b2 b3 a11 a12,
 bound_object bctx o1=exist (fun b:bound_type => bound_prop b)(l1,u1) b1 ->
 bound_object bctx o2=exist (fun b:bound_type => bound_prop b)(l2,u2) b2 ->
 bound_object bctx o3=exist (fun b:bound_type => bound_prop b)(l3,u3) b3 ->
 join (get ctx o1) (get ctx o2) (get ctx o3) ->
 bounded_context ctx bctx ->
 lhs1_bound l1 u1 b1 l2 u2 b2 l3 u3 b3 a10 a11 a12 =
   exist (fun bt : bound_type => bound_prop bt) (a14, a15) a16 -> 
  a14 <= (get ctx o1) <= a15.
Proof.
  intros.
  generalize (H3 o1);intro.
  generalize (H3 o2);intro.
  generalize (H3 o3);intro.
  remember (o_bound (get bctx o1)) as b. 
    unfold o_bound in Heqb;simpl in Heqb;rewrite H in Heqb;destruct b;simpl in Heqb;inv Heqb. 
  remember (o_bound (get bctx o2)) as b. 
    unfold o_bound in Heqb;simpl in Heqb;rewrite H0 in Heqb;destruct b;simpl in Heqb;inv Heqb. 
  remember (o_bound (get bctx o3)) as b. 
    unfold o_bound in Heqb;simpl in Heqb;rewrite H1 in Heqb;destruct b;simpl in Heqb;inv Heqb. 
  clear H H0 H1 H3.
 inv H4.
 apply (join_lhs _ _ _ _ _ _ _ _ _ H5 H6 H7 H2).
Qed.

Lemma join_lhs2_wrap: forall l1 o1 u1 l2 o2 u2 l3 o3 u3 a14 a15 a16 a10 ctx bctx
  b1 b2 b3 a11 a12,
 bound_object bctx o1=exist (fun b:bound_type => bound_prop b)(l1,u1) b1 ->
 bound_object bctx o2=exist (fun b:bound_type => bound_prop b)(l2,u2) b2 ->
 bound_object bctx o3=exist (fun b:bound_type => bound_prop b)(l3,u3) b3 ->
 join (get ctx o1) (get ctx o2) (get ctx o3) ->
 bounded_context ctx bctx ->
 lhs2_bound l1 u1 b1 l2 u2 b2 l3 u3 b3 a10 a11 a12 =
   exist (fun bt : bound_type => bound_prop bt) (a14, a15) a16 -> 
  a14 <= (get ctx o2) <= a15.
Proof.
  intros.
  generalize (H3 o1);intro.
  generalize (H3 o2);intro.
  generalize (H3 o3);intro.
  remember (o_bound (get bctx o1)) as b. 
    unfold o_bound in Heqb;simpl in Heqb;rewrite H in Heqb;destruct b;simpl in Heqb;inv Heqb. 
  remember (o_bound (get bctx o2)) as b. 
    unfold o_bound in Heqb;simpl in Heqb;rewrite H0 in Heqb;destruct b;simpl in Heqb;inv Heqb. 
  remember (o_bound (get bctx o3)) as b. 
    unfold o_bound in Heqb;simpl in Heqb;rewrite H1 in Heqb;destruct b;simpl in Heqb;inv Heqb. 
  clear H H0 H1 H3.
 inv H4.
 apply join_comm in H2.
 apply (join_lhs _ _ _ _ _ _ _ _ _ H6 H5 H7 H2).
Qed.

Lemma join_rhs_wrap: forall l1 o1 u1 l2 o2 u2 l3 o3 u3 a14 a15 a16 a10 ctx bctx
  b1 b2 b3 a11 a12,
 bound_object bctx o1=exist (fun b:bound_type => bound_prop b)(l1,u1) b1 ->
 bound_object bctx o2=exist (fun b:bound_type => bound_prop b)(l2,u2) b2 ->
 bound_object bctx o3=exist (fun b:bound_type => bound_prop b)(l3,u3) b3 ->
 join (get ctx o1) (get ctx o2) (get ctx o3) ->
 bounded_context ctx bctx ->
 rhs_bound l1 u1 b1 l2 u2 b2 l3 u3 b3 a10 a11 a12 =
   exist (fun bt : bound_type => bound_prop bt) (a14, a15) a16 -> 
  a14 <= (get ctx o3) <= a15.
Proof.
  intros.
  generalize (H3 o1);intro.
  generalize (H3 o2);intro.
  generalize (H3 o3);intro.
  remember (o_bound (get bctx o1)) as b. 
    unfold o_bound in Heqb;simpl in Heqb;rewrite H in Heqb;destruct b;simpl in Heqb;inv Heqb. 
  remember (o_bound (get bctx o2)) as b. 
    unfold o_bound in Heqb;simpl in Heqb;rewrite H0 in Heqb;destruct b;simpl in Heqb;inv Heqb. 
  remember (o_bound (get bctx o3)) as b. 
    unfold o_bound in Heqb;simpl in Heqb;rewrite H1 in Heqb;destruct b;simpl in Heqb;inv Heqb. 
  clear H H0 H1 H3.
 inv H4.
 apply (join_rhs _ _ _ _ _ _ _ _ _ H5 H6 H7 H2).
Qed.

Lemma process_bound_spec_ctx: forall bctx oldB newB o oCL bctx' b oCL',
  process_bound bctx oldB newB o oCL = Triple bctx' b oCL' ->  
   (b=true-> forall o', get bctx' o' = get (update_object bctx o newB ) o')/\
   (b=false-> bctx' = bctx).
Proof.
  unfold process_bound. intros ? ? ? ? ? ? ? ?.
  case (eq_dec _ _ ); intros; inv H; split;intros; disc;trivial.
Qed.

Lemma process_bound_spec_ctx_neq: forall bctx oldB newB o oCL bctx' b oCL',
  process_bound bctx oldB newB o oCL = Triple bctx' b oCL' -> (b=true-> oldB<>newB).
Proof.
  unfold process_bound. intros ? ? ? ? ? ? ? ?.
  case (eq_dec _ _ ); intros; inv H;disc;trivial. 
Qed.

Lemma process_bound_spec_const_list: forall oldB' bctx oldB newB o oCL bctx' b oCL',
  bound_constant_preserved oldB newB -> 
  bound_constant_preserved oldB' newB->
  constListOK bctx oCL ->  get bctx o = oldB' -> 
  process_bound bctx oldB newB o oCL = Triple bctx' b oCL' ->  
  constListOK bctx' oCL'/\ (b=false-> oCL=oCL').
Proof.
  unfold process_bound. intros ? ? ? ? ? ? ? ? ? ? ? ? ?.
  case (eq_dec _ _ ); intros; inv H3.
  split; trivial. split;trivial; intros; disc. 
  unfold constListOK; intros.
  destruct o;simpl.
     icase (bound_constant_dec newB).
     destruct H2. inv H2. simpl; rewrite lookup_update_eq;split;trivial.
     spec H1 o0 b H2. destruct H1; split;trivial. simpl in H1.
     rewrite <-H1.
     destruct o0. 
     simpl; case (eq_dec v v0); intro.
     subst;rewrite lookup_update_eq; spec H0 H3;auto.
     rewrite lookup_update_neq;trivial.
     apply exist_ext;trivial.
     spec H1 o0 b H2. destruct H1. split;trivial.
     destruct o0. simpl in *.
     icase (eq_dec v v0). subst.
     rewrite lookup_update_eq; spec H0 H3;auto.
     rewrite lookup_update_neq;trivial.
     rewrite <-H1;simpl; apply exist_ext;trivial.
    icase (bound_constant_dec newB).
    destruct H2.
      inv H2;split;trivial.
      apply H0;unfold bound_constant;auto.
      apply H1; trivial.
Qed.

Lemma process_bound_spec_res_neq : forall bctx' bctx o newB  b,
  (b=true-> forall o', get bctx' o' = get (update_object bctx o newB ) o')->
  (b=false-> bctx' = bctx)->  (forall o0, o<>o0 -> get bctx' o0 = get bctx o0).
Proof.
  intros. icase b. assert (Ht:true=true) by trivial. 
  spec H Ht. 
  spec H o0. trivial. destruct o0. simpl in *.
  destruct o. simpl in H.
  rewrite lookup_update_neq in H. trivial. 
  intro. subst. contradiction H1. trivial.
  simpl in H.  trivial. simpl. apply exist_ext. trivial.
  assert(Hf:false=false)by trivial. spec H0 Hf;subst;trivial.
Qed.

Lemma proc_spec_lhs1_bounded_ctx: forall b2 ctx bctx bctx' lhs1 o b3 s3 s4
   s s0 s1 s2 b b0 o1 o0 b1 o3 o2 e,
   bound_object bctx' o1=exist(fun b:bound_type => bound_prop b)(s,s0)b->
   bound_object bctx' o0=exist(fun b:bound_type => bound_prop b)(s1,s2)b0->
   bound_object bctx' o=exist (fun b:bound_type => bound_prop b)(s3,s4)b1->
   bounded_context ctx bctx' ->   bounded_context ctx bctx ->
   join (get ctx o) (get ctx o0) (get ctx o1)->
   lhs1 = lhs1_bound s3 s4 b1 s1 s2 b0 s s0 b o3 o2 e ->
    (b3=true->forall o' : object, get b2 o' = get (update_object bctx o lhs1) o')->
    (b3 = false -> b2 = bctx)    ->    bounded_context ctx b2.
Proof.
     intros.  unfold bounded_context. intros.
     assert (Ht:true=true) by trivial.
     assert (Hf:false=false)by trivial.
     icase (eq_dec o o4).
      subst o4. 
      icase b3. 
      spec H6 Ht. 
        spec H6 o. destruct lhs1. destruct x. symmetry in H5.
        generalize (join_lhs1_wrap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        H1 H0 H H4 H2 H5). clear -H6.
        destruct o. simpl in *. rewrite lookup_update_eq in H6. rewrite H6.
        simpl. auto.
        simpl in *. intro. split; apply join_sub_refl.
       spec H7 Hf. subst b2. apply H3. 
    generalize (process_bound_spec_res_neq _ _ _ _ _ H6 H7 _ n);intro.
    rewrite H8. apply H3.
Qed.

Lemma proc_spec_lhs2_bounded_ctx: forall b2 ctx bctx bctx' lhs1 o b3 s3 s4
   s s0 s1 s2 b b0 o1 o0 b1 o3 o2 e,
   bound_object bctx' o1=exist(fun b:bound_type => bound_prop b)(s,s0)b->
   bound_object bctx' o0=exist(fun b:bound_type => bound_prop b)(s1,s2)b0->
   bound_object bctx' o=exist (fun b:bound_type => bound_prop b)(s3,s4)b1->
   bounded_context ctx bctx' ->    bounded_context ctx bctx ->
   join (get ctx o) (get ctx o0) (get ctx o1)->
   lhs1 = lhs2_bound s3 s4 b1 s1 s2 b0 s s0 b o3 o2 e ->
   (b3=true->forall o' : object, get b2 o' = get (update_object bctx o0 lhs1) o')->
   (b3 = false -> b2 = bctx) -> bounded_context ctx b2.
Proof.
     intros.  unfold bounded_context. intros.
     assert (Ht:true=true) by trivial.
     assert (Hf:false=false)by trivial.
     icase (eq_dec o0 o4).
      subst o4. 
      icase b3. 
      spec H6 Ht. 
        spec H6 o0. destruct lhs1. destruct x. symmetry in H5.
        generalize (join_lhs2_wrap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        H1 H0 H H4 H2 H5). clear -H6.
        destruct o0. simpl in *. rewrite lookup_update_eq in H6. rewrite H6.
        simpl. auto.
        simpl in *. intro. split; apply join_sub_refl.
       spec H7 Hf. subst b2. apply H3.
    generalize (process_bound_spec_res_neq _ _ _ _ _ H6 H7 _ n);intro.
    rewrite H8. apply H3.
Qed.

Lemma proc_spec_rhs_bounded_ctx: forall b2 ctx bctx bctx' lhs1 o b3 s3 s4
   s s0 s1 s2 b b0 o1 o0 b1 o3 o2 e,
   bound_object bctx' o1=exist(fun b:bound_type => bound_prop b)(s,s0)b->
   bound_object bctx' o0=exist(fun b:bound_type => bound_prop b)(s1,s2)b0->
   bound_object bctx' o=exist (fun b:bound_type => bound_prop b)(s3,s4)b1->
   bounded_context ctx bctx' -> bounded_context ctx bctx ->
   join (get ctx o) (get ctx o0) (get ctx o1)->
   lhs1 = rhs_bound s3 s4 b1 s1 s2 b0 s s0 b o3 o2 e ->
   (b3=true->forall o' : object, get b2 o' = get (update_object bctx o1 lhs1) o')->
   (b3 = false -> b2 = bctx) -> bounded_context ctx b2.
Proof.
     intros.  unfold bounded_context. intros.
     assert (Ht:true=true) by trivial.
     assert (Hf:false=false)by trivial.
     icase (eq_dec o1 o4).
      subst o4. 
      icase b3. 
      spec H6 Ht. 
        spec H6 o1. destruct lhs1. destruct x. symmetry in H5.
        generalize (join_rhs_wrap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        H1 H0 H H4 H2 H5). clear -H6.
        destruct o1. simpl in *. rewrite lookup_update_eq in H6. rewrite H6.
        simpl. auto.
        simpl in *. intro. split; apply join_sub_refl.
       spec H7 Hf. subst b2. apply H3.
    generalize (process_bound_spec_res_neq _ _ _ _ _ H6 H7 _ n);intro.
    rewrite H8. apply H3.
Qed.

Fixpoint objBound2subst (obL : list (object * bound)) : list substitution :=
  match obL with
   | nil => nil
   | (o,b) :: obL' => let sL' := objBound2subst obL' in
     match o with
      | Cobject _ => sL'
      | Vobject x => mkCsubstitution x (fst (projT1 b)) :: sL'
     end
  end.

Lemma share_leq_dec: forall (x y : share),
 {x <= y} + {~x <= y}.
Proof with try tauto.
 intros. destruct (Share.leq_dec x y).
 left. apply leq_join_sub in o...
 right. intro. apply n. apply leq_join_sub...
Defined.

Definition bound_equation (bctx : bcontext) (eqn : equation) : bound_result :=
 match eqn with (o1, o2, o3) =>  match (get bctx o1, get bctx o2, get bctx o3) with 
   (* (o_bound (@eval _ _ _ evalable_bound_object bctx o1), o_bound (@eval _ _ _ evalable_bound_object bctx o2), o_bound (@eval _ _ _ evalable_bound_object bctx o3)) with *)
  (exist (l1, u1) bpf1 as lhs1, exist (l2,u2) bpf2 as lhs2, exist (l3, u3) bpf3 as rhs) =>
    (* sanity check 1 *)
    match share_leq_dec (lub l1 l2) u3 with
     | right _ => br_absurd (* fails *)
     | left Ha =>
    (* sanity check 2 *)
    match share_leq_dec l3 (lub u1 u2) with
     | right _ => br_absurd
     | left Hb =>
    (* sanity check 3 *)
    match eq_dec (glb l1 l2) bot with
     | right _ => br_absurd
     | left Hc =>
      (* sanity checks passed; calculate new bounds *)
      let lhs1' := lhs1_bound l1 u1 bpf1 l2 u2 bpf2 l3 u3 bpf3 Ha Hb Hc in
      let lhs2' := lhs2_bound l1 u1 bpf1 l2 u2 bpf2 l3 u3 bpf3 Ha Hb Hc in
      let rhs'  := rhs_bound  l1 u1 bpf1 l2 u2 bpf2 l3 u3 bpf3 Ha Hb Hc in
      (* only update the bound table when a bound has actually changed *)
      let (bctx1, c1, cL1) := process_bound bctx  lhs1 lhs1' o1 nil in
      let (bctx2, c2, cL2) := process_bound bctx1 lhs2 lhs2' o2 cL1 in
      let (bctx3, c3, cL3) := process_bound bctx2 rhs  rhs'  o3 cL2 in
      (* Return narrower if we have moved a bound; otherwise return unchanged *)
      if orb c1 (orb c2 c3) then 
        br_narrower (objBound2subst cL3) bctx3 
      else 
        br_unchanged
    end
    end
    end
  end end.

Definition bound_absurd {A} `{H : evalable context A} 
                        (bctx : bcontext) (a : A) : Prop :=
  forall ctx : context, bounded_context ctx bctx -> eval ctx a -> False.

Definition bounded {A} `{H : evalable context A} 
     (atcn : bcontext) (a : A) (SL : list substitution) (csqn : bcontext) : Prop :=
  forall ctx : context, bounded_context ctx atcn -> eval ctx a ->
        eval ctx SL /\ bounded_context ctx csqn.

Lemma bound_equation_absurd: forall bctx eqn,
  bound_equation bctx eqn = br_absurd ->  bound_absurd bctx eqn.
Proof.
  intros. destruct eqn as [[? ?] ?]. red. intros. revert H.
  simpl.
  case_eq (bound_object bctx o).
  case_eq (bound_object bctx o0).
  case_eq (bound_object bctx o1).
  intros [? ?] ? ? [? ?] ? ? [? ?] ? ?.
  generalize (H0 o);
  generalize (H0 o0);
  generalize (H0 o1).
  simpl get in *.
  rewrite H, H2, H3. simpl.
  intros [? ?] [? ?] [? ?].
  destruct H1.
  change join_sub with (@ord share _) in *.
  change Share.lub with (@lub share _ _) in *.
  change Share.glb with (@glb share _ _) in *.
  change Share.bot with (@bot share _ _) in *.
  simpl get in *.
  (* break apart cases *)
 (*
  case (share_leq_dec (lub s3 s1) s0).
  case (share_leq_dec s (lub s4 s2)).
  *)
  case (share_leq_dec (lub s4 s2) s1).
  case (share_leq_dec s0 (lub s5 s3)).
  case (eq_dec _ _ ). 
  intros ? ? ?.
  case (process_bound bctx _ _ _ _). intros ? ? ?.
  case (process_bound b2 _ _ _ _). intros ? ? ?.
  case (process_bound b4 _ _ _ _). intros ? ? ?.
  icase b3; icase b5; icase b7.
  (* absurd 1 *)
  intros.
  apply n.
  apply ord_antisym; auto with ord.
  transitivity (glb (get_obj_val ctx o) (get_obj_val ctx o0)).
  2: unfold s,dom.e in *;rewrite H1;reflexivity.
  apply glb_leq; tauto. 
  (* absurd 2 *)
  intros.
  apply n.
  rewrite <- H10 in H4.
  transitivity (lub (get_obj_val ctx o) (get_obj_val ctx o0)); auto.
  apply lub_leq; auto.
  (* absurd 3 *)
  intros.
  apply n.
  rewrite <- H10 in H5.
  transitivity (lub (get_obj_val ctx o) (get_obj_val ctx o0)); auto.
  apply lub_leq; auto.
Qed.

Lemma lhs2_tighter:
 forall a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16,
  lhs2_bound a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 =
   exist (fun bt : bound_type => bound_prop bt) (a14, a15) a16 -> 
     a5<=a14/\ a15<=a6.
Proof.
  intros; inv H; split. 
  simpl;rewrite<-leq_join_sub;apply Share.lub_upper1.
  simpl;rewrite<-leq_join_sub;apply Share.glb_lower1.
Qed.

Lemma lhs1_tighter:
 forall a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16,
  lhs1_bound a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 =
   exist (fun bt : bound_type => bound_prop bt) (a14, a15) a16 -> 
     a2<=a14/\ a15<=a3.
Proof.
  intros; inv H; split. 
  simpl;rewrite<-leq_join_sub;apply Share.lub_upper1.
  simpl;rewrite<-leq_join_sub;apply Share.glb_lower1.
Qed.

Lemma rhs_tighter:
 forall a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16,
  rhs_bound a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 =
   exist (fun bt : bound_type => bound_prop bt) (a14, a15) a16 -> 
     a8<=a14/\ a15<=a9.
Proof.
  intros; inv H; split. 
  simpl;rewrite<-leq_join_sub;apply Share.lub_upper1.
  simpl;rewrite<-leq_join_sub;apply Share.glb_lower1.
Qed.

Lemma lhs2_tighter_metric:
 forall h a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16,
  lhs2_bound a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 =
   exist (fun bt : bound_type => bound_prop bt) (a14, a15) a16 ->
  proper_bound_height h a2 a3->
   proper_bound_height h a5 a6 -> proper_bound_height h a8 a9 
     -> dec_bound_prop a5 a6 a14 a15 h.
Proof.
  intros. 
  inv H. split. simpl;rewrite<-leq_join_sub;apply Share.lub_upper1.
  split. simpl;rewrite<-leq_join_sub;apply Share.glb_lower1.
  destruct H0;destruct H1;destruct H2.
  split. apply height_lub;trivial. apply height_glb;trivial. rewrite Share.height_comp;trivial.
  apply height_glb;trivial. apply height_glb;trivial. rewrite Share.height_comp;trivial.
Qed.
  
Lemma lhs1_tighter_metric: forall h a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16,
  lhs1_bound a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 =
   exist (fun bt : bound_type => bound_prop bt) (a14, a15) a16 -> proper_bound_height h a2 a3->
   proper_bound_height h a5 a6 -> proper_bound_height h a8 a9 
     ->  dec_bound_prop a2 a3 a14 a15 h.
Proof.
  intros. 
  inv H. split. simpl;rewrite<-leq_join_sub;apply Share.lub_upper1.
  split. simpl;rewrite<-leq_join_sub;apply Share.glb_lower1.
  destruct H0;destruct H1;destruct H2.
  split. apply height_lub;trivial. apply height_glb;trivial. rewrite Share.height_comp;trivial.
  apply height_glb;trivial. apply height_glb;trivial. rewrite Share.height_comp;trivial.
Qed.

Lemma rhs_tighter_metric: forall h a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16,
  rhs_bound a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 =
   exist (fun bt : bound_type => bound_prop bt) (a14, a15) a16 -> 
   proper_bound_height h a2 a3 ->
   proper_bound_height h a5 a6 -> proper_bound_height h a8 a9 
     ->  dec_bound_prop a8 a9 a14 a15 h.
Proof.
  intros. unfold dec_bound_prop. 
  inv H. split. simpl;rewrite<-leq_join_sub;apply Share.lub_upper1.
  split. simpl;rewrite<-leq_join_sub;apply Share.glb_lower1.
  destruct H0;destruct H1;destruct H2.
  split. apply height_lub;trivial. apply height_lub;trivial. 
  apply height_glb;trivial. apply height_lub;trivial.
Qed.

Lemma bound_equation_narrower: forall bctx eqn SL bctx',
  bound_equation bctx eqn = br_narrower SL bctx'->
  bounded bctx eqn SL bctx'.
Proof. 
  intros. destruct eqn as [[? ?] ?]. red. intros. revert H.
  simpl.
  case_eq (bound_object bctx o).
  case_eq (bound_object bctx o0).
  case_eq (bound_object bctx o1).
  intros [? ?] ? ? [? ?] ? ? [? ?] ? ?.
  generalize (H0 o);
  generalize (H0 o0);
  generalize (H0 o1).
  simpl get in *.
  rewrite H, H2, H3. simpl.
  intros [? ?] [? ?] [? ?].
  simpl in H1. 
  assert(Hj:join (get_obj_val ctx o) (get_obj_val ctx o0) (get_obj_val ctx o1)) by trivial.
  destruct H1.
  change join_sub with (@ord share _) in *.
  change Share.lub with (@lub share _ _) in *.
  change Share.glb with (@glb share _ _) in *.
  change Share.bot with (@bot share _ _) in *.
  simpl get in *.
  (* break apart cases *)
  case (share_leq_dec (lub s4 s2) s1); disc.
  case (share_leq_dec s0 (lub s5 s3)); disc.
  case (eq_dec _ _ ); disc.
  intros ? ? ?.
  case_eq (process_bound bctx (@exist (share*share)%type (fun bt : (share*share)%type => bound_prop bt) (s4,s5) b1) (lhs1_bound s4 s5 b1 s2 s3 b0 s0 s1 b o3 o2 e) o nil).
  intros ? ? ? ?. 
  case_eq (process_bound b2 (@exist (share*share)%type (fun bt : (share*share)%type => bound_prop bt) (s2,s3) b0) (lhs2_bound s4 s5 b1 s2 s3 b0 s0 s1 b o3 o2 e) o0 l).
  intros ? ? ? ?.
  case_eq (process_bound b4 (@exist (share*share)%type (fun bt : (share*share)%type => bound_prop bt) (s0,s1) b) (rhs_bound s4 s5 b1 s2 s3 b0 s0 s1 b o3 o2 e) o1 l0).
  intros ? ? ? ?.
  remember (b3 || (b5 || b7)). icase b8. intro. inv H14.
  remember (lhs1_bound s4 s5 b1 s2 s3 b0 s0 s1 b o3 o2 e) as lhs1.
  remember (lhs2_bound s4 s5 b1 s2 s3 b0 s0 s1 b o3 o2 e) as lhs2.
  remember (rhs_bound s4 s5 b1 s2 s3 b0 s0 s1 b o3 o2 e) as rhs.
   generalize (process_bound_spec_ctx   _ _ _ _ _ _ _ _  H11); intro;destruct H14.
   generalize (process_bound_spec_ctx _ _ _ _ _ _ _ _ H12); intro; destruct H16.
   generalize (process_bound_spec_ctx _ _ _ _ _ _ _ _ H13); intro. destruct H18.
  assert (bounded_context ctx bctx').
   generalize (proc_spec_lhs1_bounded_ctx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 
     _ _ _ _ H H2 H3 H0 H0 Hj Heqlhs1 H14 H15). intro.
   generalize (proc_spec_lhs2_bounded_ctx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 
     _ _ _ _ H H2 H3 H0 H20 Hj Heqlhs2 H16 H17);intro.
   apply (proc_spec_rhs_bounded_ctx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 
     _ _ _ _ H H2 H3 H0 H21 Hj Heqrhs H18 H19).
  rename H4 into Hlb1. rename H6 into Hlb0. rename H8 into Hlb.
  clear -H H2 H3 Heqlhs1 Heqlhs2 Heqrhs H14 H15 H16 H17 H20 H11 H12 H13
    e o2 o3 Hj Hlb1 Hlb0 Hlb.
  assert (constListOK bctx' l1).
  Focus 2.
   split; trivial.
   clear -H20 H0.
   revert H0. induction l1.
    simpl. trivial.
    intro.
    simpl. destruct a. destruct o. 
    2:apply IHl1;apply (constListOK_decomp _ _ _ _ H0).
    apply constListOK_decomp in H0. destruct H0. 
    split.
    apply IHl1;trivial.
    spec H20 (@Vobject var share v). destruct H0;unfold s,dom.e in *;rewrite H0 in H20.
    destruct b. destruct x. unfold bound_constant in H1; simpl in H1.
    subst s0. simpl in H20. simpl. destruct H20; apply join_sub_antisym;trivial.
  clear H20.
  apply (process_bound_spec_const_list (get bctx o)) in H11;auto.
  2: subst lhs1;apply bound_constant_preserved_lhs1. 
  2: subst lhs1;simpl;rewrite H3; apply bound_constant_preserved_lhs1.
  2: apply constListOK_nil.
  destruct H11.
  assert(Hf:false=false)by trivial.
  assert (Ht:true=true)by trivial. 

  assert (constListOK b4 l0 /\ (b5 = false -> l = l0)).
    apply (process_bound_spec_const_list (get b2 o0)) in H12;auto.
    subst lhs2; apply bound_constant_preserved_lhs2.
    icase b3. 
      2:spec H15 Hf;subst b2 lhs2;simpl;rewrite H2;apply bound_constant_preserved_lhs2.
      spec H14 Ht o0. 
      case(eq_dec o o0);intro.
        subst o0.
        destruct o. 
         rewrite H14. simpl. rewrite lookup_update_eq.
         rewrite H2 in H3. inv H3.
         unfold bound_constant_preserved. intro. apply exist_ext. trivial.
         remember (get b2 (Cobject s5)) as b3; destruct b3. destruct x. subst lhs2. 
         inv Heqb3; inv H2.
         unfold lhs2_bound; simpl. 
         eapply bound_constant_preserved_fact;unfold o_bound; simpl; reflexivity.
        rewrite get_update_neq in H14;auto. 
        rewrite H14;subst lhs2;simpl;
         rewrite H2;apply bound_constant_preserved_lhs2;auto.

   destruct H4. clear H5 H1.
    unfold constListOK .
    apply (process_bound_spec_const_list (get b4 o1)) in H13;auto.
    destruct H13;trivial.
    subst rhs; apply bound_constant_preserved_rhs.
    destruct o1.
    Focus 2.
       unfold bound_constant_preserved;intros;subst rhs; simpl;apply exist_ext. 
       inv H;rewrite lub_commute. clear -e o2 o3.
       rewrite ord_spec2 in o3;rewrite o3.
       rewrite ord_spec1 in o2; rewrite <-o2; trivial.
    assert (Hbcp2:bound_constant_preserved (get b2 (Vobject v)) rhs).
      icase b3.
        spec H14 Ht (@Vobject var share v).
        case (eq_dec o (Vobject v));intro.
        subst o. simpl in H14. simpl. rewrite H14,lookup_update_eq.
        assert (bound_constant_preserved lhs1 rhs).
         assert(s2=bot).
           assert (@get_obj_val var share ctx o0 = bot).
             clear - Hj. apply join_comm in Hj.
             eapply join_canc. apply Hj.
             apply join_comm. split.
             apply Share.glb_bot. apply Share.lub_bot.
           unfold s,dom.e in *; rewrite H1 in *. apply join_sub_antisym. trivial. apply bot_correct'.
           subst s2.
         unfold bound_constant_preserved. intros; subst lhs1 rhs. 
         apply exist_ext. rewrite H in H3. inv H3.
         clear -H1 e o2 o3. inv H1.
         rewrite lub_bot,comp_bot,glb_top,lub_idem,glb_idem,lub_absorb,glb_absorb.
         rewrite Share.lub_absorb, Share.glb_commute in H0.
         rewrite (Share.glb_commute s5 (Share.comp Share.bot)) in H0.
         rewrite Share.glb_assoc, Share.glb_idem in H0.
         rewrite <-(Share.comp_inv s5),<-Share.demorgan1 in H0.
         rewrite Share.lub_commute,Share.lub_bot,Share.comp_inv in H0.
         subst;trivial.
       trivial.
       destruct o. simpl in H14. rewrite lookup_update_neq in H14. 
       simpl. rewrite H14. subst rhs. simpl in H. rewrite H.
       apply bound_constant_preserved_rhs.
       intro;subst v;contradiction n;trivial.
       simpl in H14. simpl. rewrite H14. simpl in H;rewrite H.
       subst rhs; apply bound_constant_preserved_rhs.
       spec H15 Hf;subst b2 rhs;simpl in *;rewrite H;apply bound_constant_preserved_rhs.

    icase b5.
     spec H16 Ht (@Vobject var share v).
     case(eq_dec o0 (Vobject v));intro.
       subst o0. simpl in H16. simpl. rewrite H16,lookup_update_eq.
       assert (bound_constant_preserved lhs2 rhs).
         assert(s4=bot).
           assert (@get_obj_val var share ctx o = bot).
            clear - Hj.
             eapply join_canc. apply Hj.
             apply join_comm. split.
             apply Share.glb_bot. apply Share.lub_bot.
           unfold s,dom.e in *;rewrite H1 in *.
           apply join_sub_antisym. trivial. apply bot_correct'.
           subst s4.
         unfold bound_constant_preserved. intros; subst lhs2 rhs. 
         apply exist_ext. rewrite H in H2. inv H2.
         clear -H1 e o2 o3. inv H1.
         rewrite (lub_commute bot s2),lub_bot,comp_bot,glb_top,lub_idem.
         rewrite lub_absorb,glb_idem,(lub_commute s5 s3),glb_absorb. 
         rewrite Share.lub_absorb, Share.glb_commute in H0.
         rewrite (Share.glb_commute s3 (Share.comp Share.bot)) in H0.
         rewrite Share.glb_assoc, Share.glb_idem in H0.
         rewrite <-(Share.comp_inv s3),<-Share.demorgan1 in H0.
         rewrite Share.lub_commute,Share.lub_bot,Share.comp_inv in H0.
         subst;trivial.
       trivial.
       destruct o0;simpl in *. rewrite H16, lookup_update_neq; trivial.
       intro;subst v; contradiction n;trivial.
       rewrite H16;trivial.
       spec H17 Hf;subst b4;trivial. 
Qed.

Definition eq_bound_height (h:nat) (bctx : bcontext) (c:equation) : Prop := 
 match c with (o1, o2, o3) =>     
  match (get bctx o1, get bctx o2, get bctx o3) with 
       (exist (l1, u1) _, 
        exist (l2,u2) _, 
        exist (l3, u3) _) =>   
          proper_bound_height h l1 u1 /\ 
          proper_bound_height h l2 u2 /\
          proper_bound_height h l3 u3
    end
 end.

Definition list_eq_bound_height (h:nat) (bctx : bcontext) (eql:list equation) : Prop := 
 forall eq, In eq eql -> eq_bound_height h bctx eq.

Lemma proc_bound_const_false_contr: forall h s1 s7 s8 , 
   dec_bound_prop s1 s1 s7 s8 h -> bound_prop (s7, s8) -> (s1, s1) = (s7, s8).
  Proof.
     intros. destruct H as [? [? ?]].
     unfold bound_prop,fst,snd in H0. 
     generalize (join_sub_trans H H0);intro.
     generalize (join_sub_antisym H3 H1);intro.
     generalize (join_sub_trans H0 H1);intro.
     generalize (join_sub_antisym H H5);intro.
     subst s7 s8;trivial.
  Qed.

Lemma true_guard_var: forall b3 o s3 s4 bctx bctx1 s5 s6 b6 h l b1 b2 l2,
   bound_object bctx1 o=exist (fun b : bound_type => bound_prop b) (s3, s4) b1
    -> process_bound bctx
       (exist (fun bt : bound_type => bound_prop bt) (s3, s4) b1)
       (exist (fun b : bound_type => bound_prop b) (s5, s6) b6) o l2 =
     Triple b2 b3 l -> dec_bound_prop s3 s4 s5 s6 h 
    -> (b3=true-> exists v, o=Vobject v).
   Proof.
    intros. destruct o. exists v;trivial.
    unfold process_bound in H0.  revert H0.
    case(eq_dec _ _ ); intros; inv H0;disc.
    contradiction n. apply exist_ext. inv H.
    apply (proc_bound_const_false_contr h);trivial.
   Qed.

Lemma dec_one_bound_size: forall h s3 s4 s5 s6,
      proper_bound_height h s3 s4->dec_bound_prop s3 s4 s5 s6 h-> 
      ((one_bound_size h s5 s6 <=one_bound_size h s3 s4)%nat).
 Proof.
      intros. destruct H. destruct H0 as [? [? [? ?]]]. 
      apply Share.share_metric_nerr in H.
      apply Share.share_metric_nerr in H1.
      apply Share.share_metric_nerr in H3.
      apply Share.share_metric_nerr in H4.
      generalize (share_metric_ord1 _ _ _ H0 H H3);intro.
      generalize (share_metric_ord1 _ _ _ H2 H4 H1);intro.
      unfold one_bound_size. 
      unfold ord,sord in *;simpl in *;omega.  
 Qed.

Lemma dec_bound_prop_dec_size: forall s3 s4 s5 s6 h,
         bound_prop (s3, s4)-> bound_prop (s5, s6)->
         dec_bound_prop s3 s4 s5 s6 h -> proper_bound_height h s3 s4 ->
         (s3,s4)<>(s5,s6)->
         (one_bound_size h s5 s6 < one_bound_size h s3 s4)%nat.
      Proof.
        intros. unfold bound_prop,fst,snd in *.
        generalize (dec_one_bound_size _ _ _ _ _ H2 H1);intro.
        unfold one_bound_size in *. rename H4 into Hleq.
        destruct H1 as [? [? [? ?]]]. destruct H2.
        apply Share.share_metric_nerr in H5.
        apply Share.share_metric_nerr in H6.
        apply Share.share_metric_nerr in H2.
        apply Share.share_metric_nerr in H7.
        generalize (share_metric_ord1 _ _ _ H0 H5 H6);intro.
        icase (eq_dec s3 s5);icase (eq_dec s6 s4);subst.
         contradiction H3;trivial.
         assert (s6<s4)by (unfold sord;split;trivial).
         generalize (share_metric_ord2 _ _ _ H9 H6 H7);intro;unfold ord,sord in *;simpl in *;omega.
         assert (s3<s5)by (unfold sord;split;trivial).
         generalize (share_metric_ord2 _ _ _ H9 H2 H5);intro;unfold ord,sord in *;simpl in *;omega.
         assert (s3<s5)by (unfold sord;split;trivial).
         generalize (share_metric_ord2 _ _ _ H9 H2 H5);intro.
         generalize (share_metric_ord1 _ _ _ H H2 H7);intro.
         generalize (share_metric_ord1 _ _ _ H4 H6 H7);intro.
         unfold ord,sord in *;simpl in *;omega.
     Qed.

Definition var_bound_size n bctx v := 
  let (l,_) := lookup bctx v in one_bound_size n (fst l) (snd l).

Definition var_in_object (x :var) (o : object) := match o with 
        | Cobject _ => False
        | Vobject v => (x=v) 
   end.

Definition in_eq_vars x c := 
   match c with (o1,o2,o3) => (var_in_object x o1) \/ (var_in_object x o2)
     \/ (var_in_object x o3) end.

Definition height_preserved h bctx' bctx v :=
   let (b,_) := lookup bctx v in  
   let (b',_) := lookup bctx' v in  
   proper_bound_height h (fst b) (snd b)-> proper_bound_height h (fst b') (snd b').

Definition height_preserved2 h bctx' bctx v :=
   let (b,_) := lookup bctx v in  
   let (b',_) := lookup bctx' v in  
   (((height (fst b)<h) -> height (fst b')<h)/\
   (height (snd b)<h -> height (snd b')<h))%nat.


Lemma height_bound_preserved2: forall bctx bctx' c ls h v,
  bound_equation bctx c = br_narrower ls bctx' -> eq_bound_height h bctx c ->
  height_preserved2 h bctx' bctx v.
Proof.
  intros. destruct c as [[? ?] ?]. intros. simpl in H. revert H.
  case_eq (bound_object bctx o).
  case_eq (bound_object bctx o0).
  case_eq (bound_object bctx o1).
  intros [? ?] ? ? [? ?] ? ? [? ?] ? ?.
  change join_sub with (@ord share _) in *.
  change Share.lub with (@lub share _ _) in *.
  change Share.glb with (@glb share _ _) in *.
  change Share.bot with (@bot share _ _) in *.
  (* break apart cases *)
  case (share_leq_dec (lub s4 s2) s1); disc.
  case (share_leq_dec s0 (lub s5 s3)); disc.
  case (eq_dec _ _ ); disc.
  intros ? ? ?.
  case_eq (process_bound bctx (@exist (share*share)%type (fun bt : (share*share)%type => bound_prop bt) 
  (s4,s5) b1) (lhs1_bound s4 s5 b1 s2 s3 b0 s0 s1 b o3 o2 e) o nil).
  intros ? ? ? ?.
  case_eq (process_bound b2 (@exist (share*share)%type (fun bt : (share*share)%type => bound_prop bt) 
  (s2,s3) b0) (lhs2_bound s4 s5 b1 s2 s3 b0 s0 s1 b o3 o2 e) o0 l).
  intros ? ? ? ?.
  case_eq (process_bound b4 (@exist (share*share)%type (fun bt : (share*share)%type => bound_prop bt) 
  (s0,s1) b) (rhs_bound s4 s5 b1 s2 s3 b0 s0 s1 b o3 o2 e) o1 l0).
  intros ? ? ? ?.
  remember (b3 || (b5 || b7)). icase b8. intro. inv H6.
  unfold eq_bound_height in H0; simpl in H0; rewrite H,H1,H2 in H0.
   generalize (process_bound_spec_ctx   _ _ _ _ _ _ _ _  H3); intro;destruct H6.
   generalize (process_bound_spec_ctx _ _ _ _ _ _ _ _ H4); intro. destruct H8.
   generalize (process_bound_spec_ctx _ _ _ _ _ _ _ _ H5); intro; destruct H10.
   
   clear -H0 H6 H7 H8 H9 H10 H11 H H1 H2 H3 H4 H5 Heqb8.
    remember (lhs1_bound s4 s5 b1 s2 s3 b0 s0 s1 b o3 o2 e) as lb1.
    remember (lhs2_bound s4 s5 b1 s2 s3 b0 s0 s1 b o3 o2 e) as lb2.
    remember (rhs_bound s4 s5 b1 s2 s3 b0 s0 s1 b o3 o2 e) as r.
    destruct lb1. destruct x. destruct lb2. destruct x. destruct r. destruct x.
    destruct H0 as [? [? ?]]. symmetry in Heqlb1. symmetry in Heqlb2. symmetry in Heqr.
    generalize (lhs1_tighter_metric _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Heqlb1 H0 H12 H13);intro.
    generalize (lhs2_tighter_metric _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Heqlb2 H0 H12 H13);intro.
    generalize (rhs_tighter_metric _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Heqr H0 H12 H13);intro.
    generalize (lhs1_preserve_height _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H0 H12 H13 Heqlb1);intro Hh1.
    generalize (lhs2_preserve_height _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H0 H12 H13 Heqlb2);intro Hh2.
    generalize (rhs_preserve_height _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H0 H12 H13 Heqr);intro Hhr.
    destruct Hhr as [Hhr1 Hhr2].    destruct Hh1 as [Hh11 Hh12].     destruct Hh2 as [Hh21 Hh22].
    apply (dec_one_bound_size _ _ _ _ _ H0) in H14.
    apply (dec_one_bound_size _ _ _ _ _ H12) in H15.
    apply (dec_one_bound_size _ _ _ _ _ H13) in H16.
     assert (Ht:true=true)by trivial.
     assert (Hf:false=false)by trivial.
(*from level to level the eq metric might not always decrease, lvl 1 dec, 
   lvl 2 increases lvl 1 but still smaller that original... so no dec on levels*)
(*it is not the case that the metric always decreases on each var, so no
   dec on vars*)
(*no choice but to case on whole equation...*)
  generalize (process_bound_spec_res_neq _ _ _ _ _ H10 H11);intro Hneq1.
  generalize (process_bound_spec_res_neq _ _ _ _ _ H8 H9);intro Hneq2.
  generalize (process_bound_spec_res_neq _ _ _ _ _ H6 H7);intro Hneq3.
  clear H5 Heqr H4 Heqlb2 H3 Heqlb1. unfold height_preserved2.
  destruct H0 as [Hp1 Hp2].  destruct H12 as [Hp3 Hp4].  destruct H13 as [Hp5 Hp6].
  case_eq(lookup bctx v). case_eq (lookup bctx' v). intros. 
  destruct x,x0;simpl.
  icase (eq_dec o (Vobject v));icase (eq_dec o1 (Vobject v));
  icase (eq_dec o0 (Vobject v)). 
  (*1/8*)
     Focus 1. subst. simpl in *. icase b7.
       spec H10 Ht (@Vobject var share v). 
       simpl in H10. rewrite lookup_update_eq in H10. 
       rewrite H10 in H0;inv H0;auto.
       icase b5. spec H8 Ht (@Vobject var share v). spec H11 Hf;subst b4. simpl in H8.
       rewrite lookup_update_eq in H8. rewrite H8 in H0;inv H0;simpl;auto.
       icase b3. spec H11 Hf. spec H9 Hf;subst b2 b4. spec H6 Ht (@Vobject var share v).
       simpl in H6. rewrite lookup_update_eq in H6. rewrite H6 in H0;inv H0. auto.
  (*2/8*) Focus 1. subst. simpl in *. 
     icase b7.      
       spec H10 Ht (@Vobject var share v). simpl in H10; rewrite H10,lookup_update_eq in H0;inv H0;auto.
       spec H11 Hf;subst b4.
       spec Hneq2 (@Vobject var share v) n;simpl in Hneq2.
       icase b3.
         spec H6 Ht (@Vobject var share v);simpl in H6;rewrite Hneq2,H6,lookup_update_eq in H0. inv H0;auto.
         spec H7 Hf;subst b2. rewrite Hneq2,H3 in H0. inv H0;auto.
  (*3/8*) Focus 1. subst. simpl in *. 
     spec Hneq1 (@Vobject var share v) n;simpl in Hneq1.
     icase b5.      
       spec H8 Ht (@Vobject var share v). simpl in H8; rewrite Hneq1,H8,lookup_update_eq in H0;inv H0;auto.
       spec H9 Hf;subst b4.
       icase b3.
         spec H6 Ht (@Vobject var share v);simpl in H6;rewrite Hneq1,H6,lookup_update_eq in H0;inv H0;auto.
         spec H7 Hf;subst b2;rewrite Hneq1,H2 in H0. inv H0;auto.
  (*4/8*) Focus 2. subst. simpl in *. 
     icase b7.      
       spec H10 Ht (@Vobject var share v). simpl in H10. rewrite H10,lookup_update_eq in H0;inv H0;auto.
       spec H11 Hf;subst b4.
       icase b5.
         spec H8 Ht (@Vobject var share v);simpl in H8;rewrite H8,lookup_update_eq in H0;inv H0;auto.
         spec H9 Hf;subst b2. 
         spec Hneq3 (@Vobject var share v) n;simpl in Hneq3;rewrite Hneq3,H1 in H0;inv H0;auto.  
  (*5/8*) Focus 1. subst. simpl in *. 
     spec Hneq1 (@Vobject var share v) n;simpl in Hneq1.
     spec Hneq2 (@Vobject var share v) n0;simpl in Hneq2. 
     icase b3.
       spec H6 Ht (@Vobject var share v);simpl in H6;rewrite Hneq1,Hneq2,H6,lookup_update_eq in H0; inv H0; auto.
       spec H7 Hf; subst b2; rewrite Hneq1,Hneq2,H2 in H0;inv H0;auto.
  (*6/8*) Focus 1. subst. simpl in *. 
     spec Hneq3 (@Vobject var share v) n;simpl in Hneq3.
     spec Hneq2 (@Vobject var share v) n0;simpl in Hneq2. 
     icase b7.
       spec H10 Ht (@Vobject var share v);simpl in H10;rewrite H10,lookup_update_eq in H0;inv H0;auto.
       spec H11 Hf; subst b4; rewrite Hneq2,Hneq3,H in H0; inv H0; auto.
  (*7/8*) Focus 1. subst. simpl in *. 
     spec Hneq1 (@Vobject var share v) n0;simpl in Hneq1.
     spec Hneq3 (@Vobject var share v) n;simpl in Hneq3. 
     icase b5.
       spec H8 Ht (@Vobject var share v);simpl in H8;rewrite Hneq1,H8,lookup_update_eq in H0;inv H0; auto.
       spec H9 Hf; subst b4. rewrite Hneq1,Hneq3,H1 in H0;inv H0;auto.
   (*8/8*)
     spec Hneq1 (@Vobject var share v) n0;simpl in Hneq1.
     spec Hneq3 (@Vobject var share v) n;simpl in Hneq3. 
     spec Hneq2 (@Vobject var share v) n1;simpl in Hneq2. 
     rewrite Hneq1,Hneq2,Hneq3,H3 in H0. inv H0. auto.
Qed.  

Lemma height_preserved2_to: forall h bctx' bctx,
(forall v, height_preserved2 h bctx' bctx v)->(forall v, height_preserved h bctx' bctx v).
Proof.
  intros. spec H v. 
  unfold height_preserved2,height_preserved,proper_bound_height in *.
  revert H. case_eq(lookup bctx v);case_eq(lookup bctx' v);intros.
  destruct x,x0,H1,H2. 
  auto.
Qed.

Lemma height_bound_preserved: forall bctx bctx' c ls h v,
  bound_equation bctx c = br_narrower ls bctx' -> eq_bound_height h bctx c ->
  height_preserved h bctx' bctx v.
Proof.
  intros.
  apply height_preserved2_to. intro.
  apply (height_bound_preserved2 _ _ _ _ _ v0 H H0).
Qed.

Lemma bound_decreases: forall bctx bctx' c ls h v,
  bound_equation bctx c = br_narrower ls bctx' -> eq_bound_height h bctx c ->
  (var_bound_size h bctx' v<=var_bound_size h bctx v)%nat.
Proof.
  intros. destruct c as [[? ?] ?]. intros. simpl in H. revert H.
  case_eq (bound_object bctx o).
  case_eq (bound_object bctx o0).
  case_eq (bound_object bctx o1).
  intros [? ?] ? ? [? ?] ? ? [? ?] ? ?.
  change join_sub with (@ord share _) in *.
  change Share.lub with (@lub share _ _) in *.
  change Share.glb with (@glb share _ _) in *.
  change Share.bot with (@bot share _ _) in *.
  (* break apart cases *)
  case (share_leq_dec (lub s4 s2) s1); disc.
  case (share_leq_dec s0 (lub s5 s3)); disc.
  case (eq_dec _ _ ); disc.
  intros ? ? ?.
  case_eq (process_bound bctx (@exist (share*share)%type (fun bt : (share*share)%type => bound_prop bt) 
  (s4,s5) b1) (lhs1_bound s4 s5 b1 s2 s3 b0 s0 s1 b o3 o2 e) o nil).
  intros ? ? ? ?.
  case_eq (process_bound b2 (@exist (share*share)%type (fun bt : (share*share)%type => bound_prop bt) 
  (s2,s3) b0) (lhs2_bound s4 s5 b1 s2 s3 b0 s0 s1 b o3 o2 e) o0 l).
  intros ? ? ? ?.
  case_eq (process_bound b4 (@exist (share*share)%type (fun bt : (share*share)%type => bound_prop bt) 
  (s0,s1) b) (rhs_bound s4 s5 b1 s2 s3 b0 s0 s1 b o3 o2 e) o1 l0).
  intros ? ? ? ?.
  remember (b3 || (b5 || b7)). icase b8. intro. inv H6.
  unfold eq_bound_height in H0; simpl in H0; rewrite H,H1,H2 in H0.
   generalize (process_bound_spec_ctx   _ _ _ _ _ _ _ _  H3); intro;destruct H6.
   generalize (process_bound_spec_ctx _ _ _ _ _ _ _ _ H4); intro. destruct H8.
   generalize (process_bound_spec_ctx _ _ _ _ _ _ _ _ H5); intro; destruct H10.
   
   clear -H0 H6 H7 H8 H9 H10 H11 H H1 H2 H3 H4 H5 Heqb8.
    remember (lhs1_bound s4 s5 b1 s2 s3 b0 s0 s1 b o3 o2 e) as lb1.
    remember (lhs2_bound s4 s5 b1 s2 s3 b0 s0 s1 b o3 o2 e) as lb2.
    remember (rhs_bound s4 s5 b1 s2 s3 b0 s0 s1 b o3 o2 e) as r.
    destruct lb1. destruct x. destruct lb2. destruct x. destruct r. destruct x.
    destruct H0 as [? [? ?]]. symmetry in Heqlb1. symmetry in Heqlb2. symmetry in Heqr.
    generalize (lhs1_tighter_metric _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Heqlb1 H0 H12 H13);intro.
    generalize (lhs2_tighter_metric _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Heqlb2 H0 H12 H13);intro.
    generalize (rhs_tighter_metric _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Heqr H0 H12 H13);intro.
    apply (dec_one_bound_size _ _ _ _ _ H0) in H14.
    apply (dec_one_bound_size _ _ _ _ _ H12) in H15.
    apply (dec_one_bound_size _ _ _ _ _ H13) in H16.
     assert (Ht:true=true)by trivial.
     assert (Hf:false=false)by trivial.
(*from level to level the eq metric might not always decrease, lvl 1 dec, 
   lvl 2 increases lvl 1 but still smaller that original... so no dec on levels*)
(*it is not the case that the metric always decreases on each var, so no
   dec on vars*)
(*no choice but to case on whole equation...*)
  generalize (process_bound_spec_res_neq _ _ _ _ _ H10 H11);intro Hneq1.
  generalize (process_bound_spec_res_neq _ _ _ _ _ H8 H9);intro Hneq2.
  generalize (process_bound_spec_res_neq _ _ _ _ _ H6 H7);intro Hneq3.
  clear H5 Heqr H4 Heqlb2 H3 Heqlb1 H0 H12 H13. unfold var_bound_size.
  icase (eq_dec o (Vobject v));icase (eq_dec o1 (Vobject v));
  icase (eq_dec o0 (Vobject v)). 
  (*1/8*)
     Focus 1. subst. simpl in *. icase b7.
       spec H10 Ht (@Vobject var share v). 
       simpl in H10. rewrite lookup_update_eq in H10. rewrite H10,H. simpl;auto.
       icase b5. spec H8 Ht (@Vobject var share v). spec H11 Hf;subst b4. simpl in H8.
       rewrite lookup_update_eq in H8. rewrite H8,H1;simpl;auto.
       icase b3. spec H11 Hf. spec H9 Hf;subst b2 b4. spec H6 Ht (@Vobject var share v).
       simpl in H6. rewrite lookup_update_eq in H6. rewrite H6,H2. simpl;auto.
  (*2/8*) Focus 1. subst. simpl in *. 
     icase b7.      
       spec H10 Ht (@Vobject var share v). simpl in H10; rewrite H10,H,lookup_update_eq;auto.
       spec H11 Hf;subst b4.
       spec Hneq2 (@Vobject var share v) n;simpl in Hneq2.
       icase b3.
         spec H6 Ht (@Vobject var share v);simpl in H6;rewrite Hneq2,H6,H2,lookup_update_eq;auto.
         spec H7 Hf;subst b2;rewrite Hneq2;auto.
  (*3/8*) Focus 1. subst. simpl in *. 
     spec Hneq1 (@Vobject var share v) n;simpl in Hneq1.
     icase b5.      
       spec H8 Ht (@Vobject var share v). simpl in H8; rewrite Hneq1,H8,H1,lookup_update_eq;trivial.
       spec H9 Hf;subst b4.
       icase b3.
         spec H6 Ht (@Vobject var share v);simpl in H6;rewrite Hneq1,H6,H2,lookup_update_eq;trivial.
         spec H7 Hf;subst b2;rewrite Hneq1;trivial.
  (*4/8*) Focus 2. subst. simpl in *. 
     icase b7.      
       spec H10 Ht (@Vobject var share v). simpl in H10; rewrite H10,H,lookup_update_eq;trivial.
       spec H11 Hf;subst b4.
       icase b5.
         spec H8 Ht (@Vobject var share v);simpl in H8;rewrite H8,H1,lookup_update_eq;trivial.
         spec H9 Hf;subst b2. 
         spec Hneq3 (@Vobject var share v) n;simpl in Hneq3;rewrite Hneq3;trivial.  
  (*5/8*) Focus 1. subst. simpl in *. 
     spec Hneq1 (@Vobject var share v) n;simpl in Hneq1.
     spec Hneq2 (@Vobject var share v) n0;simpl in Hneq2. 
     icase b3.
       spec H6 Ht (@Vobject var share v);simpl in H6;rewrite Hneq1,Hneq2,H6,H2,lookup_update_eq;trivial.
       spec H7 Hf; subst b2; rewrite Hneq1,Hneq2;trivial.
  (*6/8*) Focus 1. subst. simpl in *. 
     spec Hneq3 (@Vobject var share v) n;simpl in Hneq3.
     spec Hneq2 (@Vobject var share v) n0;simpl in Hneq2. 
     icase b7.
       spec H10 Ht (@Vobject var share v);simpl in H10;rewrite H10,H,lookup_update_eq;trivial.
       spec H11 Hf; subst b4; rewrite Hneq2,Hneq3;trivial.
  (*7/8*) Focus 1. subst. simpl in *. 
     spec Hneq1 (@Vobject var share v) n0;simpl in Hneq1.
     spec Hneq3 (@Vobject var share v) n;simpl in Hneq3. 
     icase b5.
       spec H8 Ht (@Vobject var share v);simpl in H8;rewrite Hneq1,H8,H1,lookup_update_eq;trivial.
       spec H9 Hf; subst b4. rewrite Hneq1,Hneq3;trivial.
   (*8/8*)
     spec Hneq1 (@Vobject var share v) n0;simpl in Hneq1.
     spec Hneq3 (@Vobject var share v) n;simpl in Hneq3. 
     spec Hneq2 (@Vobject var share v) n1;simpl in Hneq2. 
     rewrite Hneq1,Hneq2,Hneq3.
     remember (lookup bctx v). destruct b10 as [[? ?] ?]. simpl. clear -b10.
     unfold bound_prop,fst,snd in b10.
     assert ((height s12 <h \/ h<=height s12)%nat) by omega.
     assert ((height s13 <h \/ h<=height s13)%nat) by omega.
     destruct H,H0. 
     apply Share.share_metric_nerr in H.
     apply Share.share_metric_nerr in H0.
     generalize (share_metric_ord1 _ _ _ b10 H H0);intro. trivial.
     apply Share.share_metric_err in H0. trivial.
     apply Share.share_metric_nerr in H0. trivial.
     apply Share.share_metric_err in H. trivial.
Qed.     


Lemma bound_decreases_strict: forall bctx bctx' c ls h,
  bound_equation bctx c = br_narrower ls bctx' -> eq_bound_height h bctx c ->
  (exists v, in_eq_vars v c/\(var_bound_size h bctx' v<var_bound_size h bctx v)%nat).
Proof.
  intros. destruct c as [[? ?] ?]. intros. simpl in H. revert H.
  case_eq (bound_object bctx o).
  case_eq (bound_object bctx o0).
  case_eq (bound_object bctx o1).
  intros [? ?] ? ? [? ?] ? ? [? ?] ? ?.
  change join_sub with (@ord share _) in *.
  change Share.lub with (@lub share _ _) in *.
  change Share.glb with (@glb share _ _) in *.
  change Share.bot with (@bot share _ _) in *.
  (* break apart cases *)
  case (share_leq_dec (lub s4 s2) s1); disc.
  case (share_leq_dec s0 (lub s5 s3)); disc.
  case (eq_dec _ _ ); disc.
  intros ? ? ?.
  case_eq (process_bound bctx (@exist (share*share)%type (fun bt : (share*share)%type => bound_prop bt) 
  (s4,s5) b1) (lhs1_bound s4 s5 b1 s2 s3 b0 s0 s1 b o3 o2 e) o nil).
  intros ? ? ? ?.
  case_eq (process_bound b2 (@exist (share*share)%type (fun bt : (share*share)%type => bound_prop bt) 
  (s2,s3) b0) (lhs2_bound s4 s5 b1 s2 s3 b0 s0 s1 b o3 o2 e) o0 l).
  intros ? ? ? ?.
  case_eq (process_bound b4 (@exist (share*share)%type (fun bt : (share*share)%type => bound_prop bt) 
  (s0,s1) b) (rhs_bound s4 s5 b1 s2 s3 b0 s0 s1 b o3 o2 e) o1 l0).
  intros ? ? ? ?.
  remember (b3 || (b5 || b7)). icase b8. intro. inv H6.
  unfold eq_bound_height in H0; simpl in H0; rewrite H,H1,H2 in H0.
   generalize (process_bound_spec_ctx   _ _ _ _ _ _ _ _  H3); intro;destruct H6.
   generalize (process_bound_spec_ctx _ _ _ _ _ _ _ _ H4); intro. destruct H8.
   generalize (process_bound_spec_ctx _ _ _ _ _ _ _ _ H5); intro; destruct H10.
   remember (lhs1_bound s4 s5 b1 s2 s3 b0 s0 s1 b o3 o2 e) as lb1.
   remember (lhs2_bound s4 s5 b1 s2 s3 b0 s0 s1 b o3 o2 e) as lb2.
   remember (rhs_bound s4 s5 b1 s2 s3 b0 s0 s1 b o3 o2 e) as r.
   destruct lb1. destruct x. destruct lb2. destruct x. destruct r. destruct x.
   destruct H0 as [? [? ?]]. symmetry in Heqlb1. symmetry in Heqlb2. symmetry in Heqr.
   generalize (lhs1_tighter_metric _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Heqlb1 H0 H12 H13);intro.
   generalize (lhs2_tighter_metric _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Heqlb2 H0 H12 H13);intro.
   generalize (rhs_tighter_metric _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Heqr H0 H12 H13);intro.
   generalize (true_guard_var _ _ _ _ _ _ _ _ _ _ _ _ _ _ H2 H3 H14);intro.
   generalize (true_guard_var _ _ _ _ _ _ _ _ _ _ _ _ _ _ H1 H4 H15);intro.
   generalize (true_guard_var _ _ _ _ _ _ _ _ _ _ _ _ _ _ H H5 H16);intro.
     assert (Ht:true=true)by trivial.
     assert (Hf:false=false)by trivial.
   assert (b3=true->(one_bound_size h s6 s7 < one_bound_size h s4 s5)%nat).
     intro. subst b3. 
     generalize (process_bound_spec_ctx_neq _ _ _ _ _ _ _ _  H3 Ht); intro.
     assert ((s4,s5)<>(s6,s7)) by (intro;contradiction H20;apply exist_ext;trivial).
     apply (dec_bound_prop_dec_size _ _ _ _ h) in H21; trivial.
   assert (b5=true->(one_bound_size h s8 s9 < one_bound_size h s2 s3)%nat).
     intro. subst b5. 
     generalize (process_bound_spec_ctx_neq _ _ _ _ _ _ _ _  H4 Ht); intro.
     assert ((s2,s3)<>(s8,s9)) by (intro;contradiction H21;apply exist_ext;trivial).
     apply (dec_bound_prop_dec_size _ _ _ _ h) in H22; trivial.
   assert (b7=true->(one_bound_size h s10 s11 < one_bound_size h s0 s1)%nat).
     intro. subst b7. 
     generalize (process_bound_spec_ctx_neq _ _ _ _ _ _ _ _  H5 Ht); intro.
     assert ((s0,s1)<>(s10,s11)) by (intro;contradiction H22;apply exist_ext;auto).
     apply (dec_bound_prop_dec_size _ _ _ _ h) in H23; trivial.
(*from level to level the eq metric might not always decrease, lvl 1 dec, 
   lvl 2 increases lvl 1 but still smaller that original... so no dec on levels*)
(*it is not the case that the metric always decreases on each var, so no
   dec on vars*)
(*no choice but to case on whole equation...*)
  clear -H22 H21 H20 Ht Hf H19 H18 H17 H11 H10 H9 H8 H7 H6 Heqb8 H H1 H2.
  unfold var_bound_size.
  icase b7.
   spec H10 Ht o1. spec H19 Ht. destruct H19;subst o1. exists x.
    simpl. split. auto. simpl in *. rewrite H10,lookup_update_eq,H. 
    simpl. apply (H22 Ht).
  spec H11 Hf; subst b4.
   icase b5.
     spec H8 Ht o0. spec H18 Ht. destruct H18;subst o0. exists x.
     simpl. split. auto. simpl in *. rewrite H8,lookup_update_eq,H1.
     simpl. apply (H21 Ht).
     spec H9 Hf; subst b2.
     icase b3. 
       spec H6 Ht o. spec H17 Ht. destruct H17;subst o. exists x.
       simpl. split. auto. simpl in *. rewrite H6,lookup_update_eq,H2.
       simpl. apply (H20 Ht).
Qed.

Definition bound_once_equation_list (bctx : bcontext) (eqs: list equation) : bound_result :=
 fold_right (fun c a=> 
  match a with
   | br_absurd => a
   | br_unchanged => bound_equation bctx c
   | br_narrower ls bctx => 
     match (bound_equation bctx c) with
       | br_absurd => br_absurd
       | br_unchanged => a
       | br_narrower ls2 bctx => br_narrower (ls2++ls) bctx
     end 
  end) br_unchanged eqs.


Lemma bound_once_equation_list_narrower: forall bctx eql SL bctx',
  bound_once_equation_list bctx eql = br_narrower SL bctx'->
    bounded bctx eql SL bctx'.
Proof. 
  intros.
  revert eql bctx SL bctx' H.
  induction eql;intros. inv H.
  simpl in H. revert H.
  case_eq (bound_once_equation_list bctx eql);intros. 3:inv H0.
  2:unfold bounded;intros;destruct H2;apply (bound_equation_narrower _ _ _ _ H0);trivial.
  revert H0;case_eq (bound_equation b a);intros;inv H1.
  2:unfold bounded;intros;destruct H2;apply (IHeql bctx SL bctx' H);trivial.
  spec IHeql bctx l b H. unfold bounded in *;intros. destruct H2.
  spec IHeql ctx H1 H2. destruct IHeql.
  apply bound_equation_narrower in H0. spec H0 ctx H5 H3. destruct H0.
  split;trivial. clear -H4 H0.
  simpl in *. revert l0 l ctx H4 H0. induction l0;intros. auto.
  inv H0. split;trivial. apply IHl0;auto. 
Qed.

Lemma bound_once_equation_list_absurd: forall bctx eql,
  bound_once_equation_list bctx eql = br_absurd -> 
  bound_absurd bctx eql.
Proof.
  intros. revert eql bctx H. 
  induction eql;intros. inv H.
  unfold bound_absurd. intros.
  inv H. revert H3. simpl in H1;destruct H1.
  case_eq (bound_once_equation_list bctx eql); intros.
  revert H3; case_eq (bound_equation b a);intros;inv H4.
  apply bound_once_equation_list_narrower in H2. spec H2 ctx H0 H;destruct H2.
  apply (bound_equation_absurd b _ H3 ctx);trivial.
  apply (bound_equation_absurd bctx _ H3 ctx);trivial.
  apply (IHeql bctx H2 ctx);trivial.  
Qed.

Lemma eq_bound_height_preserved: forall h bctx' bctx eq,
 (forall v, height_preserved h bctx' bctx v) -> eq_bound_height h bctx eq->
   eq_bound_height h bctx' eq.
Proof.
   intros. rename H into H1.
  destruct eq as [[? ?] ?]. revert H0.  unfold eq_bound_height. simpl.
  case_eq(bound_object bctx o);case_eq(bound_object bctx o0); case_eq(bound_object bctx o1).
  destruct x1,x0,x.
  case_eq(bound_object bctx' o);case_eq(bound_object bctx' o0); case_eq(bound_object bctx' o1).
  destruct x1,x0,x. intros. destruct H6 as [? [? ?]].
  unfold height_preserved in H1.
  split.
    destruct o. 
       simpl in *;spec H1 v. rewrite H4,H5 in H1;apply H1;auto.
       inv H4;inv H5;trivial. 
  split.
    destruct o0.
       simpl in *;spec H1 v;rewrite H3,H0 in H1;apply H1;auto.
       inv H3;inv H0;trivial. 
  destruct o1.
    simpl in *;spec H1 v;rewrite H2,H in H1. apply H1;auto.
    inv H2;inv H;trivial.
Qed.

Lemma var_height_bound_list_preserved2: forall bctx bctx' eql ls h ,
  bound_once_equation_list bctx eql = br_narrower ls bctx' -> 
  list_eq_bound_height h bctx eql -> forall v, height_preserved2 h bctx' bctx v.
Proof.
 intros. revert eql bctx bctx' ls h H H0 v.
 induction eql;intros. inv H.
 case_eq(lookup bctx v). case_eq (lookup bctx' v). intros.
 destruct x. destruct x0. simpl in *.
 assert (list_eq_bound_height h bctx eql).
    unfold list_eq_bound_height;intros;apply H0;right;trivial.
  assert (In a (a::eql)) by (simpl;auto). spec H0 a H4. clear H4. 
 revert H. case_eq(bound_once_equation_list bctx eql);intros.
 3:inv H4. 2:apply (height_bound_preserved2 _ _ _ _ _ _ H4 H0).
 spec IHeql bctx b1 l h H H3. generalize (height_preserved2_to _ _ _ IHeql);intro Hp2.
 generalize (eq_bound_height_preserved _ _ _ _ Hp2 H0);intro.
 revert H4; case_eq(bound_equation b1 a);intros;inv H6. 2: apply IHeql.
 generalize (height_bound_preserved2 _ _ _ _ _ v H4 H5);intro.
 spec IHeql v. 
 case_eq(bound_object b1 (Vobject v)). intros.
 unfold height_preserved2 in *. rewrite H1,H2. simpl in H7.
 rewrite H2,H7 in IHeql. rewrite H1,H7 in H6. destruct H6,IHeql. auto.
Qed.

Lemma var_height_bound_list_preserved: forall bctx bctx' eql ls h ,
  bound_once_equation_list bctx eql = br_narrower ls bctx' -> 
  list_eq_bound_height h bctx eql -> forall v, height_preserved h bctx' bctx v.
Proof.
  intros.
  generalize (var_height_bound_list_preserved2  _ _ _ _ _ H H0);intro.
  apply (height_preserved2_to _ _ _ H1).
Qed.
  
Lemma height_bound_list_preserved: forall bctx bctx' eql ls h,
  bound_once_equation_list bctx eql = br_narrower ls bctx' -> 
  list_eq_bound_height h bctx eql -> list_eq_bound_height h bctx' eql.
Proof.
  intros.
  generalize (var_height_bound_list_preserved _ _ _ _ _ H H0);intro.
  clear -H1 H0.
  revert eql H0. 
  induction eql;intros. unfold list_eq_bound_height in *. intros.
  inv H.
  intro. intro.
  assert (list_eq_bound_height h bctx eql).
    unfold list_eq_bound_height;intros;apply H0;right;trivial.
  spec IHeql H2.
  destruct H. 2:auto.
  subst a.
  assert (In eq (eq::eql)) by (simpl;auto). spec H0 eq H. clear H. 
  apply (eq_bound_height_preserved _ _ _ _ H1 H0).
Qed.

Lemma bound_equation_list_decreases: forall bctx bctx' eql ls h v,
  bound_once_equation_list bctx eql = br_narrower ls bctx' -> 
   list_eq_bound_height h bctx eql ->
    var_bound_size h bctx' v<=var_bound_size h bctx v.
Proof.
  intros.
  revert eql bctx bctx' ls h H H0 v.
  induction eql;intros;inv H.
  revert H2. case_eq(bound_once_equation_list bctx eql);intros.
  3:inv H2. 2:apply (bound_decreases _ _ _ _ _ _ H2); apply H0;left;trivial.
  assert (list_eq_bound_height h bctx eql).
    unfold list_eq_bound_height;intros;apply H0;right;trivial.
  assert (In a (a::eql)) by (simpl;auto).
  spec H0 a H3.
  spec IHeql bctx b l h H H1.
  revert H2;case_eq(bound_equation b a);intros; inv H4. 2:apply IHeql.
  generalize (var_height_bound_list_preserved _ _ _ _ _ H H1);intro.
  apply (eq_bound_height_preserved _ _ _ _ H4) in H0.
  spec IHeql v.
  transitivity (var_bound_size h b v);trivial.
  apply (bound_decreases _ _ _ _ _ _ H2 H0).
Qed.
    
Lemma bound_equation_list_decreases_strict: forall bctx bctx' eql ls h,
  bound_once_equation_list bctx eql = br_narrower ls bctx' -> 
   list_eq_bound_height h bctx eql ->
   (exists eq, In eq eql /\ (exists v, in_eq_vars v eq/\
      (var_bound_size h bctx' v<var_bound_size h bctx v)%nat)).
Proof.
  intros. revert eql bctx bctx' h ls H H0.
  induction eql;intros; inv H.
  assert (In a (a::eql)) by (simpl;auto). generalize (H0 a H);clear H;intro.
  assert (list_eq_bound_height h bctx eql).
      unfold list_eq_bound_height;intros;apply H0;right;trivial.
  revert H2. case_eq(bound_once_equation_list bctx eql); intros. 3:inv H3.
  Focus 2. 
    exists a. split. left;trivial.
    apply (bound_decreases_strict _ _ _ ls);trivial.
  revert H3. case_eq (bound_equation b a);intros;inv H4.
  Focus 2. 
     spec IHeql bctx bctx' h ls H2 H1. 
     destruct IHeql. destruct H4. exists x. split;trivial. right;trivial.
  exists a. split. left;trivial.
  generalize (var_height_bound_list_preserved _ _ _ _ _ H2 H1);intro.
  apply (eq_bound_height_preserved _ _ _ _ H4) in H.
  apply(bound_decreases_strict b bctx' a l0 h H3) in H. destruct H as [? [? ?]].
  exists x. split;trivial.
  apply (bound_equation_list_decreases _ _ _ _ _ x H2) in H1.
  destruct H1; omega.
Qed.

Definition eq_bounds_size (n:nat) (bctx : bcontext) (eq : equation) : nat := 
   match eq with (o1,o2,o3) =>  
     (o_bounds_size n bctx o1)+(o_bounds_size n bctx o2)+(o_bounds_size n bctx o3)
   end.


Definition eq_bound_height_max (bctx : bcontext) (eq:equation) :nat :=
    match eq with (o1,o2,o3) => 
     match (get bctx o1, get bctx o2, get bctx o3) with 
       (exist (l1, u1) _, exist (l2,u2) _, exist (l3, u3) _) => 
       let m1:= max (height l1+1) (height u1+1) in
       let m2:= max (height l2+1) (height u2+1) in
       let m3:= max (height l3+1) (height u3+1) in
       max (max m1 m2) m3 
     end
   end.

Definition eq_bound_height_eql bctx eql :=
 fold_right (fun c a=> max a (eq_bound_height_max bctx c)) 0 eql.

Lemma list_eq_bound_height_replace:forall h bctx eql,
 list_eq_bound_height h bctx eql -> 
   (forall h1, (h<=h1)%nat->list_eq_bound_height h1 bctx eql).
Proof.
  intros. intro. intros. spec H eq H1. clear -H H0. destruct eq as [[? ?] ?].
  unfold eq_bound_height,proper_bound_height in *. simpl in *.
  revert H. 
  case_eq (bound_object bctx o);case_eq (bound_object bctx o1);case_eq (bound_object bctx o0).
  intros. destruct x,x0,x1. omega.
Qed.

Lemma height_max_sufficient: forall h eql bctx,
 h=eq_bound_height_eql bctx eql -> list_eq_bound_height h bctx eql.
Proof.
  intros. intro. intro. apply in_split in H0. destruct H0 as [? [? ?]].
  assert (h= max (eq_bound_height_eql bctx x)
             (max (eq_bound_height_eql bctx x0)
                  (eq_bound_height_max bctx eq))).
       subst eql. revert x h H.
       induction x;intros;simpl. auto. 
       rewrite <-app_comm_cons in H. simpl in H.
       remember (eq_bound_height_eql bctx (x ++ eq :: x0)). assert(n=n) by trivial.
       spec IHx n H0;clear H0.
       remember (eq_bound_height_eql bctx x).
       remember (eq_bound_height_eql bctx x0).
       remember (eq_bound_height_max bctx a).
       remember (eq_bound_height_max bctx eq). clear -H IHx. subst n.
       rewrite <- Max.max_assoc, (Max.max_comm _ n2),Max.max_assoc in H. 
       trivial.
  assert (eq_bound_height_max bctx eq <=h). clear -H1.
    generalize (Max.le_max_r (eq_bound_height_eql bctx x)
       (max (eq_bound_height_eql bctx x0)
          (eq_bound_height_max bctx eq)));intro. rewrite <-H1 in H.
    generalize (Max.le_max_r (eq_bound_height_eql bctx x0) (eq_bound_height_max bctx eq));intro.
    simpl. omega.
  clear -H2.
  destruct eq as [[o1 o2] o3]. 
  unfold eq_bound_height_max,eq_bound_height in *. revert H2.
  simpl. 
  case_eq (bound_object bctx o1).
  case_eq (bound_object bctx o2).
  case_eq (bound_object bctx o3). intros. destruct x1,x0,x.
  unfold proper_bound_height. unfold sord,ord. simpl. 
  remember (max
        (max (max (height s0 + 1) (height s1 + 1))
           (max (height s2 + 1) (height s3 + 1)))
        (max (height s4 + 1) (height s5 + 1))).
  generalize (Max.le_max_l
   (max (max (height s0 + 1) (height s1 + 1))
           (max (height s2 + 1) (height s3 + 1)))
        (max (height s4 + 1) (height s5 + 1)));intro.
  generalize (Max.le_max_r
   (max (max (height s0 + 1) (height s1 + 1))
           (max (height s2 + 1) (height s3 + 1)))
        (max (height s4 + 1) (height s5 + 1)));intro.
  rewrite <-Heqn in H3,H4. clear Heqn.
  remember (max (max (height s0 + 1) (height s1 + 1))
        (max (height s2 + 1) (height s3 + 1))).
  generalize (Max.le_max_l 
      (max (height s0 + 1) (height s1 + 1))
      (max (height s2 + 1) (height s3 + 1))).
  generalize (Max.le_max_r 
      (max (height s0 + 1) (height s1 + 1))
      (max (height s2 + 1) (height s3 + 1))). intros.
  rewrite <-Heqn0 in H5,H6. clear Heqn0.
  repeat rewrite NPeano.Nat.max_lub_iff in *. omega.
Qed.

Definition eql_bounds_size h bctx (l : list equation): nat :=
 fold_right (fun c a => a + eq_bounds_size h bctx c) 0 l.

Lemma bound_equation_eq_size_dec: forall bctx bctx' eq ls h,
 eq_bound_height h bctx eq ->
 bound_equation bctx eq = br_narrower ls bctx' ->
  (eq_bounds_size h bctx' eq < eq_bounds_size h bctx eq)%nat.
Proof.
 intros.
 generalize (bound_decreases_strict _ _ _ _ _ H0 H);intro.
 assert (forall v, var_bound_size h bctx' v <= var_bound_size h bctx v).
  intro. apply (bound_decreases bctx bctx' eq ls h);trivial.
  destruct H1 as [? [? ?]]. destruct eq as [[? ?] ?]. clear H0.
 unfold eq_bounds_size, var_bound_size, in_eq_vars in *.
  destruct o;destruct o0;destruct o1; simpl in *.
 Focus 8. inv H1. contr. destruct H0; contr. 
 Focus 7. inv H1. contr. inv H0;contr. trivial.
 Focus 6. inv H1;contr. inv H0; contr. omega.
 Focus 5. inv H1;contr. inv H0. spec H2 v0; omega. spec H2 v; omega.
 Focus 4. inv H1;contr. omega. inv H0;contr.
 Focus 3. inv H1. spec H2 v0;omega. inv H0;contr. spec H2 v;omega.
 Focus 2. inv H1. spec H2 v0;omega. inv H0;contr. spec H2 v; omega.
 inv H1. generalize (H2 v0);intro; spec H2 v1; omega.
 inv H0. generalize (H2 v);intro; spec H2 v1; omega.
 generalize (H2 v0);intro; spec H2 v; omega.
Qed.

Lemma bound_equation_eq_size_dec2: forall bctx bctx' h a2 ls a,
 eq_bound_height h bctx a -> eq_bound_height h bctx a2 ->
 bound_equation bctx a = br_narrower ls bctx' ->
 (eq_bounds_size h bctx' a2 <= eq_bounds_size h bctx a2)%nat.
Proof.
 intros.
 assert (forall v, (var_bound_size h bctx' v <= var_bound_size h bctx v)%nat).
  intro. apply (bound_decreases bctx bctx' a ls h);trivial.
  clear -H2. destruct a2 as [[? ?] ?]. unfold eq_bounds_size,var_bound_size in *.
  destruct o;destruct o0;destruct o1;simpl.
  generalize (H2 v0);generalize (H2 v1);spec H2 v;intros;omega.
  generalize (H2 v0);spec H2 v;intros;omega.
  generalize (H2 v0);spec H2 v;intros;omega.
  spec H2 v;intros;omega.
  generalize (H2 v0);spec H2 v;intros;omega.
  spec H2 v;intros;omega.
  spec H2 v;intros;omega. auto.
Qed.

Lemma bound_equation_eql_size_dec: forall bctx bctx' h eql ls a,
 list_eq_bound_height h bctx eql -> eq_bound_height h bctx a ->
 bound_equation bctx a = br_narrower ls bctx' ->
  (eql_bounds_size h bctx' eql <= eql_bounds_size h bctx eql)%nat.
Proof.
 intros. revert eql bctx bctx' h ls a H H1 H0.
 induction eql;intros. simpl.  trivial.
 assert (In a (a::eql)) by (simpl;auto). generalize (H a H2);clear H2;intro.
  assert (list_eq_bound_height h bctx eql).
      unfold list_eq_bound_height;intros;apply H;right;trivial.
 spec IHeql bctx bctx' h ls a0 H3 H1 H0.
 apply (bound_equation_eq_size_dec2 _ _ _ _ _ _ H0 H2) in H1.
 simpl in H1. clear - IHeql H1.
 simpl. omega.
Qed.

Lemma eql_bounds_eq_size_decreases1: forall bctx bctx' eql ls h,
  bound_once_equation_list bctx eql = br_narrower ls bctx' -> 
   list_eq_bound_height h bctx eql -> forall a, (eq_bound_height h bctx a ->
     (eq_bounds_size h bctx' a <= eq_bounds_size h bctx a)%nat).
Proof.
  intros. revert eql bctx' ls H0 H.
  induction eql;intros;inv H.
  assert (In a0 (a0::eql)) by (simpl;auto). generalize (H0 a0 H);clear H;intro.
  assert (list_eq_bound_height h bctx eql).
      unfold list_eq_bound_height;intros;apply H0;right;trivial.
  revert H3. case_eq(bound_once_equation_list bctx eql);intros. 3:inv H4.
  2:apply (bound_equation_eq_size_dec2 _ _ _ _ _ _ H H1 H4).
  spec IHeql b l H2 H3.
  revert H4. case_eq (bound_equation b a0);intros;inv H5;trivial.
    generalize (var_height_bound_list_preserved _ _ _ _ _ H3 H2);intro.
    apply (eq_bound_height_preserved _ _ _ _ H5) in H.
    apply (eq_bound_height_preserved _ _ _ _ H5) in H1.
  apply (bound_equation_eq_size_dec2 b bctx' h a l0 a0 H H1) in H4. simpl in H4.
  omega.
Qed.

Lemma eql_bounds_eq_size_decreases2: forall bctx bctx' eql ls h,
  bound_once_equation_list bctx eql = br_narrower ls bctx' -> 
   list_eq_bound_height h bctx eql -> 
    exists a , In a eql /\
       (eq_bounds_size h bctx' a < eq_bounds_size h bctx a)%nat.
Proof.
 intros. revert eql ls bctx' H0 H.
 induction eql;intros;inv H.
 assert (In a (a::eql)) by (simpl;auto). generalize (H0 a H);clear H;intro.
 assert (list_eq_bound_height h bctx eql).
      unfold list_eq_bound_height;intros;apply H0;right;trivial.
 revert H2; case_eq (bound_once_equation_list bctx eql);intros. 3:inv H3.
 Focus 2. 
  exists a;split. left;trivial. 
  apply(bound_equation_eq_size_dec _ _ _ _ _ H H3).
  spec IHeql l b H1 H2. destruct IHeql as [? [? ?]]. 
  revert H3; case_eq(bound_equation b a);intros;inv H6.
  Focus 2. exists x; split;trivial. right;trivial.
  exists a. split. left;trivial. 
  generalize (var_height_bound_list_preserved _ _ _ _ _ H2 H1);intro.
  generalize(eq_bound_height_preserved _ _ _ _ H6 H);intro.
  generalize(bound_equation_eq_size_dec _ _ _ _ _ H7 H3);intro.
  generalize(eql_bounds_eq_size_decreases1 _ b eql l h H2 H1 a H);intro.
  omega.
Qed.

Lemma bound_once_equation_list_size_dec: forall bctx' bctx eql ls,
  bound_once_equation_list bctx eql = br_narrower ls bctx' ->
   (eql_bounds_size (eq_bound_height_eql bctx' eql) bctx' eql <
     eql_bounds_size (eq_bound_height_eql bctx eql) bctx eql)%nat.
Proof. 
  intros. rename H into teq1.
  assert ((eq_bound_height_eql bctx' eql <= eq_bound_height_eql bctx eql)%nat).
    remember (eq_bound_height_eql bctx eql).
    generalize (height_max_sufficient _ _ _ Heqn);intro.
    generalize (var_height_bound_list_preserved2 _ _ _ _ _ teq1 H);intro.
    clear -H H0.
    revert eql bctx' H H0. induction eql;intros. simpl;omega.
    assert (In a (a::eql)) by (simpl;auto). generalize (H a H1);clear H1;intro.
    assert (list_eq_bound_height n bctx eql).
      unfold list_eq_bound_height;intros;apply H;right;trivial.
    spec IHeql bctx' H2 H0.
    remember (eq_bound_height_eql bctx' eql). simpl.
    rewrite <-Heqn0. clear -IHeql H1 H0.
    generalize (Max.max_spec n0 (eq_bound_height_max bctx' a));intro.
    destruct H;destruct H;simpl in *;rewrite H2;trivial.
    clear -H0 H1. revert H1.
    unfold eq_bound_height_max. unfold eq_bound_height. simpl. destruct a as [[? ?] ?].
    case_eq (bound_object bctx o);case_eq (bound_object bctx o1);case_eq (bound_object bctx o0).
    case_eq (bound_object bctx' o);case_eq (bound_object bctx' o1);case_eq (bound_object bctx' o0).
    intros;destruct x,x0,x1,x2,x3,x4. 
    destruct H6 as [[? ?] ?]. destruct H8 as [[? ?] ? ?]. destruct H10.
    unfold height_preserved2 in H0. unfold sord in *. simpl in *.
    apply Max.max_lub. apply Max.max_lub.
     destruct o;inv H2; inv H5. spec H0 v;rewrite H13,H12 in H0.
     destruct H0. simpl in *. spec H0 H6; spec H2 H7. 
     apply Max.max_lub;omega. 
     apply Max.max_lub;omega. 
     destruct o0;inv H;inv H3. spec H0 v. rewrite H13,H12 in H0.
     destruct H0. simpl in *. spec H0 H9; spec H H8. 
     apply Max.max_lub;omega. 
     apply Max.max_lub;omega. 
     destruct o1;inv H4;inv H1. spec H0 v. rewrite H13,H12 in H0.
     destruct H0. simpl in *. spec H0 H10; spec H1 H11. 
     apply Max.max_lub;omega. 
     apply Max.max_lub;omega.
  assert (eql_bounds_size (eq_bound_height_eql bctx' eql) bctx' eql <=
     eql_bounds_size (eq_bound_height_eql bctx eql) bctx' eql).
     remember (eq_bound_height_eql bctx' eql).
     remember (eq_bound_height_eql bctx eql).
     generalize (height_max_sufficient _ _ _ Heqn0);intro.
     generalize (var_height_bound_list_preserved2 _ _ _ _ _ teq1 H0);intro.     
     generalize (height_max_sufficient _ _ _ Heqn);intro.
     clear -H H2 H1.
     revert eql H2. induction eql;intros;simpl. auto.
     simpl.
     assert (In a (a::eql)) by (simpl;auto). generalize (H2 a H0);clear H0;intro.
     assert (list_eq_bound_height n bctx' eql).
      unfold list_eq_bound_height;intros;apply H2;right;trivial.
      spec IHeql H3; clear H3 H2.
     assert (eq_bounds_size n bctx' a<=eq_bounds_size n0 bctx' a).
     2:simpl in *;omega.
     clear -H H0. destruct a as [[? ?] ?]. unfold eq_bounds_size.
     unfold eq_bound_height in H0. revert H0. simpl.
     case_eq (bound_object bctx' o);case_eq (bound_object bctx' o0);
     case_eq (bound_object bctx' o1). intros. destruct x1,x0,x.
     destruct H3.  destruct H4.
     assert (forall o s1 s2 b, proper_bound_height n s1 s2 ->
        bound_object bctx' o =
         exist (fun b : bound_type => bound_prop b) (s1, s2) b->
           (o_bounds_size n bctx' o <= o_bounds_size n0 bctx' o)%nat).
       intros. destruct o2;simpl; auto. 
       case_eq (lookup bctx' v);intros.
       simpl in H7. rewrite H7 in H8. inv H8. simpl.
       destruct H6. unfold bound_prop,fst,snd in b2.
       assert (Share.Ord s6 s7).
         clear - b2. rewrite leq_join_sub. tauto.
       apply (Share.share_metric_dif_monotonic _ _ _ _ H9 H H6 H8). 
    generalize (H6 o0 _ _ _ H4 H1);intro.
    generalize (H6 o _ _ _ H3 H2);intro.
    generalize (H6 o1 _ _ _ H5 H0);intro. simpl in *. omega.
   assert ((eql_bounds_size (eq_bound_height_eql bctx eql) bctx' eql <
     eql_bounds_size (eq_bound_height_eql bctx eql) bctx eql)%nat).
     2:destruct H1;simpl in *;omega.
   clear -teq1.
   remember (eq_bound_height_eql bctx eql).
   apply height_max_sufficient in Heqn. 
   generalize (eql_bounds_eq_size_decreases2 _ _ _ _ _ teq1 Heqn);intros.
   generalize (eql_bounds_eq_size_decreases1 _ _ _ _ _ teq1 Heqn);intros.
   clear -H H0 Heqn.
   destruct H as [? [? ?]]. apply In_split in H. destruct H as [? [? ?]].
   subst eql.
   assert ((eql_bounds_size n bctx' x1 <= eql_bounds_size n bctx x1)%nat).
    assert (list_eq_bound_height n bctx x1).
      clear -Heqn. intro. intros. apply Heqn. 
      apply (in_cons x eq) in H.  apply in_or_app;right;trivial. 
    clear -H0 H. revert x1 H. induction x1;intros. simpl;trivial.
    simpl in *.
    assert (In a (a::x1)) by (simpl;auto). generalize (H a H1);clear H1;intro.
    assert (list_eq_bound_height n bctx x1).
      unfold list_eq_bound_height;intros;apply H;right;trivial.
    spec IHx1 H2. clear H2 H.
    spec H0 a H1. omega.
    revert x0 Heqn. induction x0;intros. simpl in *. unfold sord. simpl. omega.
    simpl. 
    assert (list_eq_bound_height n bctx (x0++x::x1)).
      unfold list_eq_bound_height;intros;apply Heqn;right;trivial.
    spec IHx0 H2.
    assert (In a ((a::x0) ++ x:: x1)) by (simpl;auto).
      generalize (Heqn a H3);clear H3;intro.
    spec H0 a H3. clear -H0 IHx0.
    unfold sord in *. simpl in *. omega.
Qed.

Definition bounds_size (p : bcontext*list equation*list substitution): nat :=
  match p with (bctx,eql,lsub) => 
   let h:= eq_bound_height_eql bctx eql in
   eql_bounds_size h bctx eql end.

Function bound_eql_fix (p :bcontext*list equation*list substitution) 
  {measure bounds_size p} :  option (bcontext*list substitution) :=
  match p with (bctx,eql, subsl) =>
  match (bound_once_equation_list bctx eql) with
   | br_absurd => None
   | br_unchanged => Some (bctx, subsl)
   | br_narrower ls bctx' => 
      bound_eql_fix (bctx',eql,ls++subsl)
  end
 end.
Proof.
  intros. unfold bounds_size. 
  apply (bound_once_equation_list_size_dec _ _ _ _ teq1).
Defined.

Lemma bound_eql_fix_none: forall p,
  bound_eql_fix p = None -> bound_absurd (fst(fst p)) (snd(fst p)).
Proof.
  intros. remember (bounds_size p).
  assert (bounds_size p <= n)%nat by omega.
  destruct p as [[? ?] ?].  simpl. clear -H0 H.  revert b l l0 H0 H. 
  induction n; intros.
  assert (bounds_size (b,l,l0) = 0) by omega. clear H0.
  rewrite bound_eql_fix_equation in H.
  remember (bound_once_equation_list b l). symmetry in Heqb0. icase b0.
  generalize (bound_once_equation_list_size_dec _ _ _ _ Heqb0);intro.
  simpl in H1. exfalso;omega.
  apply bound_once_equation_list_absurd;trivial.
  (* now you're in the inductive case. *)
  rewrite bound_eql_fix_equation in H.
  remember (bound_once_equation_list b l). symmetry in Heqb0. icase b0.
  simpl in *.
  assert ((eql_bounds_size (eq_bound_height_eql b0 l) b0 l <= n)%nat) by
   (generalize (bound_once_equation_list_size_dec _ _ _ _ Heqb0);intro;omega).
  spec IHn b0 l (l1++l0) H1 H.
  clear -IHn Heqb0.
  apply bound_once_equation_list_narrower in Heqb0.
  intro. intros. spec Heqb0 ctx H H0. destruct Heqb0.
  apply (IHn ctx H2 H0).
  apply bound_once_equation_list_absurd;trivial.
Qed.

Lemma bound_eql_fix_some: forall b l l0 bctx subsl,
  bound_eql_fix (b,l,l0) = Some (bctx, subsl) -> 
   (forall ctx : context, bounded_context ctx b -> eval ctx l -> eval ctx l0->
     eval ctx subsl /\ bounded_context ctx bctx).
Proof.
  intros. 
  remember (bounds_size (b,l,l0)).
  assert (bounds_size (b,l,l0) <= n)%nat by omega. clear Heqn.
  revert n b bctx subsl l0 H H0 H2 H3.

  induction n;intros.
  assert((bounds_size (b, l, l0)= 0)%nat) by omega. clear H3.
  rewrite bound_eql_fix_equation in H.
  remember (bound_once_equation_list b l). symmetry in Heqb0. icase b0.
  generalize (bound_once_equation_list_size_dec _ _ _ _ Heqb0);intro.  
  exfalso; simpl in H4; omega. 
  inv H. auto.
  rewrite bound_eql_fix_equation in H.
  remember (bound_once_equation_list b l). symmetry in Heqb0. 
  icase b0;simpl in *. 2:inv H;auto.

  assert ((eql_bounds_size (eq_bound_height_eql b0 l) b0 l <= n)%nat) by
   (generalize (bound_once_equation_list_size_dec _ _ _ _ Heqb0);intro;omega). clear H3.
  generalize (bound_once_equation_list_narrower _ _ _ _ Heqb0);intro.
  spec H3 ctx H0 H1. destruct H3.
  assert (eval ctx (l1++l0)).
   clear -H2 H3. revert l1 H3. induction l1;intros. auto. destruct H3.
   split. apply IHl1;auto. auto.
  apply(IHn b0 bctx subsl (l1++l0) H H5 H6 H4). 
Qed.

Definition check_sat (eqs:equation_system) : option (list substitution) := 
  match bound_eql_fix (initial_bcontext,eqs_equations eqs, eqs_substitutions eqs) with
   | None => None
   | Some (_,subsl) => Some subsl 
  (*Some (Equation_system subsl (eqs_equations eqs))*)
 end.

Lemma check_sat_correct1: forall eqs ctx, 
   check_sat eqs = None -> ctx |= eqs -> False.
Proof.
  intros. destruct eqs as [ ln le ls]. unfold check_sat in H. inv H. destruct H0.
  simpl in *.
  remember (bound_eql_fix (initial_bcontext, ls, le)).
  icase o. destruct p. inv H2.
  symmetry in Heqo. apply bound_eql_fix_none in Heqo. simpl in *.
  generalize (initial_bcontext_bounds_all ctx);intro.   spec Heqo ctx H1.
  apply Heqo. tauto.
Qed.

Lemma check_sat_correct2: forall eqs ls', 
   check_sat eqs = Some ls' -> (forall ctx, eval ctx eqs -> eval ctx ls').
Proof.
 intros. destruct eqs as [ln ls le]. unfold check_sat in H. inv H. destruct H0.
 simpl in *.
 remember (bound_eql_fix (initial_bcontext, le, ls)). icase o. destruct p. inv H2.
 symmetry in Heqo.
 generalize (bound_eql_fix_some _ _ _ _ _ Heqo);intros.
 generalize (initial_bcontext_bounds_all ctx);intro.
 destruct H0.
 spec H1 ctx H2 H3 H0. destruct H1;trivial. 
Qed.

Definition SATbounder := fun (ses : sat_equation_system) =>
 match wrapped_ses ses with
 |None => None
 |Some ses' => match check_sat ses' with
               |None => None
               |Some l => Some (unwrapped_ses 
               (Equation_system (eqs_nzvars ses') (l++(eqs_substitutions ses')) (eqs_equations ses')))
               end
 end.

 Lemma SATbounder_None : forall ses,
  SATbounder ses = None -> forall rho, ~rho |= ses.
 Proof with try tauto.
  intro ses.
  unfold SATbounder.
  case_eq (wrapped_ses ses). intros ? ?.
  case_eq (check_sat e); repeat intro.
  inv H1. apply wrapped_ses_Some with (rho:=rho) in H.
  apply check_sat_correct1 with (ctx:= rho)in H0...
  repeat intro.
  apply wrapped_ses_None with (rho:=rho) in H...
 Qed.

 Lemma SATbounder_Some : forall ses ses',
  SATbounder ses = Some ses' ->
  forall rho, rho |= ses <-> rho |= ses'.
 Proof with try tauto.
  intros ses ses'.
  unfold SATbounder.
  case_eq (wrapped_ses ses). intros ? ?.
  case_eq (check_sat e); intros;inv H1.
  apply wrapped_ses_Some with (rho:=rho) in H.
  rewrite <-unwrapped_ses_eval. rewrite H.
  generalize (check_sat_correct2 _ _ H0 rho);intro.
  destruct e as [l1 l2 l3];simpl in *.
  unfold eval_equation_system in *;simpl in *.
  change (eval_list rho (l++l2)) with (rho |= (l++l2)).
  rewrite eval_list_app...
  intros. inv H0.
 Qed.

 Definition ies_bounder:= fun (ies : impl_equation_system) =>
  match SATbounder (ies2ses ies) with
  |None => None
  |Some ses' => Some (Impl_equation_system (impl_exvars ies) (sat_nzvars ses') (sat_equalities ses') (sat_equations ses'))
  end.

 Lemma ies_bounder_None: forall ies,
   ies_bounder ies = None -> forall rho,~rho |= ies.
 Proof with try tauto.
  intro ies.
  unfold ies_bounder.
  case_eq (SATbounder (ies2ses ies));repeat intro.
  inv H0. destruct H1 as [rho' H1].
  apply SATbounder_None with (rho:=[impl_exvars ies => rho']rho) in H...
 Qed.

 Lemma ies_bounder_Some: forall ies ies',
   ies_bounder ies = Some ies' ->
   forall rho, rho |= ies <-> rho |= ies'.
 Proof with try tauto.
  intros ies ies'.
  unfold ies_bounder.
  case_eq (SATbounder (ies2ses ies));repeat intro;inv H0.
  destruct ies as [l1 l2 l3 l4];simpl. 
  split;intro H1;destruct H1 as [rho' H1];
  apply SATbounder_Some with (rho:=[l1 => rho']rho) in H;
  exists rho';
  unfold eval_impl_equation_system,ies2ses in *;simpl in *;
  unfold eval_sat_equation_system in *;simpl in *; tauto.
 Qed.

 Definition IMPLbounder: impl_system -> result impl_system unit := 
  fun (is : impl_system) =>
  let (ies1,ies2) := is in
  match ies_bounder ies1 with
  |None => Simpler tt
  |Some ies1' => match ies_bounder ies2 with
                 |None => Absurd
                 |Some ies2' => Same (ies1',ies2')
                 end
  end.

 Lemma IMPLbounder_Absurd: forall is,
   SAT (ies2ses (fst is)) ->
   IMPLbounder is = Absurd ->
   ~IMPL is.
 Proof with try tauto.
   repeat intro.
   destruct H as [rho H].
   spec H1 rho.
   unfold IMPLbounder in H0.
   destruct is as [ies1 ies2].
   remember (ies_bounder ies1).
   remember (ies_bounder ies2).
   symmetry in Heqo,Heqo0.
   icase o;icase o0.
   apply ies_bounder_None with (rho:=rho) in Heqo0.
   apply Heqo0. apply H1.
   exists rho. rewrite context_override_idem...
 Qed.

 Lemma IMPLbounder_Simpler: forall is,
   IMPLbounder is = Simpler tt ->
   forall rho, rho |= is.
 Proof with try tauto.
   repeat intro.
   unfold IMPLbounder in H.
   destruct is as [ies1 ies2].
   remember (ies_bounder ies1).
   remember (ies_bounder ies2).
   symmetry in Heqo,Heqo0.
   icase o;icase o0.
   apply ies_bounder_None with (rho:=rho) in Heqo...
   apply ies_bounder_None with (rho:=rho) in Heqo...
  Qed.

 Lemma IMPLbounder_Same: forall is is',
   IMPLbounder is = Same is' ->
   forall rho, (rho |= fst is <-> rho |= fst is') /\
  (rho |= snd is <-> rho |= snd is').
 Proof with try tauto.
   repeat intro.
   unfold IMPLbounder in H.
   destruct is as [ies1 ies2].
   remember (ies_bounder ies1).
   remember (ies_bounder ies2).
   symmetry in Heqo,Heqo0.
   icase o;icase o0. inv H.
   generalize (ies_bounder_Some _ _ Heqo rho);intro.
   generalize (ies_bounder_Some _ _ Heqo0 rho);intro.
   simpl in *...
 Qed.

End Bounder.
  
  

(*

Definition check_imply (ante:equation_system) (conseq:equation_system) 
  : option bool* (list substitution)*(list substitution) :=
 match bound_eql_fix (initial_bcontext,eqs_equations ante, eqs_substitutions ante) with
   | None => (Some true,nil,nil)
   | Some (bante,subsla) =>  
      match bound_eql_fix (bante,eqs_equations conseq, eqs_substitutions conseq) with
       | None => (Some false,nil,nil) 
       | Some (_,subslc) => (None,subsla, subslc)
      end
 end.

Lemma check_imply_correct1: forall ante conseq l1 l2,
  check_imply ante conseq = (Some true,l1,l2) -> 
     forall ctx, eval ctx ante -> eval ctx conseq.
Proof.
  intros. destruct ante as [asl ael]. destruct conseq as [csl cel].
  unfold check_imply in H. simpl in *. destruct H0. simpl in *.
  remember (bound_eql_fix (initial_bcontext, ael, asl)). icase o.
    2:symmetry in Heqo; apply bound_eql_fix_none in Heqo; simpl in *;
    generalize (initial_bcontext_bounds_all ctx);intro; exfalso; apply (Heqo ctx);trivial.
  destruct p.
  remember (bound_eql_fix (b, cel, csl)). icase o. destruct p. inv H.
Qed.  

Lemma check_imply_correct2: forall ante conseq l1 l2,
  check_imply ante conseq = (Some false,l1,l2) -> 
     forall ctx, eval ctx ante -> eval ctx conseq -> False.
Proof.
  intros. destruct ante as [asl ael]. destruct conseq as [csl cel].
  unfold check_imply in H. simpl in *. 
  remember (bound_eql_fix (initial_bcontext, ael, asl)). icase o. destruct p.
  remember (bound_eql_fix (b, cel, csl)). icase o. destruct p. inv H.
  inv H.
  symmetry in Heqo;symmetry in Heqo0. destruct H0,H1.
  apply bound_eql_fix_none in Heqo0. simpl in *. apply (Heqo0 ctx);trivial.
  generalize (initial_bcontext_bounds_all ctx);intro;
  apply (bound_eql_fix_some _ _ _ _ _ Heqo ctx);trivial. 
Qed.

Lemma check_imply_correct3: forall ante conseq l1 l2 s,
  check_imply ante conseq = (s,l1,l2) -> 
   (forall ctx, eval ctx ante -> eval ctx l1)/\ 
   (forall ctx, eval ctx ante -> eval ctx conseq -> eval ctx l2).
Proof.
  intros. destruct ante as [asl ael]. destruct conseq as [csl cel].
  unfold check_imply in H. simpl in *. 
  remember (bound_eql_fix (initial_bcontext, ael, asl)). icase o. destruct p.
  2:inv H;split;intros;simpl;trivial.
  remember (bound_eql_fix (b, cel, csl)). icase o. destruct p. inv H.
  2:inv H;split;intros;simpl;trivial.
  symmetry in Heqo, Heqo0.
  split;intros.
   generalize (initial_bcontext_bounds_all ctx);intro. destruct H. simpl in *.
  apply (bound_eql_fix_some _ _ _ _ _ Heqo ctx);trivial. 
  generalize (initial_bcontext_bounds_all ctx);intro. destruct H,H0. simpl in *.
  generalize (bound_eql_fix_some _ _ _ _ _ Heqo ctx H1 H2 H); intros. destruct H4.
  apply (bound_eql_fix_some _ _ _ _ _ Heqo0 ctx); auto.
Qed.
*)


(* Extraction Magic *)
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

Extraction "share_dec.ml" Bounder.
*)


