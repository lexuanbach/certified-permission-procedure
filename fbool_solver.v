Require Import msl.msl_standard.
Require Import share_dec_base.
Require Import share_equation_system.
Require Import base_properties.
Require Import share_dec_interface.


Module Bool_formula (sv : SV) <: BOOL_FORMULA sv.

 Definition var := sv.t.
 Definition context := var -> bool.

 Inductive bF : Type := 
 |valF : bool -> bF
 |varF : var  -> bF
 |andF : bF -> bF -> bF
 |orF  : bF -> bF -> bF
 |implF: bF -> bF -> bF
 |negF : bF -> bF
 |exF  : var -> bF -> bF
 |allF : var -> bF -> bF.

 Fixpoint bF_vars f :=
  match f with
  |valF b => nil 
  |varF v => v::nil
  |andF f1 f2
  |orF f1 f2
  |implF f1 f2 => (bF_vars f1)++(bF_vars f2)
  |negF f'  => bF_vars f'
  |exF v f'  
  |allF v f' => v::bF_vars f'
  end.

 Instance bF_varsable : varsable bF var.
 constructor. intros. apply (bF_vars X).
 Defined.

 Fixpoint beval (ctx : context) (f : bF):=
  match f with
  |valF b => b
  |varF v => ctx v
  |andF f1 f2 => (beval ctx f1) && (beval ctx f2)
  |orF f1 f2 => (beval ctx f1) || (beval ctx f2)
  |implF f1 f2 => implb (beval ctx f1) (beval ctx f2)
  |negF f' => negb (beval ctx f')
  |exF v f' => (beval (upd ctx v true) f') || (beval (upd ctx v false) f')
  |allF v f' => (beval (upd ctx v true) f') && (beval (upd ctx v false) f')
  end.
 Instance bF_eval: evalable context bF.
 constructor. intros rho f.
 apply (beval rho f = true).
 Defined.

 Definition valid {A B} `{evalable A B}:= 
  fun (b : B) => forall a, a |= b.
 Definition unsat {A B} `{evalable A B}:= 
  fun (b : B) => forall a, ~(a |= b).

 Fixpoint not_free v f: Prop := 
  match f with
  |valF b => True
  |varF v' => match eq_dec v v' with
              |left _ => False
              |right _ => True
              end
  |andF f1 f2 
  |orF f1 f2 
  |implF f1 f2 => (not_free v f1) /\ (not_free v f2)
  |negF f' => not_free v f'
  |exF v' f' 
  |allF v' f' => match eq_dec v v' with
                |left _ => True
                |right _ => not_free v f'
                end
  end.

 Definition full_quan := 
  fun f => forall v, In v (vars f) -> not_free v f.

 Fixpoint bsize (f : bF) :=
  match f with
  |valF b => 1 
  |varF v => 1
  |andF f1 f2 
  |orF f1 f2 
  |implF f1 f2 => 1 + (bsize f1) + (bsize f2)
  |negF f'  => 1 + (bsize f')
  |exF v f' 
  |allF v f' => 1 + (bsize f') 
  end.

 Fixpoint bsubst (f : bF) (v : var) (b : bool) :=
  match f with
  |valF b'    => valF b'
  |varF v'    => match eq_dec v v' with
                 |left _  => valF b
                 |right _ => varF v'
                 end
  |andF f1 f2 => andF (bsubst f1 v b) (bsubst f2 v b)
  |orF f1 f2 => orF (bsubst f1 v b) (bsubst f2 v b)
  |implF f1 f2 => implF (bsubst f1 v b) (bsubst f2 v b)
  |negF f'    => negF (bsubst f' v b)
  |exF v' f'  => match eq_dec v v' with
                 |left _  => exF v' f'
                 |right _ => exF v' (bsubst f' v b)
                 end
  |allF v' f' => match eq_dec v v' with
                 |left _  => allF v' f'
                 |right _ => allF v' (bsubst f' v b)
                 end
  end.

 Lemma bF_valid_rewrite: forall (f : bF),
  valid f <-> forall rho, beval rho f = true.
 Proof with try tauto.
  intros...
 Qed.
 Lemma bF_unsat_rewrite: forall (f : bF),
  unsat f <-> forall rho, beval rho f = false.
 Proof with try tauto.
  intros. split;repeat intro.
  spec H rho. simpl in H.
  icase (beval rho f)...
  spec H a. simpl in H0.
  icase (beval a f)...
 Qed.

 Lemma bsize_bsubst : forall v b f,
  bsize (bsubst f v b) = bsize f.
 Proof with try tauto.
  induction f;intros;
  simpl...
  destruct (eq_dec v v0)...
  rewrite IHf1,IHf2...
  rewrite IHf1,IHf2...
  rewrite IHf1,IHf2...
  rewrite IHf...
  destruct (eq_dec v v0)... simpl.
  rewrite IHf...
  destruct (eq_dec v v0)... simpl.
  rewrite IHf...
 Qed.

 Instance bF_eq_dec: EqDec bF.
 Proof with try tauto;disc.
 induction a;intros.
 icase a'.
 destruct (bool_dec b b0)... left;subst...
 right;intro;subst;inv H...
 right... right... right... right... right...
 right... right...
 icase a'. right...
 destruct (eq_dec v v0);subst...
 right;intro;inv H...
 right... right... right... right... right... right...
 icase a'. right... right...
 spec IHa1 a'1. spec IHa2 a'2.
 destruct IHa1;destruct IHa2;subst...
 right;intro;inv H... right;intro;inv H...
 right;intro;inv H... right... right... right... right... right...
 icase a'. right... right... right...
 spec IHa1 a'1. spec IHa2 a'2.
 destruct IHa1;destruct IHa2;subst...
 right;intro;inv H... right;intro;inv H...
 right;intro;inv H... right... right... right... right... 
 icase a'. right... right... right... right...
 spec IHa1 a'1. spec IHa2 a'2.
 destruct IHa1;destruct IHa2;subst...
 right;intro;inv H... right;intro;inv H...
 right;intro;inv H... right... right... right...
 icase a'. right... right... right... right... right...
 spec IHa a'. destruct IHa ;subst...
 right;intro;inv H...
 right... right...
 icase a'. right... right... right... right... right... right...
 spec IHa a'. destruct IHa ;subst...
 destruct (eq_dec v v0);subst... right;intro;inv H...
 right;intro;inv H... right...
 icase a'. right... right... right... right... right... right... right...
 spec IHa a'. destruct IHa ;subst...
 destruct (eq_dec v v0);subst... right;intro;inv H...
 right;intro;inv H...
 Defined.

 Lemma beval_bsubst: forall f rho v b,
  beval rho (bsubst f v b) = beval (upd rho v b) f.
 Proof with try tauto.
  induction f;intros;
  simpl...
  destruct (eq_dec v0 v);simpl.
  subst;rewrite upd_eq...
  rewrite upd_neq...
  f_equal. apply IHf1. apply IHf2.
  f_equal. apply IHf1. apply IHf2.
  f_equal. apply IHf1. apply IHf2.
  f_equal. apply IHf.
  destruct (eq_dec v0 v);subst;simpl.
  repeat rewrite upd_absorb...
  f_equal;rewrite upd_swap;
  try apply IHf...
  destruct (eq_dec v0 v);subst;simpl.
  repeat rewrite upd_absorb...
  f_equal;rewrite upd_swap;
  try apply IHf...
 Qed.

 Lemma bsubst_id: forall f v b,
  ~In v (vars f) ->
  bsubst f v b = f.
 Proof with try tauto.
  induction f;intros;simpl.
  icase b.
  simpl in H.
  destruct (eq_dec v0 v)...
  subst...
  simpl in H. repeat rewrite in_app_iff in H.
  assert (~In v (vars f1) /\ ~In v (vars f2)) by tauto.
  destruct H0. spec IHf1 v b H0.  spec IHf2 v b H1.
  rewrite IHf1,IHf2...
  simpl in H. repeat rewrite in_app_iff in H.
  assert (~In v (vars f1) /\ ~In v (vars f2)) by tauto.
  destruct H0. spec IHf1 v b H0.  spec IHf2 v b H1.
  rewrite IHf1,IHf2...
  simpl in H. repeat rewrite in_app_iff in H.
  assert (~In v (vars f1) /\ ~In v (vars f2)) by tauto.
  destruct H0. spec IHf1 v b H0.  spec IHf2 v b H1.
  rewrite IHf1,IHf2...
  spec IHf v b H. rewrite IHf...
  simpl in H. assert (v <> v0 /\ ~In v0 (vars f)) by tauto.
  destruct H0.
  destruct (eq_dec v0 v)... rewrite IHf...
  simpl in H. assert (v <> v0 /\ ~In v0 (vars f)) by tauto.
  destruct H0.
  destruct (eq_dec v0 v)... rewrite IHf...
 Qed.

 Lemma bsubst_reduce: forall v b b' f,
  bsubst (bsubst f v b) v b' = bsubst f v b.
 Proof with try tauto.
  induction f;intros;
  simpl...
  destruct (eq_dec v v0)...
  simpl.
  destruct (eq_dec v v0)...
  f_equal...
  f_equal...
  f_equal...
  f_equal...
  destruct (eq_dec v v0). subst.
  simpl. destruct (eq_dec v0 v0)...
  simpl. destruct (eq_dec v v0)...
  rewrite IHf...
  destruct (eq_dec v v0). subst.
  simpl. destruct (eq_dec v0 v0)...
  simpl. destruct (eq_dec v v0)...
  rewrite IHf...
 Qed.

 Lemma bsubst_comm: forall v v' b b' f,
  v <> v' ->
  bsubst (bsubst f v b) v' b' = bsubst (bsubst f v' b') v b.
 Proof with try tauto.
  induction f;intros;
  simpl...
  destruct (eq_dec v v0)...
  simpl. subst.
  destruct (eq_dec v' v0).
  simpl;subst... simpl.
  destruct (eq_dec v0 v0)...
  destruct (eq_dec v' v0).
  subst. simpl. destruct (eq_dec v0 v0)...
  simpl. destruct (eq_dec v' v0);
  destruct (eq_dec v v0)...
  spec IHf1 H. spec IHf2 H.
  congruence.
  spec IHf1 H. spec IHf2 H.
  congruence.
  spec IHf1 H. spec IHf2 H.
  congruence.
  spec IHf H. congruence.
  spec IHf H.
  destruct (eq_dec v v0);
  destruct (eq_dec v' v0);subst;simpl...
  destruct (eq_dec v' v0)...
  destruct (eq_dec v0 v0)...
  destruct (eq_dec v0 v0)...
  destruct (eq_dec v v0)...
  destruct (eq_dec v' v0)...
  destruct (eq_dec v v0)...
  rewrite IHf...
  destruct (eq_dec v v0);
  destruct (eq_dec v' v0);subst;simpl...
  destruct (eq_dec v' v0)...
  destruct (eq_dec v0 v0)...
  destruct (eq_dec v0 v0)...
  destruct (eq_dec v v0)...
  destruct (eq_dec v' v0)...
  destruct (eq_dec v v0)...
  rewrite IHf...
 Qed.

 Lemma bsubst_sublist: forall v b f,
  sublist (vars (bsubst f v b)) (vars f).
 Proof with try tauto.
  induction f;repeat intro;simpl in *...
  destruct (eq_dec v v0)...

  rewrite in_app_iff in *.
  destruct H. left. apply IHf1...
  right. apply IHf2... 
  rewrite in_app_iff in *.
  destruct H. left. apply IHf1...
  right. apply IHf2... 
  rewrite in_app_iff in *.
  destruct H. left. apply IHf1...
  right. apply IHf2... 

  apply IHf...
  destruct (eq_dec v v0)...
  simpl in H. destruct H...
  right. apply IHf...
  destruct (eq_dec v v0)...
  simpl in H. destruct H...
  right. apply IHf...
 Qed.

 Lemma bsubst_in: forall f v v' b,
  v' <> v ->
  In v' (vars f) ->
  In v' (vars (bsubst f v b)).
 Proof with try tauto.
  induction f;intros;simpl in *...
  destruct H0;subst...
  destruct (eq_dec v0 v');subst...
  simpl...
  rewrite in_app_iff in *.
  destruct H0. left. apply IHf1...
  right. apply IHf2...
  rewrite in_app_iff in *.
  destruct H0. left. apply IHf1...
  right. apply IHf2...
  rewrite in_app_iff in *.
  destruct H0. left. apply IHf1...
  right. apply IHf2...
  apply IHf...
  destruct (eq_dec v0 v);subst.
  destruct H0;subst... simpl.
  right. apply bsubst_sublist with (v:=v)(b:=b).
  apply IHf...
  destruct H0;subst...
  simpl... simpl. right. apply IHf...
  destruct (eq_dec v0 v);subst.
  destruct H0;subst... simpl.
  right. apply bsubst_sublist with (v:=v)(b:=b).
  apply IHf...
  destruct H0;subst...
  simpl... simpl. right. apply IHf...
 Qed.

 Lemma bsubst_not_free_id: forall v b f,
  not_free v (bsubst f v b).
 Proof with try tauto.
  induction f;intros;
  simpl...
  destruct (eq_dec v v0);
  simpl... destruct (eq_dec v v0)...
  destruct (eq_dec v v0)...
  subst. simpl. destruct (eq_dec v0 v0)...
  simpl. destruct (eq_dec v v0)...
  destruct (eq_dec v v0)...
  subst. simpl. destruct (eq_dec v0 v0)...
  simpl. destruct (eq_dec v v0)...
 Qed.

 Lemma bsubst_not_free_diff: forall v v' b f,
  v <> v' ->
  (not_free v (bsubst f v' b) <-> not_free v f).
 Proof with try tauto.
  induction f;intros...
  simpl. destruct (eq_dec v' v0)...
  subst. destruct (eq_dec v v0)...

  spec IHf1 H. spec IHf2 H. simpl...
  spec IHf1 H. spec IHf2 H. simpl...
  spec IHf1 H. spec IHf2 H. simpl...
  spec IHf H. simpl.
  destruct (eq_dec v' v0)...
  destruct (eq_dec v v0);
  subst;simpl. destruct (eq_dec v0 v0)...
  destruct (eq_dec v v0)...
  spec IHf H. simpl.
  destruct (eq_dec v' v0)...
  destruct (eq_dec v v0);
  subst;simpl. destruct (eq_dec v0 v0)...
  destruct (eq_dec v v0)...
 Qed.

 Lemma bsubst_upd_reduce: forall f rho v b b',
  beval (upd rho v b) (bsubst f v b') = beval rho (bsubst f v b').
 Proof with try tauto.
  induction f;intros;
  simpl...
  destruct (eq_dec v0 v);simpl...
  rewrite upd_neq...
  f_equal. apply IHf1. apply IHf2.
  f_equal. apply IHf1. apply IHf2.
  f_equal. apply IHf1. apply IHf2.
  f_equal. apply IHf.
  destruct (eq_dec v0 v);subst;simpl.
  repeat rewrite upd_absorb...
  f_equal;rewrite upd_swap;
  try apply IHf...
  destruct (eq_dec v0 v);subst;simpl.
  repeat rewrite upd_absorb...
  f_equal;rewrite upd_swap;
  try apply IHf...
 Qed.
 
 Lemma beval_upd_not_in: forall f v b rho,
  ~In v (vars f) ->
  beval (upd rho v b) f = beval rho f.
 Proof with try tauto. 
  induction f;intros;simpl...
  simpl in H. assert (v <> v0) by tauto.
  rewrite upd_neq... intro;subst...
  assert (~In v (vars f1) /\ ~In v (vars f2)).
   simpl in H. rewrite in_app_iff in H...
  destruct H0.
  rewrite IHf1,IHf2...
  assert (~In v (vars f1) /\ ~In v (vars f2)).
   simpl in H. rewrite in_app_iff in H...
  destruct H0.
  rewrite IHf1,IHf2...
  assert (~In v (vars f1) /\ ~In v (vars f2)).
   simpl in H. rewrite in_app_iff in H...
  destruct H0.
  rewrite IHf1,IHf2...
  rewrite IHf...
  simpl in H. assert (v <> v0 /\ ~In v0 (vars f)) by tauto.
  destruct H0.
  assert (v0 <> v). intro;subst...
  f_equal;rewrite upd_swap;try rewrite IHf...
  simpl in H. assert (v <> v0 /\ ~In v0 (vars f)) by tauto.
  destruct H0.
  assert (v0 <> v). intro;subst...
  f_equal;rewrite upd_swap;try rewrite IHf...
 Qed. 

  Lemma not_free_upd: forall f v rho,
   not_free v f -> forall b, beval (upd rho v b) f = beval rho f.
  Proof with try tauto.
   induction f;intros;simpl in *...
   icase (eq_dec v0 v);subst;simpl...
   rewrite upd_neq...
   rewrite IHf1,IHf2...
   rewrite IHf1,IHf2...
   rewrite IHf1,IHf2...
   rewrite IHf...
   icase (eq_dec v0 v);subst.
   repeat rewrite upd_absorb...
   repeat rewrite upd_swap with (x:=v0)...
   spec IHf v0. repeat rewrite IHf...
   icase (eq_dec v0 v);subst.
   repeat rewrite upd_absorb...
   repeat rewrite upd_swap with (x:=v0)...
   spec IHf v0. repeat rewrite IHf...
  Qed.

 Lemma not_free_trivial: forall bf v,
  ~In v (vars bf) -> not_free v bf.
 Proof with try tauto.
  induction bf;intros;simpl in *...
  destruct (eq_dec v0 v);subst...
  rewrite in_app_iff in H.
  split;try apply IHbf1; try apply IHbf2...
  rewrite in_app_iff in H.
  split;try apply IHbf1; try apply IHbf2...
  rewrite in_app_iff in H.
  split;try apply IHbf1; try apply IHbf2...
  apply IHbf...
  destruct (eq_dec v0 v);subst... apply IHbf...
  destruct (eq_dec v0 v);subst... apply IHbf...
 Qed.

 Lemma full_quan_andF: forall f1 f2,
  full_quan (andF f1 f2) <-> full_quan f1 /\ full_quan f2.
 Proof with try tauto.
  intros.
  split;intros H.
  split;intros v H1;
  spec H v;simpl in *;rewrite in_app_iff in *...
  destruct H.
  intros v H2;spec H v;spec H0 v.
  simpl in H2. rewrite in_app_iff in H2;simpl in *...
  generalize (not_free_trivial f1 v);intro.
  generalize (not_free_trivial f2 v);intro.
  tauto.
 Qed.

 Lemma full_quan_orF: forall f1 f2,
  full_quan (orF f1 f2) <-> full_quan f1 /\ full_quan f2.
 Proof with try tauto.
  intros.
  split;intros H.
  split;intros v H1;
  spec H v;simpl in *;rewrite in_app_iff in *...
  destruct H.
  intros v H2;spec H v;spec H0 v.
  simpl in H2. rewrite in_app_iff in H2;simpl in *...
  generalize (not_free_trivial f1 v);intro.
  generalize (not_free_trivial f2 v);intro.
  tauto.
 Qed.

 Lemma full_quan_implF: forall f1 f2,
  full_quan (implF f1 f2) <-> full_quan f1 /\ full_quan f2.
 Proof with try tauto.
  intros.
  split;intros H.
  split;intros v H1;
  spec H v;simpl in *;rewrite in_app_iff in *...
  destruct H.
  intros v H2;spec H v;spec H0 v.
  simpl in H2. rewrite in_app_iff in H2;simpl in *...
  generalize (not_free_trivial f1 v);intro.
  generalize (not_free_trivial f2 v);intro.
  tauto.
 Qed.

 Lemma full_quan_negF: forall f,
  full_quan (negF f) <-> full_quan f.
 Proof with try tauto.
  intros. split;intros H v H1;spec H v;firstorder.
 Qed.

 Lemma full_quan_exF: forall f v b,
  full_quan (exF v f) <-> full_quan (bsubst f v b).
 Proof with try tauto.
  intros.
  unfold full_quan.
  split;intros.
  simpl in *.
  destruct (eq_dec v v0);subst.
  apply bsubst_not_free_id.
  spec H v0. spec H. right.
  eapply bsubst_sublist. apply H0.
  destruct (eq_dec v0 v);subst...
  apply bsubst_not_free_diff...

  simpl in H0. simpl.
  destruct (eq_dec v0 v);subst...
  destruct H0;subst...
  rewrite<- bsubst_not_free_diff...
  apply H...
  apply bsubst_in... trivial.
 Qed.

 Lemma full_quan_allF: forall f v b,
  full_quan (allF v f) <-> full_quan (bsubst f v b).
 Proof with try tauto.
  intros.
  unfold full_quan.
  split;intros.
  simpl in *.
  destruct (eq_dec v v0);subst.
  apply bsubst_not_free_id.
  spec H v0. spec H. right.
  eapply bsubst_sublist. apply H0.
  destruct (eq_dec v0 v);subst...
  apply bsubst_not_free_diff...

  simpl in H0. simpl.
  destruct (eq_dec v0 v);subst...
  destruct H0;subst...
  rewrite<- bsubst_not_free_diff...
  apply H...
  apply bsubst_in... trivial.
 Qed.

 Lemma full_quan_case: forall f,
  full_quan f ->
  (valid f \/ unsat f).
 Proof with try tauto.
  intros f H. remember (bsize f) as n.
  assert (bsize f <= n) by omega. clear Heqn.
  revert H0 H. revert f. induction n;intros;rewrite bF_unsat_rewrite in *.
  inv H0. icase f. icase f.
  - icase b; firstorder.
  - spec H v. simpl in H. spec H...
    destruct (eq_dec v v)...
  - assert (bsize f1 <= n /\ bsize f2 <= n) by (simpl in H0;omega).
    destruct H1 as [Hf1 Hf2].
    rewrite full_quan_andF in H.
    destruct H.
    generalize (IHn f1 Hf1 H);generalize (IHn f2 Hf2 H1);
    repeat rewrite bF_unsat_rewrite;intros;simpl;
    icase H2;icase H3;[left|right|right|right];
    intro rho;spec H2 rho;spec H3 rho;simpl in *;try rewrite H2,H3...
  - assert (bsize f1 <= n /\ bsize f2 <= n) by (simpl in H0;omega).
    destruct H1 as [Hf1 Hf2].
    rewrite full_quan_orF in H.
    destruct H.
    generalize (IHn f1 Hf1 H);generalize (IHn f2 Hf2 H1);
    repeat rewrite bF_unsat_rewrite;intros;simpl;
    icase H2;icase H3;[left|left|left|right];
    intro rho;spec H2 rho;spec H3 rho;simpl in *;try rewrite H2,H3...
  - assert (bsize f1 <= n /\ bsize f2 <= n) by (simpl in H0;omega).
    destruct H1 as [Hf1 Hf2].
    rewrite full_quan_implF in H.
    destruct H.
    generalize (IHn f1 Hf1 H);generalize (IHn f2 Hf2 H1);
    repeat rewrite bF_unsat_rewrite;intros;simpl;
    icase H3;icase H2; [left|right|left|left];
    intro rho;spec H2 rho;spec H3 rho;simpl in *;try rewrite H2,H3...
  - assert (bsize f <= n) by (simpl in H0;omega).
    rewrite full_quan_negF in H. spec IHn f H1 H.
    repeat rewrite bF_unsat_rewrite in *;intros;simpl.
    icase IHn;[right|left];
    intro rho; spec H2 rho;simpl in*;try rewrite H2...
  - assert (bsize (bsubst f v true) <= n /\ bsize (bsubst f v false) <= n).
     split;rewrite bsize_bsubst;simpl in H0;omega.
    destruct H1.
    copy H. rewrite full_quan_exF with (b:=true) in H.
    rewrite full_quan_exF with (b:= false) in H3.
    generalize (IHn _ H1 H);intro.
    generalize (IHn _ H2 H3);intro.
    repeat rewrite bF_unsat_rewrite in *.
    icase H4;icase H5;[left|left|left|right];
    intro rho;spec H4 rho;spec H5 rho;
    simpl in *;rewrite beval_bsubst in *; rewrite H4,H5...
  - assert (bsize (bsubst f v true) <= n /\ bsize (bsubst f v false) <= n).
     split;rewrite bsize_bsubst;simpl in H0;omega.
    destruct H1.
    copy H. rewrite full_quan_allF with (b:=true) in H.
    rewrite full_quan_allF with (b:= false) in H3.
    generalize (IHn _ H1 H);intro.
    generalize (IHn _ H2 H3);intro.
    repeat rewrite bF_unsat_rewrite in *.
    icase H4;icase H5;[left|right|right|right];
    intro rho;spec H4 rho;spec H5 rho;
    simpl in *;rewrite beval_bsubst in *; rewrite H4,H5...
  Qed.

End Bool_formula.

Module BF_solver (sv : SV) (Import bf : BOOL_FORMULA sv) <: BF_SOLVER sv bf.

 Inductive fType : Type :=
 |bT : bool -> fType
 |fT : bF -> fType.

 Definition check_bval (f : bF) :=
 match f with
 |valF b => bT b
 |_ => fT f
 end.

 Lemma check_bval_bT : forall f b,
  check_bval f = bT b <-> f = valF b.
 Proof with try tauto.
  intros. icase f;simpl;
  split;intros;inv H...
 Qed.

 Lemma check_bval_fT : forall f f',
  check_bval f = fT f' -> f = f'.
 Proof with try tauto.
  intros. icase f;inv H...
 Qed.

 Lemma check_bval_fT2: forall f f',
  check_bval f = fT f' -> f = f' /\ forall b, f <> valF b.
 Proof with try tauto.
  intros. icase f;inv H;
  split;repeat intro;disc...
 Qed.

 Fixpoint fsimpl_onepass (f : bF) : bF :=
 match f with
 |andF f1 f2 => match check_bval f1 with
                |bT b => if b then f2 else valF false
                |fT f1' => match check_bval f2 with
                           |bT b => if b then f1 else valF false
                           |fT f2' => andF f1 f2
                           end
                end
 |orF f1 f2 => match check_bval f1 with
                |bT b => if b then valF true else f2
                |fT f1' => match check_bval f2 with
                           |bT b => if b then valF true else f1
                           |fT f2' => orF f1 f2
                           end
               end
 |implF f1 f2 => match check_bval f1 with
                  |bT b => if b then f2 else valF true
                  |fT f1' => match check_bval f2 with
                             |bT b => if b then valF true else negF f1
                             |fT f2' => implF f1 f2
                             end
                  end
 |negF f' => match check_bval f' with
              |bT b => valF (negb b)
              |fT f'' => negF f'
              end
 |exF v f' => match check_bval f' with
               |bT b => valF b
               |fT f'' => exF v f'
               end
 |allF v f' => match check_bval f' with
               |bT b => valF b
               |fT f'' => allF v f'
               end
 |_ => f
 end.


 Lemma fsimpl_onepass_andF: forall f1 f2,
  (fsimpl_onepass (andF f1 f2) = valF false /\ (f1 = valF false \/ f2 = valF false)) \/
  (fsimpl_onepass (andF f1 f2) = f1 /\ f2 = valF true) \/
  (fsimpl_onepass (andF f1 f2) = f2 /\ f1 = valF true) \/
  (fsimpl_onepass (andF f1 f2) = andF f1 f2 /\ forall b, f1 <> valF b /\ f2 <> valF b).
 Proof with try tauto.
  intros. simpl.
  case_eq (check_bval f1);intros.
  apply check_bval_bT in H. rewrite H.
  icase b.
  apply check_bval_fT2 in H.
  destruct H. rewrite H.
  case_eq (check_bval f2);intros...
  apply check_bval_bT in H1. rewrite H1.
  icase b0.
  apply check_bval_fT2 in H1.
  destruct H1. rewrite H1.
  repeat right. split;repeat intro;split;repeat intro;subst;
  spec H0 b1;spec H2 b1...
 Qed.

 Lemma fsimpl_onepass_orF: forall f1 f2,
  (fsimpl_onepass (orF f1 f2) = valF true /\ (f1 = valF true \/ f2 = valF true)) \/
  (fsimpl_onepass (orF f1 f2) = f1 /\ f2 = valF false) \/
  (fsimpl_onepass (orF f1 f2) = f2 /\ f1 = valF false) \/
  (fsimpl_onepass (orF f1 f2) = orF f1 f2 /\ forall b, f1 <> valF b /\ f2 <> valF b).
 Proof with try tauto.
  intros. simpl.
  case_eq (check_bval f1);intros.
  apply check_bval_bT in H. rewrite H.
  icase b.
  apply check_bval_fT2 in H.
  destruct H. rewrite H.
  case_eq (check_bval f2);intros...
  apply check_bval_bT in H1. rewrite H1.
  icase b0.
  apply check_bval_fT2 in H1.
  destruct H1. rewrite H1.
  repeat right. split;repeat intro;split;repeat intro;subst;
  spec H0 b1;spec H2 b1...
 Qed. 

 Lemma fsimpl_onepass_implF: forall f1 f2,
  (fsimpl_onepass (implF f1 f2) = valF true /\ (f1 = valF false \/ f2 = valF true)) \/
  (fsimpl_onepass (implF f1 f2) = f2 /\ f1 = valF true) \/
  (fsimpl_onepass (implF f1 f2) = negF f1 /\ f2 = valF false) \/
  (fsimpl_onepass (implF f1 f2) = implF f1 f2 /\ forall b, f1 <> valF b /\ f2 <> valF b).
 Proof with try tauto.
  intros. simpl.
  case_eq (check_bval f1);intros.
  apply check_bval_bT in H. rewrite H.
  icase b.
  apply check_bval_fT2 in H.
  destruct H. rewrite H.
  case_eq (check_bval f2);intros...
  apply check_bval_bT in H1. rewrite H1.
  icase b0.
  apply check_bval_fT2 in H1.
  destruct H1. rewrite H1.
  repeat right. split;repeat intro;split;repeat intro;subst;
  spec H0 b1;spec H2 b1...
 Qed.

 Lemma fsimpl_onepass_negF: forall f,
  (exists b, fsimpl_onepass (negF f) = valF (negb b) /\ f = valF b) \/
  (fsimpl_onepass (negF f) = negF f /\ forall b, f <> valF b).
 Proof with try tauto.
  intros. simpl.
  case_eq (check_bval f);intros.
  apply check_bval_bT in H;rewrite H.
  left;exists b...
  right... split...
  apply check_bval_fT2 in H...
 Qed. 

 Lemma fsimpl_onepass_exF: forall f v,
  (exists b, fsimpl_onepass (exF v f) = valF b /\ f = valF b)\/
  (fsimpl_onepass (exF v f) = exF v f /\ forall b, f <> valF b).
 Proof with try tauto.
  intros. simpl.
  case_eq (check_bval f);intros.
  apply check_bval_bT in H;rewrite H.
  left;exists b...
  right... split...
  apply check_bval_fT2 in H...
 Qed.

 Lemma fsimpl_onepass_allF: forall f v,
  (exists b, fsimpl_onepass (allF v f) = valF b /\ f = valF b)\/
  (fsimpl_onepass (allF v f) = allF v f /\ forall b, f <> valF b).
 Proof with try tauto.
  intros. simpl.
  case_eq (check_bval f);intros.
  apply check_bval_bT in H;rewrite H.
  left;exists b...
  right... split...
  apply check_bval_fT2 in H...
 Qed.

 Opaque fsimpl_onepass.

 Lemma fsimpl_onepass_beval: forall f rho,
  beval rho f = beval rho (fsimpl_onepass f).
 Proof with try tauto.
  intros.
  icase f;simpl.

  - generalize (fsimpl_onepass_andF f1 f2);intros.
    firstorder;try subst f1; try subst f2;try rewrite H;simpl;
    try rewrite andb_false_r;
    try rewrite andb_true_r...

  - generalize (fsimpl_onepass_orF f1 f2);intros.
    firstorder;try subst f1; try subst f2;try rewrite H;simpl;
    try rewrite orb_true_r;
    try rewrite orb_false_r...

  - generalize (fsimpl_onepass_implF f1 f2);intros.
    firstorder;try subst f1; try subst f2;try rewrite H;simpl...
    icase (beval rho f1).

  - generalize (fsimpl_onepass_negF f);intros.
    firstorder;subst;try rewrite H...

  - generalize (fsimpl_onepass_exF f v);intros.
    firstorder;subst;try rewrite H...
    compute. icase x.

  - generalize (fsimpl_onepass_allF f v);intros.
    firstorder;subst;try rewrite H...
    compute. icase x.
  Qed.

 Transparent fsimpl_onepass.

 Lemma fsimpl_onepass_bsize: forall f,
  bsize (fsimpl_onepass f) <= bsize f.
 Proof with try tauto;try omega.
  intros. icase f;simpl.
  - icase ( check_bval f1);icase (check_bval f2);
    try icase b;try icase b0;simpl...
  - icase ( check_bval f1);icase (check_bval f2);
    try icase b;try icase b0;simpl...
  - icase ( check_bval f1);icase (check_bval f2);
    try icase b;try icase b0;simpl...
  - icase (check_bval f);try icase b;simpl...
  - icase (check_bval f);try icase b;simpl...
  - icase (check_bval f);try icase b;simpl...
 Qed.

 Opaque fsimpl_onepass.

 Fixpoint fsimpl (f : bF) :=
  match f with
  |valF b => valF b
  |varF v => varF v
  |andF f1 f2 => fsimpl_onepass (andF (fsimpl f1) (fsimpl f2))
  |orF f1 f2 => fsimpl_onepass (orF (fsimpl f1) (fsimpl f2))
  |implF f1 f2 => fsimpl_onepass (implF (fsimpl f1) (fsimpl f2))
  |negF f' => fsimpl_onepass (negF (fsimpl f'))
  |exF v f' => fsimpl_onepass (exF v (fsimpl f'))
  |allF v f' => fsimpl_onepass (allF v (fsimpl f'))
  end.

 Lemma fsimpl_beval: forall f rho,
  beval rho f = beval rho (fsimpl f).
 Proof with try tauto.
  induction f;intros;simpl;
  try rewrite<- fsimpl_onepass_beval;
  try rewrite IHf1,IHf2;
  try repeat rewrite IHf...
 Qed.

 Lemma fsimpl_bsize: forall f,
  bsize (fsimpl f) <= bsize f.
 Proof with try tauto;try omega.
   induction f;intros;simpl;
   try rewrite fsimpl_onepass_bsize;simpl...
 Qed.

 Definition quan_elim_exF (v : var) (f : bF) :=
  fsimpl_onepass (orF (fsimpl (bsubst f v true)) (fsimpl (bsubst f v false))).

 Lemma quan_elim_exF_beval: forall f v rho,
  beval rho (exF v f) = beval rho (quan_elim_exF v f).
 Proof with try tauto.
  intros.
  unfold quan_elim_exF. simpl.
  repeat rewrite<- beval_bsubst.
  f_equal;
  rewrite<- fsimpl_onepass_beval;simpl;
  repeat rewrite<-fsimpl_beval...
 Qed.

 Definition quan_elim_allF (v : var) (f : bF) :=
  fsimpl_onepass (andF (fsimpl (bsubst f v true)) (fsimpl (bsubst f v false))).

 Lemma quan_elim_allF_beval: forall f v rho,
  beval rho (allF v f) = beval rho (quan_elim_allF v f).
 Proof with try tauto.
  intros.
  unfold quan_elim_allF. simpl.
  repeat rewrite<- beval_bsubst.
  f_equal;
  rewrite<- fsimpl_onepass_beval;simpl;
  repeat rewrite<-fsimpl_beval...
 Qed.

 Fixpoint quan_elim (f : bF): bF :=
  match f with
  |valF b => valF b
  |varF v => varF v
  |andF f1 f2 => fsimpl_onepass (andF (quan_elim f1) (quan_elim f2))               
  |orF f1 f2 => fsimpl_onepass (orF (quan_elim f1) (quan_elim f2))
  |implF f1 f2 => fsimpl_onepass (implF (quan_elim f1) (quan_elim f2)) 
  |negF f' => fsimpl_onepass (negF (quan_elim f'))
  |exF v f'  => quan_elim_exF v (quan_elim f')
  |allF v f' => quan_elim_allF v (quan_elim f')
  end.

  Lemma quan_elim_beval: forall bf rho,
   beval rho (quan_elim bf) = beval rho bf.
  Proof with try tauto.
   induction bf;intros;simpl;
   try rewrite<- fsimpl_onepass_beval;simpl...
   f_equal;try apply IHbf1;try apply IHbf2.
   f_equal;try apply IHbf1;try apply IHbf2.
   f_equal;try apply IHbf1;try apply IHbf2.
   f_equal;apply IHbf.
   rewrite <- quan_elim_exF_beval. simpl.
   f_equal;apply IHbf.
   rewrite <- quan_elim_allF_beval. simpl.
   f_equal;apply IHbf.
  Qed.

 Definition var_free {A} `{varsable A var}:= fun (a : A) => vars a = nil.

 Definition var_free_spec (A : Type) {B} `{varsable A var} `{evalable B A} := 
  forall a, var_free a -> (valid a \/ unsat a).
 
 Class var_free_prop (A : Type) {B} `{varsable A var} `{evalable B A} := Var_free_prop {
   var_free_case: var_free_spec A
 }.

 Instance bf_var_free: var_free_prop bF.
 Proof with try tauto.
  constructor.
  induction a;intros H; unfold var_free in *;simpl in *;
  rewrite bF_unsat_rewrite,bF_valid_rewrite in *.
  icase b. left. repeat intro...
  inv H. 
  
  apply app_eq_nil in H.
  destruct H. spec IHa1 H. spec IHa2 H0.
  icase IHa1;icase IHa2.
  left. repeat intro;simpl.
  spec H1 rho. spec H2 rho.
  rewrite H1,H2...
  right. repeat intro;simpl.
  spec H1 rho. spec H2 rho.
  rewrite H1,H2...
  right. repeat intro;simpl.
  spec H1 rho. spec H2 rho.
  rewrite H1,H2...
  right. repeat intro;simpl.
  spec H1 rho. spec H2 rho.
  rewrite H1,H2...

  apply app_eq_nil in H.
  destruct H. spec IHa1 H. spec IHa2 H0.
  icase IHa1;icase IHa2.
  left. repeat intro;simpl.
  spec H1 rho. spec H2 rho.
  rewrite H1,H2...
  left. repeat intro;simpl.
  spec H1 rho. spec H2 rho.
  rewrite H1,H2...
  left. repeat intro;simpl.
  spec H1 rho. spec H2 rho.
  rewrite H1,H2...
  right. repeat intro;simpl.
  spec H1 rho. spec H2 rho.
  rewrite H1,H2...

  apply app_eq_nil in H.
  destruct H. spec IHa1 H. spec IHa2 H0.
  icase IHa1;icase IHa2.
  left. repeat intro;simpl.
  spec H1 rho. spec H2 rho.
  rewrite H1,H2...
  right. repeat intro;simpl.
  spec H1 rho. spec H2 rho.
  rewrite H1,H2...
  left. repeat intro;simpl.
  spec H1 rho. spec H2 rho.
  rewrite H1,H2...
  left. repeat intro;simpl.
  spec H1 rho. spec H2 rho.
  rewrite H1,H2...

  spec IHa H.
  destruct IHa;[right|left];
  repeat intro;simpl; spec H0 rho;
  rewrite H0...
  inv H. inv H.
 Qed.

 Transparent fsimpl_onepass.

 Lemma fsimpl_reduce: forall f,
  fsimpl (fsimpl f) = fsimpl f.
 Proof with try tauto.
  induction f;simpl...
  - case_eq (check_bval (fsimpl f1));intros.
    apply check_bval_bT in H. rewrite H in *.
    icase b.
    case_eq (check_bval (fsimpl f2));intros.
    apply check_bval_bT in H0. rewrite H0 in *.
    icase b0.
    simpl. rewrite IHf1,IHf2,H,H0...
  - case_eq (check_bval (fsimpl f1));intros.
    apply check_bval_bT in H. rewrite H in *.
    icase b.
    case_eq (check_bval (fsimpl f2));intros.
    apply check_bval_bT in H0. rewrite H0 in *.
    icase b0.
    simpl. rewrite IHf1,IHf2,H,H0...
  - case_eq (check_bval (fsimpl f1));intros.
    apply check_bval_bT in H. rewrite H in *.
    icase b.
    case_eq (check_bval (fsimpl f2));intros.
    apply check_bval_bT in H0. rewrite H0 in *.
    icase b0;simpl. rewrite IHf1,H...
    simpl. rewrite IHf1,IHf2,H,H0...
  - case_eq (check_bval (fsimpl f));intros...
    simpl. rewrite IHf,H...
  - case_eq (check_bval (fsimpl f));intros...
    simpl. rewrite IHf,H...
  - case_eq (check_bval (fsimpl f));intros...
    simpl. rewrite IHf,H...
 Qed.

 Lemma fsimpl_bsubst_reduce: forall f v b,
  fsimpl (bsubst (fsimpl f) v b) = fsimpl (bsubst f v b).
 Proof with try tauto.
  induction f;intros;simpl...
  - case_eq (check_bval (fsimpl f1));intros;simpl.
    apply check_bval_bT in H.
    rewrite H in IHf1.
    rewrite <- IHf1. simpl.
    icase b0...
    case_eq (check_bval (fsimpl f2));intros;simpl.
    apply check_bval_bT in H0.
    rewrite H0 in IHf2.
    rewrite <- IHf2. simpl.
    icase b1...
    rewrite IHf1.
    case_eq (check_bval (fsimpl (bsubst f1 v b)));intros...
    apply check_bval_bT in H1. rewrite H1. icase b1...
    case_eq (check_bval (fsimpl (bsubst f1 v b)));intros;simpl...
    icase b1...
    rewrite IHf1,IHf2...
  - case_eq (check_bval (fsimpl f1));intros;simpl.
    apply check_bval_bT in H.
    rewrite H in IHf1.
    rewrite <- IHf1. simpl.
    icase b0...
    case_eq (check_bval (fsimpl f2));intros;simpl.
    apply check_bval_bT in H0.
    rewrite H0 in IHf2.
    rewrite <- IHf2. simpl.
    icase b1...
    case_eq (check_bval (fsimpl (bsubst f1 v b)));intros... icase b1.
    rewrite IHf1.
    case_eq (check_bval (fsimpl (bsubst f1 v b)));intros...
    apply check_bval_bT in H1. rewrite H1. icase b1...
    rewrite IHf1,IHf2...
  - case_eq (check_bval (fsimpl f1));intros;simpl.
    apply check_bval_bT in H.
    rewrite H in IHf1.
    rewrite <- IHf1. simpl.
    icase b0...
    case_eq (check_bval (fsimpl f2));intros;simpl.
    apply check_bval_bT in H0.
    rewrite H0 in IHf2.
    rewrite <- IHf2. simpl.
    icase b1...
    case_eq (check_bval (fsimpl (bsubst f1 v b)));intros... icase b1.
    simpl. rewrite IHf1.
    case_eq (check_bval (fsimpl (bsubst f1 v b)));intros... icase b1.
    rewrite IHf1,IHf2...
  - case_eq (check_bval (fsimpl f));intros;simpl.
    apply check_bval_bT in H. rewrite H in IHf.
    simpl in IHf. rewrite<- IHf. simpl...
    rewrite IHf...
  - destruct (eq_dec v0 v);subst;simpl.
    case_eq (check_bval (fsimpl f));intros;simpl...
    destruct (eq_dec v v);subst;simpl...
    rewrite fsimpl_reduce,H...
    case_eq (check_bval (fsimpl f));intros;simpl.
    apply check_bval_bT in H. rewrite H in *.
    rewrite<- IHf with (v:=v0)(b:=b);simpl...
    destruct (eq_dec v0 v);subst...
    simpl. rewrite IHf...
  - destruct (eq_dec v0 v);subst;simpl.
    case_eq (check_bval (fsimpl f));intros;simpl...
    destruct (eq_dec v v);subst;simpl...
    rewrite fsimpl_reduce,H...
    case_eq (check_bval (fsimpl f));intros;simpl.
    apply check_bval_bT in H. rewrite H in *.
    rewrite<- IHf with (v:=v0)(b:=b);simpl...
    destruct (eq_dec v0 v);subst...
    simpl. rewrite IHf...
 Qed.

 Lemma quan_elim_bsubst: forall f v b,
  quan_elim (bsubst f v b) = fsimpl (bsubst (quan_elim f) v b).
 Proof with try tauto.
  intro f. remember (bsize f) as n.
  assert (bsize f <= n) by omega. clear Heqn.
  revert H. revert f.
  induction n;intros;simpl in *... inv H. icase f...
  icase f;simpl.
  - destruct (eq_dec v v0);subst...
  - assert (bsize f1 <= n /\ bsize f2 <= n) by (simpl in H;omega).
    repeat rewrite IHn...
    case_eq (check_bval (quan_elim f1));intros...
    rewrite check_bval_bT in H1. rewrite H1. icase b0.
    case_eq (check_bval (quan_elim f2));intros...
    rewrite check_bval_bT in H2. rewrite H2. simpl. icase b1.
    case_eq (check_bval (fsimpl (bsubst (quan_elim f1) v b)));intros...
    apply check_bval_bT in H3;rewrite H3. icase b1.
    case_eq (check_bval (fsimpl (bsubst (quan_elim f1) v b)));intros...
    icase b1.
  - assert (bsize f1 <= n /\ bsize f2 <= n) by (simpl in H;omega).
    repeat rewrite IHn...
    case_eq (check_bval (quan_elim f1));intros...
    rewrite check_bval_bT in H1. rewrite H1. icase b0.
    case_eq (check_bval (quan_elim f2));intros...
    rewrite check_bval_bT in H2. rewrite H2. simpl. icase b1.
    case_eq (check_bval (fsimpl (bsubst (quan_elim f1) v b)));intros...
    icase b1.
    case_eq (check_bval (fsimpl (bsubst (quan_elim f1) v b)));intros...
    apply check_bval_bT in H3;rewrite H3. icase b1.
  - assert (bsize f1 <= n /\ bsize f2 <= n) by (simpl in H;omega).
    repeat rewrite IHn...
    case_eq (check_bval (quan_elim f1));intros...
    rewrite check_bval_bT in H1. rewrite H1. icase b0.
    case_eq (check_bval (quan_elim f2));intros...
    rewrite check_bval_bT in H2. rewrite H2. simpl. icase b1.
    case_eq (check_bval (fsimpl (bsubst (quan_elim f1) v b)));intros...
    icase b1. simpl.
    case_eq (check_bval (fsimpl (bsubst (quan_elim f1) v b)));intros...
    icase b1.
  - simpl in H;rewrite IHn;try omega.
    case_eq (check_bval (quan_elim f));intros...
    apply check_bval_bT in H0;rewrite H0;simpl...
  - simpl in H.
    assert (bsize f <= n) by omega.
    assert (bsize (bsubst f v true) <= n /\ bsize (bsubst f v false) <= n).
     split;rewrite bsize_bsubst...
    destruct (eq_dec v v0);subst;simpl... 
    + unfold quan_elim_exF.
      repeat rewrite<- IHn...
      simpl.
      case_eq (check_bval (quan_elim (bsubst f v0 true)));intros.
      icase b0. rewrite <- IHn...
      rewrite bsubst_reduce...
      case_eq (check_bval (quan_elim (bsubst f v0 false)));intros.
      icase b1. rewrite <- IHn...
      rewrite bsubst_reduce...
      simpl. repeat rewrite <-IHn...
      repeat rewrite bsubst_reduce.
      rewrite H2,H3...
    + unfold quan_elim_exF.
      repeat rewrite<- IHn;try rewrite bsize_bsubst...
      simpl.
      case_eq (check_bval (quan_elim (bsubst f v0 true)));intros.
      apply check_bval_bT in H2.
      rewrite bsubst_comm...
      rewrite IHn;try rewrite bsize_bsubst...
      rewrite H2. simpl.
      icase b0... repeat rewrite IHn;try rewrite bsize_bsubst...
      repeat rewrite fsimpl_bsubst_reduce.
      rewrite bsubst_comm...
      case_eq (check_bval (quan_elim (bsubst f v0 false)));intros.
      apply check_bval_bT in H3.
      generalize (bsubst_comm v v0 b false f n0);intro.
      repeat rewrite H4.
      assert (bsize (bsubst f v0 false) <= n) by (rewrite bsize_bsubst;omega).
      generalize (IHn _ H5 v b);intro.
      rewrite H3 in H6.
      repeat rewrite H6. simpl.
      icase b1. 
      case_eq (check_bval (quan_elim (bsubst (bsubst f v b) v0 true)));intros...
      icase b1. rewrite <-IHn;try rewrite bsize_bsubst...
      rewrite bsubst_comm...
      case_eq (check_bval (quan_elim (bsubst (bsubst f v0 true) v b)));intros...
      apply check_bval_bT in H7;rewrite H7. icase b1.
      repeat rewrite IHn;try rewrite bsize_bsubst...
      simpl.
      repeat rewrite fsimpl_bsubst_reduce.
      assert (forall f' v' b1 b2, v <> v' -> bsubst (bsubst f' v b1) v' b2 = bsubst (bsubst f' v' b2) v b1).
        intros;apply bsubst_comm...
      repeat rewrite H4...
  - simpl in H.
    assert (bsize f <= n) by omega.
    assert (bsize (bsubst f v true) <= n /\ bsize (bsubst f v false) <= n).
     split;rewrite bsize_bsubst...
    destruct (eq_dec v v0);subst;simpl... 
    + unfold quan_elim_allF.
      repeat rewrite<- IHn...
      simpl.
      case_eq (check_bval (quan_elim (bsubst f v0 true)));intros.
      icase b0. rewrite <- IHn...
      rewrite bsubst_reduce...
      case_eq (check_bval (quan_elim (bsubst f v0 false)));intros.
      icase b1. rewrite <- IHn...
      rewrite bsubst_reduce...
      simpl. repeat rewrite <-IHn...
      repeat rewrite bsubst_reduce.
      rewrite H2,H3...
    + unfold quan_elim_allF.
      repeat rewrite<- IHn;try rewrite bsize_bsubst...
      simpl.
      case_eq (check_bval (quan_elim (bsubst f v0 true)));intros.
      apply check_bval_bT in H2.
      rewrite bsubst_comm...
      rewrite IHn;try rewrite bsize_bsubst...
      rewrite H2. simpl.
      icase b0... repeat rewrite IHn;try rewrite bsize_bsubst...
      repeat rewrite fsimpl_bsubst_reduce.
      rewrite bsubst_comm...
      case_eq (check_bval (quan_elim (bsubst f v0 false)));intros.
      apply check_bval_bT in H3.
      generalize (bsubst_comm v v0 b false f n0);intro.
      repeat rewrite H4.
      assert (bsize (bsubst f v0 false) <= n) by (rewrite bsize_bsubst;omega).
      generalize (IHn _ H5 v b);intro.
      rewrite H3 in H6.
      repeat rewrite H6. simpl.
      rewrite bsubst_comm...
      icase b1;try rewrite <- IHn;try rewrite bsize_bsubst...
      case_eq (check_bval (quan_elim (bsubst (bsubst f v0 true) v b)));intros...
      apply check_bval_bT in H7. icase b1...
      simpl.
      case_eq (check_bval (quan_elim (bsubst (bsubst f v0 true) v b)));intros...
      icase b1...
      repeat rewrite IHn;try rewrite bsize_bsubst...
      simpl.
      repeat rewrite fsimpl_bsubst_reduce.
      assert (forall f' v' b1 b2, v <> v' -> bsubst (bsubst f' v b1) v' b2 = bsubst (bsubst f' v' b2) v b1).
        intros;apply bsubst_comm...
      repeat rewrite H4...
  Qed.

 Lemma quan_elim_full_quan: forall f,
  full_quan f ->
  exists b, quan_elim f = valF b.
 Proof with try tauto.
  intro. remember (bsize f) as n. symmetry in Heqn.
  assert (bsize f <= n) by omega.
  clear Heqn. revert H. revert f. induction n;intros.
  inv H;icase f.
  icase f;simpl...
  exists b...
  spec H0 v. spec H0;simpl...
  simpl in H0. destruct (eq_dec v v);subst...

  simpl in H.
  assert (bsize f1 <= n /\ bsize f2 <= n) by omega.
  destruct H1.
  assert (full_quan f1 /\ full_quan f2).
   split;intros v H3;spec H0 v;simpl in H0;detach H0;
   try rewrite in_app_iff...
  destruct H3.
  generalize (IHn f1 H1 H3);intro.
  generalize (IHn f2 H2 H4);intro.
  destruct H5 as [b1 H5]. destruct H6 as [b2 H6].
  rewrite H5,H6. simpl. icase b1. exists b2... exists false...

  simpl in H.
  assert (bsize f1 <= n /\ bsize f2 <= n) by omega.
  destruct H1.
  assert (full_quan f1 /\ full_quan f2).
   split;intros v H3;spec H0 v;simpl in H0;detach H0;
   try rewrite in_app_iff...
  destruct H3.
  generalize (IHn f1 H1 H3);intro.
  generalize (IHn f2 H2 H4);intro.
  destruct H5 as [b1 H5]. destruct H6 as [b2 H6].
  rewrite H5,H6. simpl. icase b1. exists true... exists b2...

  simpl in H.
  assert (bsize f1 <= n /\ bsize f2 <= n) by omega.
  destruct H1.
  assert (full_quan f1 /\ full_quan f2).
   split;intros v H3;spec H0 v;simpl in H0;detach H0;
   try rewrite in_app_iff...
  destruct H3.
  generalize (IHn f1 H1 H3);intro.
  generalize (IHn f2 H2 H4);intro.
  destruct H5 as [b1 H5]. destruct H6 as [b2 H6].
  rewrite H5,H6. simpl. icase b1. exists b2... exists true...

  simpl in H.
  assert (bsize f <= n) by omega.
  assert (full_quan f).
   intros v H2. spec H0 v. spec H0...
  spec IHn f H1 H2. destruct IHn as [b IHn].
  rewrite IHn. simpl. exists (negb b)...
  
  simpl in H.
  assert (bsize f <= n) by omega.
  assert (bsize (bsubst f v true) <= n /\ bsize (bsubst f v false) <= n).
   split;rewrite bsize_bsubst...
  destruct H2.
  assert (full_quan (bsubst f v true) /\ full_quan (bsubst f v false)).
   split;intros v' H4;
   spec H0 v';detach H0...
   simpl in H0. destruct (eq_dec v' v);subst.
   apply bsubst_not_free_id. apply bsubst_not_free_diff...
   apply bsubst_sublist in H4... right...
   simpl in H0. destruct (eq_dec v' v);subst.
   apply bsubst_not_free_id. apply bsubst_not_free_diff...
   apply bsubst_sublist in H4... right...
  destruct H4.
  generalize (IHn _ H2 H4);intro.
  generalize (IHn _ H3 H5);intro.
  destruct H6 as [b1 H6]. destruct H7 as [b2 H7].
  unfold quan_elim_exF.
  repeat rewrite<- quan_elim_bsubst.
  rewrite H7,H6. simpl. icase b1... exists true... exists b2...

  simpl in H.
  assert (bsize f <= n) by omega.
  assert (bsize (bsubst f v true) <= n /\ bsize (bsubst f v false) <= n).
   split;rewrite bsize_bsubst...
  destruct H2.
  assert (full_quan (bsubst f v true) /\ full_quan (bsubst f v false)).
   split;intros v' H4;
   spec H0 v';detach H0...
   simpl in H0. destruct (eq_dec v' v);subst.
   apply bsubst_not_free_id. apply bsubst_not_free_diff...
   apply bsubst_sublist in H4... right...
   simpl in H0. destruct (eq_dec v' v);subst.
   apply bsubst_not_free_id. apply bsubst_not_free_diff...
   apply bsubst_sublist in H4... right...
  destruct H4.
  generalize (IHn _ H2 H4);intro.
  generalize (IHn _ H3 H5);intro.
  destruct H6 as [b1 H6]. destruct H7 as [b2 H7].
  unfold quan_elim_allF.
  repeat rewrite<- quan_elim_bsubst.
  rewrite H7,H6. simpl. icase b1... exists b2... exists false...
 Qed. 

 Definition bsolver (f : bF) := 
 match check_bval (quan_elim (fsimpl f)) with
 |bT b => Some b 
 |_ => None
 end.

 Lemma fsimpl_onepass_vars: forall f,
  sublist (vars (fsimpl_onepass f)) (vars f).
 Proof with try tauto.
  intros f v.
  icase f;simpl in *;
  try case_eq (check_bval f1);
  try case_eq (check_bval f2);
  try case_eq (check_bval f);
  intros;
  try icase b0; try icase b; 
  simpl in *; try rewrite in_app_iff in *...
 Qed.

 Lemma fsimpl_onepass_not_free: forall f v,
  not_free v f -> not_free v (fsimpl_onepass f).
 Proof with try tauto.
  intros.
  icase f;simpl in *;
  try case_eq (check_bval f1);
  try case_eq (check_bval f2);
  try case_eq (check_bval f);
  simpl;intros;
  try icase b0;try icase b;simpl...
 Qed.

 Opaque fsimpl_onepass.

 Lemma fsimpl_vars: forall f,
  sublist (vars (fsimpl f)) (vars f).
 Proof with try tauto.
  induction f;simpl;repeat intro...
  apply fsimpl_onepass_vars in H;simpl in *.
  repeat rewrite in_app_iff in *. spec IHf1 e;spec IHf2 e...
  apply fsimpl_onepass_vars in H;simpl in *.
  repeat rewrite in_app_iff in *. spec IHf1 e;spec IHf2 e...
  apply fsimpl_onepass_vars in H;simpl in *.
  repeat rewrite in_app_iff in *. spec IHf1 e;spec IHf2 e...
  apply fsimpl_onepass_vars in H;simpl in *. spec IHf e...  
  apply fsimpl_onepass_vars in H;simpl in *. spec IHf e...
  apply fsimpl_onepass_vars in H;simpl in *. spec IHf e...
 Qed.

 Lemma fsimpl_not_free: forall f v,
  not_free v f -> not_free v (fsimpl f).
 Proof with try tauto.
  induction f;simpl;repeat intro;
  try apply fsimpl_onepass_not_free;simpl;
  try spec IHf1 v;try spec IHf2 v; try generalize (IHf v);intros...
  destruct (eq_dec v0 v);subst...
  apply IHf...
  destruct (eq_dec v0 v);subst...
  apply IHf...
 Qed.
 
 Lemma fsimpl_full_quan_preserve: forall f,
  full_quan f -> full_quan (fsimpl f).
 Proof with try tauto.
  intros. unfold full_quan in *.
  intros.
  apply fsimpl_not_free.
  apply H. apply fsimpl_vars...
 Qed.

 Lemma bsolver_Some: forall f,
  full_quan f ->
  exists b, bsolver f = Some b.
 Proof with try tauto.
  intros. apply fsimpl_full_quan_preserve in H.
  unfold bsolver.
  case_eq (check_bval (quan_elim (fsimpl f)));intros.
  exists b...
  apply quan_elim_full_quan in H.
  destruct H as [b1 H]. rewrite H in H0.
  inv H0. 
 Qed.

 Lemma bsolver_valid: forall f,
  full_quan f ->
  (bsolver f = Some true <-> valid f).
 Proof with try tauto.
  intros. apply fsimpl_full_quan_preserve in H.
  unfold bsolver.
  generalize (quan_elim_full_quan _ H);intro.
  destruct H0 as [b H0]. rewrite H0. simpl.
  split;intros. inv H1. repeat intro.
  generalize (quan_elim_beval (fsimpl f) a);intro.
  rewrite H0 in H1. rewrite<- fsimpl_beval in H1.
  simpl in *. rewrite H1...
  spec H1 (fun (v : var) => false).
  simpl in H1.
  rewrite fsimpl_beval in H1.
  rewrite <- quan_elim_beval in H1.
  rewrite H0 in H1. simpl in H1.
  subst...
 Qed. 
  
 Lemma bsolver_unsat: forall f,
  full_quan f ->
  (bsolver f = Some false <-> unsat f).
 Proof with try tauto.
  intros. apply fsimpl_full_quan_preserve in H.
  rewrite bF_unsat_rewrite.
  unfold bsolver.
  generalize (quan_elim_full_quan _ H);intro.
  destruct H0 as [b H0]. rewrite H0. simpl.
  split;intros. inv H1. repeat intro.
  generalize (quan_elim_beval (fsimpl f) rho);intro.
  rewrite H0 in H1. rewrite<- fsimpl_beval in H1.
  simpl in *. rewrite H1...
  spec H1 (fun (v : var) => false).
  simpl in H1.
  rewrite fsimpl_beval in H1.
  rewrite <- quan_elim_beval in H1.
  rewrite H0 in H1. simpl in H1.
  subst...
 Qed.

End BF_solver.

(*
 Module es := Equation_system sv_nat.
 Module bv := Bool_formula sv_nat.
 Module test := BF_solver sv_nat bv.
 Import bv test.

 Definition eqF := fun f1 f2 => orF (andF f1 f2) (andF (negF f1) (negF f2)).

 Fixpoint lF (l1 l2 : list nat) :=
 match (l1,l2) with
 |(nil,nil) => valF true
 |(v1::l1',v2::l2') => andF (eqF (varF v1) (varF v2)) (lF l1' l2')
 |_ => valF false
 end.

 Fixpoint exl (l : list nat) f:=
 match l with
 | nil => f
 |v::l' => exF v (exl l' f)
 end.

 Fixpoint axl (l : list nat) f:=
 match l with
 | nil => f
 |v::l' => allF v (axl l' f)
 end.

 Definition l1 := 1::2::3::4::5::6::7::8::9::10::nil.
 Definition l2 := 11::12::13::14::15::16::17::18::19::20::nil.
 Definition f2 := lF l1 l2.
 Definition f3 := axl l1 (exl l2 f2).
 Eval compute in f3.
 Time Eval compute in (quan_elim f3).

 Definition f1 := exF 1 (allF 2 (orF (varF 1) (varF 2))).

 Time Eval compute in (quan_elim f1).
*) 
