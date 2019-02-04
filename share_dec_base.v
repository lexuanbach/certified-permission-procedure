Require Import msl.msl_standard.
Require Import NPeano.
Require Import borders.
Require Import Max.
Require Import Min.

(* Canonical Structure ord_nat. *)

(* move to MSL *)

Lemma upd_eq' {A} {B} `{EqDec A} : forall (f : A -> B) x x',
  upd f x (f x') x' = f x'.
Proof.
  intros. unfold upd. case (eq_dec x x'); auto.
Qed.

Lemma upd_absorb {A} {B} `{EqDec A}: forall (ctx : A -> B) x v v',
  upd (upd ctx x v) x v' = upd ctx x v'.
Proof.
  intros. extensionality q. unfold upd.
  case eq_dec; auto.
Qed.

Lemma upd_swap {A} {B} `{EqDec A} : forall (f : A -> B) x y v1 v2,
  x <> y ->
  upd (upd f x v1) y v2 = upd (upd f y v2) x v1.
Proof.
  intros. extensionality q.
  unfold upd.
  case eq_dec; case eq_dec; auto.
  intros. subst. destruct H0; auto.
Qed.

Definition override {A} {B} `{EqDec A} (ctx ctx' : A -> B) (evars : list A) : A -> B :=
  fold_right (fun e rho => upd rho e (ctx' e)) ctx evars.
Notation " [ E '=>' ctx2 ']' ctx1 " := (override ctx1 ctx2 E) (at level 10).

Lemma override_in {A} {B} `{EqDec A}: forall (ctx ctx' : A -> B) E x,
  In x E ->
  ([E => ctx'] ctx) x = ctx' x.
Proof.
  induction E; simpl; intros. contr.  
  destruct H0. subst x. rewrite upd_eq; auto.
  case (eq_dec a x); intro. subst x. rewrite upd_eq. trivial.
  rewrite upd_neq; auto.
Qed.

Lemma override_not_in {A} {B} `{EqDec A}: forall (ctx ctx' : A -> B) E x,
  ~In x E ->
  ([E => ctx'] ctx) x = ctx x.
Proof.
  induction E; simpl; intros; auto.
  assert (a <> x /\ ~In x E) by tauto. clear H0. destruct H1.
  rewrite upd_neq; auto.
Qed.

Lemma override_absorb_in {A} {B} `{EqDec A}: forall (ctx ctx' : A -> B) E x v,
  In x E ->
  [E => ctx'] (upd ctx x v) = [E => ctx'] ctx.
Proof.
  intros. extensionality q.
  case (in_dec eq_dec q E); intro.
  do 2 (rewrite override_in; auto).
  do 2 (rewrite override_not_in; auto).
  rewrite upd_neq; auto.
  intro. subst. contr.
Qed.

Lemma override_absorb_not_in {A} {B} `{EqDec A}: forall (ctx ctx' : A -> B) E x v,
  ~In x E ->
  [E => ctx'] (upd ctx x v) = upd ([E => ctx'] ctx) x v.
Proof.
  induction E; simpl. auto.
  intros. assert (a <> x /\ ~In x E) by tauto. clear H0. destruct H1.
  rewrite upd_swap; auto.
  f_equal.
  apply IHE.
  trivial.
Qed.

Lemma override_within_in {A} {B} `{EqDec A}: forall (ctx ctx' : A -> B) E x v,
  In x E ->
  [E => (upd ctx' x v)] ctx = upd ([E => ctx'] ctx) x v.
Proof.
  intros. extensionality q.
  case (in_dec eq_dec q E); intro.
  rewrite override_in; auto.
  case (eq_dec x q); intro. subst.
  repeat (rewrite upd_eq); auto.
  do 2 (rewrite upd_neq; auto).
  rewrite override_in; auto.
  rewrite override_not_in; auto.
  rewrite upd_neq.
  rewrite override_not_in; auto.
  intro. subst. contr.
Qed.

Lemma override_within_not_in {A} {B} `{EqDec A}: forall (ctx ctx' : A -> B) E x v,
  ~In x E ->
  [E => (upd ctx' x v)] ctx = [E => ctx'] ctx.
Proof.
  intros. extensionality q.
  case (in_dec eq_dec q E); intro.
  do 2 (rewrite override_in; auto).
  rewrite upd_neq; auto.
  intro. subst. contr.
  do 2 (rewrite override_not_in; auto).
Qed.

Lemma context_override_idem {A} {B} `{EqDec A}: forall (ctx : A -> B) L,
  override ctx ctx L = ctx.
Proof.
  intros. extensionality a.
  case (in_dec eq_dec a L).
  apply override_in.
  apply override_not_in.
Qed.

Lemma override_first_last {A} {B} `{EqDec A}: forall (ctx ctx' : A -> B) E x,
  [E => ctx'] (upd ctx x (ctx' x)) =
  upd ([E => ctx'] ctx) x (ctx' x).
Proof.
  intros.
  case (in_dec eq_dec x E); intros.
  rewrite override_absorb_in; auto.
  extensionality q.
  case (in_dec eq_dec q E); intro.
  rewrite override_in; auto.
  case (eq_dec x q); intro.
  subst. rewrite upd_eq. trivial.
  rewrite upd_neq; auto.
  rewrite override_in; auto.
  rewrite override_not_in; auto.
  case (eq_dec x q); intro. subst x. contr.
  rewrite upd_neq; auto. rewrite override_not_in; auto.
  rewrite override_absorb_not_in; auto.
Qed.

Lemma f_apply: forall {A B : Type} (f : A -> B) (a b : A),
  a = b -> f a = f b.
Proof.
 intros;congruence.
Qed.

(* end move to MSL *)


(*
Set Implicit Arguments.
*)

Class getable (A : Type) (B : Type) (C : Type) : Type := Getable {
  get : A -> B -> C
}.
Implicit Arguments Getable [A B C].
Class evalable (A : Type) (B : Type) : Type := Evalable {
  eval : A -> B -> Prop
}.
Implicit Arguments Evalable [A B].
Notation " rho '|=' obj " := (eval rho obj) (at level 30).

Definition e_eval {A} {B} {C} `{EqDec A} `{evalable (A -> B) C} : (A -> B) -> (list A) -> C -> Prop :=
  fun rho E obj => exists rho', [E => rho'] rho |= obj.

Definition eval_list {A} {B} `{evalable A B} : A -> list B -> Prop := 
    fun a => fold_right (fun e t => t /\ a |= e) True.
Instance evalable_list {A} {B} `{evalable A B} : evalable A (list B):=
  Evalable eval_list.
Lemma eval_list_app {A} {B} `{evalable A B} : forall (a : A) (l1 l2 : list B),
    a |= (l1 ++ l2) <-> a |= l1 /\ a |= l2.
Proof.
  induction l1; intros; simpl in *. tauto.
  rewrite IHl1. tauto.
Qed.

Definition impl {A} {B} `{H : evalable A B} : relation B := fun b1 b2 =>
  forall a : A, eval a b1 -> eval a b2.
Notation " obj1 '|-' obj2 " := (impl obj1 obj2) (at level 20).

Lemma impl_refl {A} {B} `{evalable A B}: reflexive _ impl.  
Proof.
  unfold reflexive. intro b. compute; tauto.
Qed.
Lemma impl_trans {A} {B} `{evalable A B}: transitive _ impl.
Proof.
  unfold transitive. intros. intros ? ?. apply H1, H0, H2.
Qed.
Add Parametric Relation {A} {B} `{evalable A B} : B impl
  reflexivity proved by impl_refl
  transitivity proved by impl_trans
  as impl_rel.

Definition e_impl {A B C} `{EqDec A} `{evalable (A -> B) C} : (list A) -> C -> (list A) -> C -> Prop :=
  fun e1 c1 e2 c2 => forall rho, 
    (e_eval rho e1 c1) -> (e_eval rho e2 c2).

Definition equiv {A} {B} `{evalable A B} : relation B := fun b1 b2 =>
  impl b1 b2 /\ impl b2 b1.
Notation " obj1 '-|-' obj2 " := (equiv obj1 obj2) (at level 20).
Lemma equiv_refl {A} {B} `{evalable A B}: reflexive _ equiv.
Proof.
  split; reflexivity.
Qed.
Lemma equiv_sym {A} {B} `{evalable A B}: symmetric _ equiv.
Proof.
  compute; intros; tauto.
Qed.
Lemma equiv_trans {A} {B} `{evalable A B}: transitive _ equiv.
Proof.
  unfold transitive. intros. destruct H0, H1.
  split; transitivity y; trivial.
Qed.
Add Parametric Relation {A} {B} `{evalable A B} : B equiv
  reflexivity proved by equiv_refl
  symmetry proved by equiv_sym 
  transitivity proved by equiv_trans
  as equiv_rel.

Definition e_equiv {A} {B} {C} `{EqDec A} `{evalable (A -> B) C} : (list A) -> C -> (list A) -> C -> Prop :=
  fun e1 c1 e2 c2 => e_impl e1 c1 e2 c2 /\ e_impl e2 c2 e1 c1.

(*
Add Parametric Morphism {A} {B} `{evalable A B} (b1 b2 : B) :
    (impl b1 b2)
    with signature (impl ) -->
                   (impl A) ++>
                   impl
     as impl_morphism.
Proof.
  repeat intro.
  transitivity x; auto.
  transitivity x0; auto.
Qed.
*)

Definition cequiv {A} {B} `{evalable A B} : B -> A -> A -> Prop :=
    fun b a1 a2 => (a1 |= b) <-> (a2 |= b).
(*
Notation " obj 'views' rho1 'equivalentTo' rho2 " := (cequiv obj rho1 rho2) (at level 30).
*)

Lemma cequiv_refl {A} {B} `{evalable A B}: forall b, reflexive _ (cequiv b).
Proof. repeat intro. red. tauto. Qed.
Lemma cequiv_sym {A} {B} `{evalable A B}: forall b, symmetric _ (cequiv b).
Proof. firstorder. Qed.
Lemma cequiv_trans {A} {B} `{evalable A B}: forall b, transitive _ (cequiv b).
Proof. firstorder. Qed.
Add Parametric Relation {A} {B} `{evalable A B} (b : B) : A (cequiv b)
  reflexivity proved by (cequiv_refl b)
  symmetry proved by (cequiv_sym b) 
  transitivity proved by (cequiv_trans b)
  as cequiv_rel.

Class varsable (A B : Type) : Type := Varsable {
  vars : A -> list B
}.
Implicit Arguments Varsable [A B].
Definition vars_list {A} {B} `{varsable A B} : (list A) -> (list B) :=
  fold_right (fun a L' => (vars a) ++ L') nil.
Instance varsable_list {A} {B} `{varsable A B} : varsable (list A) B :=
  Varsable vars_list.
Definition IN {A} {B} `{varsable A B} : B -> A -> Prop :=
  fun b a => In b (vars a).
Definition fresh {A} {B} `{varsable A B} : B -> A -> Prop :=
  fun b a => ~ IN b a.
Lemma fresh_cons {A} {B} `{varsable A B} : forall b a aL,
  (fresh b (a :: aL)) <->
  (fresh b a /\ fresh b aL).
Proof.
  unfold fresh, IN. split; repeat intro.
  split; intro; apply H0; simpl; apply in_or_app; auto.
  apply H0. simpl in H1. apply in_app_or in H1. destruct H0.
  tauto.
Qed.

Class cheightable (A : Type) (B : Type) : Type := Cheightable {
  cheight : A -> B -> nat
}.
Implicit Arguments Cheightable [A B].
Existing Instance Cheightable.
Notation " | a | " := (height a) (at level 45).
Definition list_cheight {A B} `{cheightable A B} (a : A) (LB : list B) : nat :=
  fold_right max 0 (map (cheight a) LB).
Instance list_cheightable {A B} `{cheightable A B} : cheightable A (list B):=
  Cheightable list_cheight.

Class infinite A : Type :=
  pick_fresh : forall (L : list A), exists a : A, ~In a L.

Class proper A B C `{EqDec A} `{infinite A} `{varsable C A} `{evalable (A -> B) C} `{heightable C} := Proper {
(* Maybe should be merged into/with the simplifier, maybe not. *)
  substitute: A -> A -> C -> C;
  substitute_height: forall a a' c,
    height c = height (substitute a a' c);
  substitute_vars: forall x y obj,
    fresh y obj ->
    fresh x (substitute x y obj);
  substitute_fresh: forall (rho : A -> B) (x y : A) (obj : C),
    fresh y obj ->
    (rho |= obj <-> (upd rho y (rho x)) |= (substitute x y obj));
  change_unused: forall (x : A) (obj : C),
    fresh x obj -> forall (rho : A -> B) v, 
      cequiv obj rho (upd rho x v)
}.
Implicit Arguments Proper [A B C H H0 H1 H2 H3].

Import Setoid.

(* This proof is amazingly subtle. *)
Lemma can_freshen_existentials {A} {B} {C} `{proper A B C}:
  forall (obj : C) (E : list A) (L : list A),
    exists fresh_obj, exists fresh_E,
      e_equiv E obj fresh_E fresh_obj /\
      height obj = height fresh_obj /\
(*      (forall rho, cheight rho obj = cheight rho obj_fresh) /\ *)
      forall x, In x fresh_E -> ~In x L.
Proof.
  intros obj E. revert obj. induction E; intros.
  exists obj. exists nil.
  split. split; intros ? ?; auto.
  split; auto.
  destruct (IHE obj (a :: L ++ E)) as [fresh_obj [fresh_E [? [? ?]]]]. clear IHE.
  (* pick a super-fresh variable *)
  destruct (pick_fresh (a :: fresh_E ++ (vars fresh_obj) ++ L ++ E)) as [fresh_a ?].
  assert (fact1: a <> fresh_a) by (intro; apply H8; left; auto).
  assert (fact2: ~In fresh_a fresh_E) by (intro; apply H8; right; apply in_or_app; auto).
  assert (fact3: ~In fresh_a (vars fresh_obj)) by (intro; apply H8; right; apply in_or_app; right; apply in_or_app; auto).
  assert (fact4: ~In fresh_a L) by (intro; apply H8; right; apply in_or_app; right; apply in_or_app; right; apply in_or_app; auto).
  assert (fact5: ~In fresh_a E) by (intro; apply H8; right; apply in_or_app; right; apply in_or_app; right; apply in_or_app; auto). clear H8.
  assert (fact6: ~In a fresh_E) by (intro Hx; apply H7 in Hx; apply Hx; left; auto).
  exists (substitute a fresh_a fresh_obj). exists (fresh_a :: fresh_E).
  split.
(* the key fact *)
(* ***** *)
  destruct H5. clear H6 H7. (*rename H6 into H_fact. *)
  split; [clear H8 | clear H5]; repeat intro.
(* => *)
  destruct H6 as [rhoE1 ?]. simpl in H6.
  spec H5 (upd rho a (rhoE1 a)).
  spec H5.
    exists rhoE1.
    rewrite override_first_last; auto.
  clear H6.
  destruct H5 as [rhoE2 ?].
  rewrite (substitute_fresh _ a fresh_a),
          override_not_in,
          upd_eq,
          override_absorb_not_in,
          upd_swap
          in H5; auto.
  rewrite <- override_absorb_not_in in H5; auto.
  generalize (change_unused a (substitute a fresh_a fresh_obj)); intro.
  spec H6. apply substitute_vars. red; auto.
  unfold cequiv in H6.
  rewrite <- H6 in H5. clear H6.
  rewrite override_absorb_not_in in H5; auto.
  exists (upd rhoE2 fresh_a (rhoE1 a)).
  simpl.
  rewrite upd_eq, override_within_not_in; auto.
(* <= *)
  destruct H5 as [rhoE1 ?]. simpl in H5.
  generalize (substitute_fresh ([fresh_E => rhoE1] (upd rho a (rhoE1 fresh_a))) a fresh_a fresh_obj fact3); intro.
  rewrite override_not_in in H6; auto.
  rewrite upd_eq in H6.
  pattern ([fresh_E => rhoE1](upd rho a (rhoE1 fresh_a))) in H6 at 2.
  rewrite override_absorb_not_in in H6;auto.
  rewrite upd_swap in H6; auto.
  generalize (change_unused a (substitute a fresh_a fresh_obj)); intro.
  spec H7. apply substitute_vars. apply fact3.
  spec H7 (upd ([fresh_E => rhoE1]rho) fresh_a (rhoE1 fresh_a)) (rhoE1 fresh_a). unfold cequiv in H7.
  rewrite <- H7 in H6. rewrite <- H6 in H5. clear H6 H7.
  spec H8 (upd rho a (rhoE1 fresh_a)).
  spec H8. exists rhoE1; auto. clear H5.
  destruct H8 as [rhoE2 ?].
  case (in_dec eq_dec a E); intro.
  rewrite override_absorb_in in H5; auto.
  exists rhoE2. simpl.
  rewrite <- override_first_last.
  rewrite override_absorb_in; auto.
  exists (upd rhoE2 a (rhoE1 fresh_a)).
  simpl.
  rewrite upd_eq.
  rewrite override_within_not_in; auto.
  rewrite override_absorb_not_in in H5; auto.
(* ***** *)
  split.
  rewrite H6. apply substitute_height.
  repeat intro.
  simpl in *.
  destruct H8.
  subst x. contr.
  apply (H7 _ H8).
  right.
  apply in_or_app.
  auto.
Qed.

Definition substitute_list {A} {B} {C} `{proper A B C} (x y : A) : list C -> list C :=
  map (substitute x y).
Lemma substitute_list_height {A} {B} {C} `{proper A B C}: forall a a' cL,
  height cL = height (substitute_list a a' cL).
Proof.
  induction cL; simpl; intros; auto. simpl in IHcL.
  unfold list_height in *. simpl.
  rewrite IHcL.
  f_equal. apply substitute_height.
Qed.
Lemma substitute_list_vars {A} {B} {C} `{proper A B C}: forall a a' cL,
  fresh a' cL ->
  fresh a (substitute_list a a' cL).
Proof.
  induction cL; simpl; intros. intro. inversion H6.
  rewrite fresh_cons.
  rewrite fresh_cons in H5. destruct H5.
  split; auto.
  apply substitute_vars; auto. 
Qed.
Lemma substitute_list_fresh {A} {B} {C} `{proper A B C}:
  forall (rho : A -> B) (x y : A) (Lobj : list C),
    fresh y Lobj ->
    (rho |= Lobj <-> (upd rho y (rho x)) |= (substitute_list x y Lobj)).
Proof.
  induction Lobj; intros. tauto.
  rewrite fresh_cons in H5. destruct H5.
  spec IHLobj H6. 
  simpl. change eval_list with (@eval _ _ evalable_list). rewrite IHLobj. 
  generalize (substitute_fresh rho x _ a H5).
  tauto.
Qed.
Lemma substitute_list_change_unused {A} {B} {C} `{proper A B C}:
  forall (x : A) (Lobj : list C),
    fresh x Lobj -> forall (rho : A -> B) v, 
      cequiv Lobj rho (upd rho x v).
Proof.
  induction Lobj; intros. red. tauto.
  red. simpl.
  rewrite fresh_cons in H5. destruct H5.
  spec IHLobj H6 rho v. red in IHLobj. 
  simpl. change eval_list with (@eval _ _ evalable_list). rewrite IHLobj. 
  generalize (change_unused _ _ H5 rho v). unfold cequiv. tauto.
Qed.
Instance proper_list {A} {B} {C} `{proper A B C} : proper A B (list C) :=
  Proper substitute_list 
         substitute_list_height 
         substitute_list_vars
         substitute_list_fresh 
         substitute_list_change_unused.

Module Type SV.
  Parameter t : Type.
  Axiom t_eq_dec : EqDec t.
  Existing Instance t_eq_dec.
  Axiom t_infinite : infinite t.
  Existing Instance t_infinite.
  Axiom t_ord : Ord t.
  Existing Instance t_ord.
  Axiom t_tord : TOrd t.
  Existing Instance t_tord.
  Open Scope ord.
  Parameter t_lt_dec : forall (x y : t), {x < y} + {~ (x < y)}.
  Parameter t_leq_dec : forall (x y : t), {x <= y} + {~ (x <= y)}.
  Close Scope ord.
End SV.

Module sv_nat <: SV.
  Definition t : Type := nat.
  Instance t_eq_dec : EqDec t := nat_eq_dec.
  Lemma t_infinite : forall (L : list t), exists t_fresh : t, ~In t_fresh L.
  Proof.
    intros.
    exists (S (fold_right plus 0 L)). remember 0. clear Heqn. revert n.
    induction L; simpl; repeat intro. trivial.
    destruct H. omega. 
    apply (IHL (n + a)).
    replace (fold_right plus (n + a) L) with (a + fold_right plus n L); auto. clear.
    induction L; simpl; intros; omega.
  Qed.

  Instance t_ord : Ord t := nat_ord.
  Instance t_tord : TOrd t := nat_tord.
  Open Scope ord.
  Definition t_lt_dec : forall (x y : t), {x < y} + {~ (x < y)}.
    intros. case (Compare_dec.lt_dec x y).
    left. split. simpl. omega. omega.
    right. intros [? ?]. unfold ord in H. simpl in H.
    apply n. unfold t in *. omega.
  Defined.
  Definition t_leq_dec : forall (x y : t), {x <= y} + {~ (x <= y)} :=
    Compare_dec.le_dec.
  Close Scope ord.
End sv_nat.  

(*
Module Type INTERNAL_SV <: SV.
  Declare Module sv : SV.
  
  Inductive path : Type :=
   | Leaf : path
   | Left : path -> path
   | Right : path -> path.
  Axiom path_eq_dec : EqDec path.
  Existing Instance path_eq_dec.

  Definition t : Type := (sv.t * path)%type.
  Axiom t_eq_dec : EqDec t.
  Existing Instance t_eq_dec.
  
  Axiom t_infinite : forall (L : list t), exists t_fresh : t, ~In t_fresh L.
  Axiom t_ord : Ord t.
  Existing Instance t_ord.
  Axiom t_tord : TOrd t.
  Existing Instance t_tord.
  Open Scope ord.
  Parameter lt_dec : forall (x y : t), {x < y} + {~ (x < y)}.
  Parameter leq_dec : forall (x y : t), {x <= y} + {~ (x <= y)}.
  Close Scope ord.




End INTERNAL_SV.
*)

Module Internal_SV (sv' : SV) <: SV.  (* with Module sv := sv'. *)
  Module sv := sv'.

  Inductive path : Type :=
   | Leaf : path
   | Left : path -> path
   | Right : path -> path.
  Lemma path_eq_dec : EqDec path.
  Proof.
    unfold EqDec.
    induction a. destruct a'; auto; right; congr.
    destruct a'; try (right; congruence).
    destruct (IHa a'). subst a'. auto.
    right. congr.
    destruct a'; try (right; congruence).
    destruct (IHa a'). subst a'. auto.
    right. congr.
  Qed.
  Existing Instance path_eq_dec.
  
  Fixpoint path_leq (p1 p2 : path) : Prop :=
    match p1, p2 with
     | Leaf, _ 
     | Left _, Right _ => True
     | Left p1', Left p2' => path_leq p1' p2'
     | Right p1', Right p2' => path_leq p1' p2'
     | _, _ => False
    end.
  Lemma path_leq_refl: forall p, path_leq p p.
  Proof. induction p; compute; auto. Qed.
  Lemma path_leq_trans: forall p1 p2 p3, 
    path_leq p1 p2 -> path_leq p2 p3 -> path_leq p1 p3.
  Proof. induction p1; auto; intros; icase p2; icase p3; simpl in *; eauto. Qed.
  Lemma path_leq_antisym: forall p1 p2,
    path_leq p1 p2 -> path_leq p2 p1 -> p1 = p2.
  Proof. induction p1; intros; icase p2; simpl in *; f_equal; eauto. Qed.
  Instance path_ord : Ord path := 
    {| ord := path_leq ; ord_refl := path_leq_refl ; ord_trans := path_leq_trans ; ord_antisym := path_leq_antisym |}.
    
  Instance path_tord : TOrd path.
  Proof.
    red. induction x; intros.
    left. hnf. trivial.
    destruct y. right. hnf. trivial.
    destruct (IHx y); auto.
    left. hnf. auto.
    destruct y. right. hnf. trivial.
    right. hnf. trivial.
    destruct (IHx y); auto.
  Qed.
  
  (* Since we care about computation time here we do not want
     to just compine the leq_dec and eq_dec tests, which may
     have to explore the paths twice. *)
  Lemma path_lt_dec : forall (x y : path), ({x < y} + {~ (x < y)})%ord.
  Proof.
    induction x; destruct y.
    right. intro. destruct H. auto.
    left. hnf. split. hnf. trivial. disc.
    left. hnf. split. hnf. trivial. disc.
    right. intro. destruct H. apply H.
    destruct (IHx y).
      left. destruct s. split. hnf. apply H. intro. inv H1. auto.
      right. intro. destruct H. apply n. split. apply H. intro. apply H0. congr.
    left. split. hnf. trivial. disc.
    right. intro. destruct H. apply H.
    right. intro. destruct H. apply H.
    destruct (IHx y).
      left. destruct s. split. hnf. apply H. intro. inv H1; auto.
      right. intro. destruct H. apply n. split. apply H. intro. apply H0. congr.
  Qed.
    
  Lemma path_leq_dec : forall (x y : path), ({x <= y} + {~ (x <= y)})%ord.
  Proof.
    induction x. left. hnf. trivial.
    destruct y. right. intro. apply H.
    destruct (IHx y). left. apply o. right. intro. contr.
    left. hnf. trivial.
    destruct y. right. intro. apply H.
    right. intro. apply H.
    destruct (IHx y).
    left. apply o. right. intro. contr.
  Qed.

  Definition t : Type := (sv.t * path)%type.
  Lemma t_eq_dec : EqDec t.
  Proof.
    unfold EqDec.
    destruct a. destruct a'.
    case (eq_dec t0 t1); intro.
    subst t1.
    case (eq_dec p p0); intro.
    subst p0. auto.
    right. intro. apply n. inv H. trivial.
    right. intro. apply n. inv H. trivial.
  Qed.
  Existing Instance t_eq_dec.

  Lemma t_infinite : forall (L : list t), exists t_fresh : t, ~In t_fresh L.
  Proof.
    intro.
    destruct (sv.t_infinite (map (fun (p : sv.t * path) => fst p) L)).
    exists (x, Leaf). intro. apply H. clear H.
    change x with ((fun p : sv.t * path => fst p) (x,Leaf)).
    apply in_map.
    trivial.
  Qed.
  
  Definition t_leq (t1 t2 : t) : Prop :=
    match t1, t2 with
     (v1, p1), (v2, p2) => (v1 <= v2)%ord /\ ((v1 = v2) -> (p1 <= p2))%ord
    end.
  Lemma t_leq_refl : forall t, t_leq t t.
  Proof. destruct t0. red. split; reflexivity. Qed.
  Lemma t_leq_trans : forall t1 t2 t3, t_leq t1 t2 -> t_leq t2 t3 -> t_leq t1 t3.
  Proof. 
    destruct t1. destruct t2. destruct t3. intros.
    destruct H, H0. split. transitivity t1; auto.
    intro. subst t2. assert (t0 = t1) by (apply ord_antisym; auto). subst t1.
    transitivity p0; auto.
  Qed.
  Lemma t_leq_antisym : forall t1 t2, t_leq t1 t2 -> t_leq t2 t1 -> t1 = t2.
  Proof. 
    destruct t1. destruct t2. intros.
    destruct H, H0. assert (t0 = t1) by (apply ord_antisym; auto). subst t1.
    assert (p = p0) by (apply ord_antisym; auto). subst. trivial.
  Qed.
  Instance t_ord : Ord t := 
    {| ord := t_leq ; ord_refl := t_leq_refl ; ord_trans := t_leq_trans ; ord_antisym := t_leq_antisym |}.

  Instance t_tord : TOrd t.
  Proof.
    red. destruct x. destruct y.
    destruct (eq_dec t0 t1). subst.
    destruct (tord_total p p0).
    left. hnf. split; auto. reflexivity.
    right. hnf. split; auto. reflexivity.
    destruct (tord_total t0 t1).
    left. hnf. split; auto; contr.
    right. hnf. split; auto. intros; subst. destruct n. trivial.
  Qed.

  Open Scope ord.
  (* this is *not* computationally optimal; need to
     shift the SV module type for that. *)
  Lemma t_lt_dec : forall (x y : t), {x < y} + {~ (x < y)}.
  Proof.
    destruct x. destruct y.
    case (sv.t_lt_dec t0 t1); intro.
    left. split. split. apply sord_leq. trivial. intro. subst. destruct s. exfalso. auto.
    intro. inv H. destruct s; auto.
    (* Here is the suboptimal part : we examine t0 t1 again,
       this time for equality. *)
    case (eq_dec t0 t1); intro.
    case (path_lt_dec p p0).
    left. destruct s. subst. split. split. reflexivity. auto.
    intro. inv H1. auto.
    right. subst. intro. destruct H. destruct H. subst. spec H1; auto.
    apply H0. clear H0 H n. assert (p = p0).
    case (eq_dec p p0); auto. intro.
    elim n0. split; auto. subst;trivial.
    right. intro. destruct H. apply n. split; auto.
    destruct H; auto.
  Qed.
  
  (* Again, computationally suboptimal. *)
  Lemma t_leq_dec : forall (x y : t), {x <= y} + {~ (x <= y)}.
  Proof.
    destruct x. destruct y.
    case (sv.t_leq_dec t0 t1); intro.
    (* Test t0 t1 again... *)
    case (eq_dec t0 t1); intro.
    case (path_leq_dec p p0); intro.
    left. split; auto.
    right. intro. destruct H. auto.
    left. split; auto. contr.
    right. intro. destruct H; auto.
  Qed.
  Close Scope ord.
End Internal_SV.


(*
Module Type TREE_SHARES.
  Parameter t : Type.
  Parameter top : t.
  Parameter bot : t.

 
  Axiom share_height : heightable t.
  Existing Instance share_height.

  Parameter glb : t -> t -> t.
  Parameter lub : t -> t -> t.
  Parameter comp : t -> t.


  Parameter add : t -> t -> option t.
  Parameter sub : t -> t -> option t.

  Parameter decompose : t -> (t * t).
  Parameter recompose : (t * t) -> t. 

(* AXIOMS *)
  Axiom nontrivial : top <> bot.
  Axiom join_t : Join t. Existing Instance join_t.
  Axiom perm_t: Perm_alg t. Existing Instance perm_t.
  Axiom sep_t: Sep_alg t. Existing Instance sep_t.
  Axiom canc_t: Canc_alg t. Existing Instance canc_t.
  Axiom disj_t: Disj_alg t.  Existing Instance disj_t.
  Axiom cross_t : Cross_alg t. Existing Instance cross_t.
  
  (* Decidable equality and order *)
  Axiom eq_dec_t : EqDec t. Existing Instance eq_dec_t.
  Axiom leq_dec : forall (x y : t), ({x <= y} + {~ (x <= y)})%ord.

  Axiom height_top : height top = 0.
  Axiom height_bot : height bot = 0.
  Axiom height_zero_eq: forall t, height t = 0 -> {t = top} + {t = bot}.
  Axiom decompose_height : forall n t1 t2 t3,
                          height t1 = S n ->
                          decompose t1 = (t2, t3) ->
                          height t2 <= n /\ height t3 <= n.
  Axiom decompose_recompose: forall t1 t2,
    decompose (recompose (t1, t2)) = (t1, t2).
  Axiom recompose_decompose: forall t,
    recompose (decompose t) = t.
  Axiom decompose_join: forall t1 t11 t12 t2 t21 t22 t3 t31 t32,
    decompose t1 = (t11, t12) ->
    decompose t2 = (t21, t22) ->
    decompose t3 = (t31, t32) ->
    (join t1 t2 t3 <-> 
    (join t11 t21 t31 /\ join t12 t22 t32)).
(*
  Axiom depth_recompose: forall t1 t2 t,
    recompose (t1, t2) = t ->
    depth 
*)
(* these are not minimal for now, but whatever *)
  Axiom bot_identity : identity bot.
  Axiom identity_bot : forall t, identity t -> t = bot.
  Axiom bot_join : forall t, join bot t t.
  Open Scope ord.
  Axiom bot_bot : forall t, bot <= t.
  Axiom top_top : forall t, t <= top.
  Axiom join_unfold: forall t1 t2 t3 : t,
    join t1 t2 t3 <-> lub t1 t2 = t3 /\ glb t1 t2 = bot.
  Axiom join_top : forall t1 t2, join top t1 t2 -> t1 = bot /\ t2 = top.
  Axiom add_join : forall t1 t2 t3,
    add t1 t2 = Some t3 <-> join t1 t2 t3.
  Axiom sub_join : forall t1 t2 t3,
    sub t1 t2 = Some t3 <-> join t2 t3 t1.
(* Various BA axioms/facts *)
  Axiom lub_upper1 : forall x y, x <= (lub x y).
  Axiom lub_upper2 : forall x y, y <= (lub x y).
  Axiom lub_least : forall x y z, x <= z -> y <= z -> (lub x y) <= z.
  Axiom glb_lower1 : forall x y, (glb x y) <= x.
  Axiom glb_lower2 : forall x y, (glb x y) <= y.
  Axiom glb_greatest : forall x y z, z <= x -> z <= y -> z <= (glb x y).
  Axiom distrib1 : forall x y z, glb x (lub y z) = lub (glb x y) (glb x z).
  Axiom distrib2 : forall x y z, lub x (glb y z) = glb (lub x y) (lub x z).
  Axiom lub_bot : forall x, lub x bot = x.
  Axiom lub_top : forall x, lub x top = top.
  Axiom glb_bot : forall x, glb x bot = bot.
  Axiom glb_top : forall x, glb x top = x.
  Axiom comp1 : forall x, lub x (comp x) = top.
  Axiom comp2 : forall x, glb x (comp x) = bot.
  Axiom demorgan1 : forall x y, comp (lub x y) = glb (comp x) (comp y).
  Axiom demorgan2 : forall x y, comp (glb x y) = lub (comp x) (comp y).
  Axiom comp_inv : forall x, comp (comp x) = x.
  Axiom lub_commute : forall x y, lub x y = lub y x.
  Axiom glb_commute : forall x y, glb x y = glb y x.
  Axiom lub_assoc : forall x y z, lub (lub x y) z = lub x (lub y z).
  Axiom glb_assoc : forall x y z, glb (glb x y) z = glb x (glb y z).
  Axiom lub_idem : forall x, (lub x x) = x.
  Axiom ord_spec1 : forall x y, x <= y <-> x = glb x y.
  Axiom ord_spec2 : forall x y, x <= y <-> lub x y = y.
  Axiom glb_idem : forall x, glb x x = x.
  Close Scope ord.
End TREE_SHARES.
*)


(*
Module Tree_Bonus.
  Import Share.


End Tree_Bonus.

Import Tree_Bonus.
*)
(*
Class get_vars (A : Type) (B: Type): Type := Get_vars { vars_of : A -> list B}.
Implicit Arguments Get_vars [A B].
*)
(* The input type, supplied by the tool (e.g., SLEEK) *)

(*

Inductive objectT {A B}: Type :=
  | Vobject : A -> objectT
  | Cobject : B -> objectT.

Definition get_obj_val {A B} (ctx : A -> B) (obj : @objectT A B) :=
 match obj with
 | Vobject v => ctx v
 | Cobject c => c
 end.
Instance getable_obj_val {A B}: getable (A -> B) (@objectT A B) B :=
 Getable get_obj_val.

Module Type EQUATION_SYSTEM.

  Parameter var : Type.
  Axiom var_eq_dec : EqDec var. 
  Existing Instance var_eq_dec.
  Parameter equality : Type.
  Axiom equality_eq_dec : EqDec equality.
  Existing Instance equality_eq_dec.
  Parameter equation : Type.
  Axiom equation_eq_dec : EqDec equation.
  Existing Instance equation_eq_dec.
  Definition context := var -> share.
  Parameter eval_equality : evalable context equality.
  Existing Instance eval_equality.
  Parameter eval_equation : evalable context equation.
  Existing Instance eval_equation.
  Parameter eval_nzvars : evalable context var.
  Existing Instance eval_nzvars.

  Record sat_equation_system : Type := Sat_equation_system {
    sat_nzvars        : list var;
    sat_equalities    : list equality;
    sat_equations     : list equation
  }.
  Record impl_equation_system : Type := Impl_equation_system {
    impl_nzvars     : list var;
    impl_exvars     : list var;
    impl_equalities : list equality;
    impl_equations  : list equation
  }.

  Definition eval_sat_equation_system (ctx : context) (ses : sat_equation_system) : Prop :=
    ctx |= (sat_equalities ses) /\ 
    ctx |= (sat_equations ses) /\
    ctx |= (sat_nzvars ses).
  Instance evalable_sat_equation_system : evalable context sat_equation_system :=
    Evalable eval_sat_equation_system.

  Definition ies2ses := 
  fun (ies : impl_equation_system) => 
  Sat_equation_system (impl_nzvars ies) (impl_equalities ies) (impl_equations ies).

  Definition eval_impl_equation_system (ctx : context) (ies : impl_equation_system) : Prop:=
   e_eval ctx (impl_exvars ies) (ies2ses ies).
  Instance evalable_impl_equation : evalable context impl_equation_system :=
   Evalable eval_impl_equation_system.

End EQUATION_SYSTEM.

Module equation_system (Import sv :SV) : EQUATION_SYSTEM.
 
  Definition var := t.
  Definition var_eq_dec : EqDec var := _.
  Existing Instance var_eq_dec.
  Definition object := @objectT var share.
  Definition equality := (object * object)%type.
  Instance obj_eq_dec: EqDec object.
  Proof with congruence.
  repeat intro.
  icase a;icase a'.
  destruct (eq_dec v v0). subst.
  left... right...
  right...
  right...
  destruct (eq_dec s s0). subst.
  left... right...
  Defined.
  Instance equality_eq_dec : EqDec equality.
  Proof with congruence.
  repeat intro.
  destruct a;destruct a'.
  destruct (eq_dec o o1). subst.
  destruct (eq_dec o0 o2). subst.
  left... right... right...
  Defined.
  Definition equation := (object * object * object)%type.
  Instance equation_eq_dec : EqDec equation.
  Proof with congruence.
  repeat intro.
  destruct a as [[? ?] ?];destruct a' as [[? ?] ?].
  destruct (eq_dec o o2).
  destruct (eq_dec o0 o3).
  destruct (eq_dec o1 o4).
  left... right... right... right...
  Defined.
  Definition context := var -> share.
  Instance eval_equality : evalable context equality.
  constructor. repeat intro.
  destruct X0. apply (get X o = get X o0).
  Defined.
  Instance eval_equation : evalable context equation.
  constructor. repeat intro.
  destruct X0 as [[? ?] ?]. apply (join (get X o) (get X o0) (get X o1)).
  Defined.
  Instance eval_nzvars : evalable context var.
  constructor. repeat intro.
  apply (X X0 <> emptyshare).
  Defined.
  Existing Instance eval_nzvars.
  Parameter override : context -> context -> list var -> context.

  Record sat_equation_system : Type := Sat_equation_system {
    sat_nzvars        : list var;
    sat_equalities    : list equality;
    sat_equations     : list equation
  }.
  Record impl_equation_system : Type := Impl_equation_system {
    impl_nzvars     : list var;
    impl_exvars     : list var;
    impl_equalities : list equality;
    impl_equations  : list equation
  }.

  Definition eval_sat_equation_system (ctx : context) (ses : sat_equation_system) : Prop :=
    ctx |= (sat_equalities ses) /\ 
    ctx |= (sat_equations ses) /\
    ctx |= (sat_nzvars ses).
  Instance evalable_sat_equation_system : evalable context sat_equation_system :=
    Evalable eval_sat_equation_system.

  Definition ies2ses := 
  fun (ies : impl_equation_system) => 
  Sat_equation_system (impl_nzvars ies) (impl_equalities ies) (impl_equations ies).

  Definition eval_impl_equation_system (ctx : context) (ies : impl_equation_system) : Prop:=
   e_eval ctx (impl_exvars ies) (ies2ses ies).
  Instance evalable_impl_equation : evalable context impl_equation_system :=
   Evalable eval_impl_equation_system.
End equation_system.

(* This is a modified version used internally to the solver in a way that reduces some cases *)
Module Type INTERNAL_EQUATION_SYSTEM.
  Declare Module sv : SV.

  Definition var : Type := sv.t.
  Definition context : Type := var -> share.
  Instance cheightable_var : cheightable context var :=
    Cheightable (fun ctx v => height (ctx v)).

  (* Objects *)
  Inductive object : Type :=
    | Vobject : var -> object
    | Cobject : share -> object.

  Axiom dec_eq_object : EqDec object.
  Existing Instance dec_eq_object.

  Definition height_object (o : object) : nat :=
    match o with
     | Cobject c => height c
     | Vobject v => 0
    end.
  Axiom is_height_zero_object : is_height_zero_spec height_object. 
  Instance heightable_object : heightable object :=
    Heightable height_object is_height_zero_object.

  Definition cheight_object (ctx : context) (o : object) : nat :=
    match o with
    | Cobject c => 0
    | Vobject v => height (ctx v)
    end.
  Instance cheightable_object : cheightable context object :=
   Cheightable cheight_object.

  Definition get_object (ctx : context) (so : object) : share :=
    match so with
     | Cobject c => c
     | Vobject v => ctx v
    end.
  Instance getable_object : getable context object share :=
    Getable get_object.
  
  Definition vars_obj (obj : object) : list var :=
    match obj with
     | Cobject c => nil
     | Vobject v' => v' :: nil
   end.
  Instance varsable_obj : varsable object var :=
    Varsable vars_obj.
  (* End Objects *)
  
  (* Substitutions *)
  Definition substitution : Type :=
    {p : (var * object)%type | snd p <> Vobject (fst p)}.
  Definition sbst_var (sbst : substitution) : var := fst (projT1 sbst).
  Definition sbst_object (sbst : substitution) : object := snd (projT1 sbst).
  Program Definition mkCsubstitution (x : var) (sh : share) : substitution :=
    (x, Cobject sh).
  (*Next Obligation. disc. Qed.*)
  Program Definition mkVsubstitution (x : var) (y : var) (pf : x <> y) : substitution :=
    (x, Vobject y).
  (*Next Obligation. unfold fst, snd. intro. apply pf. inv H. trivial. Qed.*)
  
  Axiom dec_eq_substitution : EqDec substitution.
  Existing Instance dec_eq_substitution.

  Definition eval_substitution (ctx : context) (subst : substitution) : Prop :=
    match subst with exist (x, fp) pf => ctx x = get ctx fp end.
  Instance evalable_substitution : evalable context substitution :=
    Evalable eval_substitution.
  Definition height_substitution (s : substitution) : nat :=
    height (sbst_object s).
  
  Definition vars_subst (subst : substitution) : list var :=
   (sbst_var subst) :: (vars (sbst_object subst)).
  Instance varsable_subst : varsable substitution var :=
   Varsable vars_subst.

  Axiom is_height_zero_substitution : is_height_zero_spec height_substitution.
  Instance heightable_substitution : heightable substitution :=
    Heightable height_substitution is_height_zero_substitution.

  Definition cheight_substitution (ctx : context) (s : substitution) : nat :=
   max (cheight ctx ( Vobject (sbst_var s))) (cheight ctx (sbst_object s)).
  Instance cheightable_substitution : cheightable context substitution :=
    Cheightable cheight_substitution.
  
  Axiom proper_substitution: proper var share substitution.
  Existing Instance proper_substitution.
    
(* Not sure if these belong here or not... *)
  Definition upd_context (ctx : context) (sbst : substitution) : context :=
    upd ctx (sbst_var sbst) (get ctx (sbst_object sbst)).
  Axiom upd_context_eq: forall ctx sbst, 
    upd_context ctx sbst (sbst_var sbst) = get ctx (sbst_object sbst).
  Axiom upd_context_equiv: forall ctx sbst,
    ctx (sbst_var sbst) = get ctx (sbst_object sbst) ->
    upd_context ctx sbst = ctx.
  Definition upd_context_list (ctx : context) (subst_list : list substitution) : context :=
    fold_right (fun vfp ctx' => upd_context ctx' vfp) ctx subst_list.
  Axiom upd_context_list_equiv: forall ctx subst_list,
    eval_list ctx subst_list ->
    upd_context_list ctx subst_list = ctx.
(* End not sure *)

  (* Equations *)
  Definition equation : Type := 
    (object * object * object)%type.

  Definition vars_eqn (eqn :equation) : list var :=
   match eqn with (obj1,obj2,obj3) => (vars obj1) ++ (vars obj2) ++ (vars obj3) end.
  Instance varsable_eqn : varsable equation var :=
   Varsable vars_eqn.

  Definition height_equation (eqn : equation) : nat :=
    match eqn with (o1, o2, o3) =>
      max (height o1) (max (height o2) (height o3))
    end.
  Axiom is_height_zero_equation : is_height_zero_spec height_equation.
  Instance heightable_equation : heightable equation :=
    Heightable height_equation is_height_zero_equation.
  Definition cheight_equation (ctx : context)(eqn :equation) : nat :=
   match eqn with (o1,o2,o3) =>
    max (cheight ctx o1) (max (cheight ctx o2) (cheight ctx o3))
   end.
  Instance cheightable_equation : cheightable context equation :=
   Cheightable cheight_equation.
  Definition eval_equation (ctx : context) (eqn : equation) : Prop :=
    match eqn with (fp1, fp2, fp3) => 
      join (get ctx fp1) (get ctx fp2) (get ctx fp3) 
    end.
  Instance evalable_equation : evalable context equation :=
    Evalable eval_equation.
  Axiom proper_equation: proper var share equation.
  Existing Instance proper_equation.

  Record equation_system : Type := Equation_system {
    eqs_substitutions : list substitution;
    eqs_equations     : list equation
  }.
  Definition height_equation_system (eqs : equation_system) : nat :=
    max (height (eqs_substitutions eqs)) (height (eqs_equations eqs)).
  Axiom is_height_zero_equation_system : is_height_zero_spec height_equation_system.
  Instance heightable_equation_system : heightable equation_system :=
    Heightable height_equation_system is_height_zero_equation_system.
  Definition cheight_equation_system (ctx : context) (eqs : equation_system) : nat :=
    max (cheight ctx (eqs_substitutions eqs)) (cheight ctx (eqs_equations eqs)).
  Instance cheightable_equation_system : cheightable context equation_system :=
    Cheightable cheight_equation_system.  
  Definition eval_equation_system (ctx : context) (eqs : equation_system) : Prop :=
    eval ctx (eqs_substitutions eqs) /\ eval ctx (eqs_equations eqs).
  Instance evalable_equation_system : evalable context equation_system :=
    Evalable eval_equation_system.
  Definition vars_es (es : equation_system) : list var :=
    vars (eqs_substitutions es) ++ vars (eqs_equations es).
  Instance varsable_es : varsable equation_system var :=
   Varsable vars_es.  
  Axiom proper_equation_system: proper var share equation_system.
  Existing Instance proper_equation_system.

  Record top_level : Type := Top_level {
    tl_equation_system : equation_system;
    tl_exists           : list var;
    tl_nonzeros         : list var
  }.

  Definition height_top_level (tleqs : top_level) : nat :=
    height (tl_equation_system tleqs).
  Axiom is_height_zero_top_level : is_height_zero_spec height_top_level.
  Instance heightable_top_level : heightable top_level :=
    Heightable height_top_level is_height_zero_top_level.
  Definition cheight_top_level (ctx : context)(tleqs : top_level) : nat :=
    max (cheight ctx (tl_equation_system tleqs)) (cheight ctx (tl_nonzeros tleqs)).
  Instance cheightable_top_level : cheightable context top_level :=
    Cheightable cheight_top_level.
  Definition eval_var_nz (ctx : context) (v : var) : Prop :=
   ctx v <> bot.
  Instance evalable_var_nz : evalable context var := Evalable eval_var_nz.
  Definition eval_top_level (ctx : context) (tleqs : top_level) : Prop :=
    exists ctx',
      [(tl_exists tleqs) => ctx'] ctx |= (tl_equation_system tleqs) /\
      [(tl_exists tleqs) => ctx'] ctx |= (tl_nonzeros tleqs).
  Instance evalable_top_level : evalable context top_level :=
    Evalable eval_top_level.

  Record top_es : Type := Top_es {
    tes_equation_system : equation_system;
    tes_exists          : list var
  }.
  Definition height_top_es (tes : top_es) : nat :=
    height (tes_equation_system tes).
  Axiom is_height_zero_top_es : is_height_zero_spec height_top_es.
  Instance heightable_top_es : heightable top_es :=
    Heightable height_top_es is_height_zero_top_es.
  Definition cheight_top_es (ctx : context)(tes : top_es) : nat :=
    cheight ctx (tes_equation_system tes).
  Instance cheightable_top_es : cheightable context top_es :=
    Cheightable cheight_top_es.
  Definition eval_top_es (ctx : context) (tes : top_es) : Prop :=
    exists ctx',
      [(tes_exists tes) => ctx'] ctx |= (tes_equation_system tes).
  Instance evalable_top_es : evalable context top_es :=
    Evalable eval_top_es.

  Definition tl2tes (tl : top_level) : top_es := 
   Top_es (tl_equation_system tl) (tl_exists tl).

  Definition eval_top_level_bounded (ctx : context) (btleqs : (top_level*nat)) : Prop :=
   exists ctx',
      match btleqs with (tleqs,n) =>
      cheight ctx' tleqs <= n /\
      [(tl_exists tleqs) => ctx'] ctx |= (tl_equation_system tleqs) /\
      [(tl_exists tleqs) => ctx'] ctx |= (tl_nonzeros tleqs)
      end.
  Instance evalable_top_level_bounded : evalable context (top_level*nat) :=
    Evalable eval_top_level_bounded.

(*

  Record ntop_level : Type := NTop_level {
    ntl_tl : top_level;
    ntl_nonzeros : list var
  }.

  Definition height_ntop_level (ntleqs : ntop_level) : nat :=
    height (ntl_tl ntleqs).
  Axiom is_height_zero_ntop_level : is_height_zero_spec height_ntop_level.
  Instance heightable_ntop_level : heightable ntop_level :=
    Heightable height_ntop_level is_height_zero_ntop_level.
  Definition cheight_ntop_level (ctx : context)(ntleqs : ntop_level) : nat :=
    max (cheight ctx (ntl_tl ntleqs)) (cheight ctx (ntl_nonzeros ntleqs)).
  Instance cheightable_ntop_level : cheightable context ntop_level :=
    Cheightable cheight_ntop_level.  
  Definition eval_nonzeros (ctx : context)(nl : list var) : Prop :=
    fold_right (fun (v : var)(P : Prop)  => P /\ ~(ctx v = bot)) True nl.
  Instance evalable_nonzeros : evalable context (list var) :=
    Evalable eval_nonzeros.
  Definition eval_ntop_level (ctx : context) (ntleqs : ntop_level) : Prop :=
    eval ctx (ntl_tl ntleqs) /\ eval ctx (ntl_nonzeros ntleqs).
  Instance evalable_ntop_level : evalable context ntop_level :=
    Evalable eval_ntop_level.
*)
End INTERNAL_EQUATION_SYSTEM.

Module Internal_Equation_System (sv' : SV)
  : INTERNAL_EQUATION_SYSTEM with Module sv := sv'.

  Module sv := sv'.

  Definition var : Type := sv.t.
  Definition context : Type := var -> share.
  Instance cheightable_var : cheightable context var :=
    Cheightable (fun ctx v => height (ctx v)).

  (* Objects *)
  Inductive object : Type :=
    | Vobject : var -> object
    | Cobject : share -> object.

  Instance dec_eq_object : EqDec object.
    unfold EqDec.
    destruct a; destruct a'.
    destruct (eq_dec v v0). left. f_equal. trivial.
    right. intro. inv H. apply n. trivial.
    right. disc.
    right. disc.
    destruct (eq_dec s s0). left. f_equal. trivial.
    right. intro. inv H. apply n. trivial.
  Defined.

  Definition height_object (o : object) : nat :=
    match o with
     | Cobject c => height c
     | Vobject v => 0
    end.
  Lemma is_height_zero_object : is_height_zero_spec height_object.
  Proof.
    hnf.
    destruct a. left. trivial. 
    simpl. case (is_height_zero s); [left | right]; trivial.
  Qed.
  Instance heightable_object : heightable object :=
    Heightable height_object is_height_zero_object.

  Definition cheight_object (ctx : context) (o : object) : nat :=
    match o with
    | Cobject c => 0
    | Vobject v => height (ctx v)
    end.
  Instance cheightable_object : cheightable context object :=
   Cheightable cheight_object.

  Definition get_object (ctx : context) (so : object) : share :=
    match so with
     | Cobject c => c
     | Vobject v => ctx v
    end.
  Instance getable_object : getable context object share :=
    Getable get_object.
  
  Definition vars_obj (obj : object) : list var :=
    match obj with
     | Cobject c => nil
     | Vobject v' => v' :: nil
   end.
  Instance varsable_obj : varsable object var :=
    Varsable vars_obj.
  
  Definition substitute_object (x y : var) (obj : object) : object :=
    match obj with
     | Cobject c => Cobject c
     | Vobject v => Vobject (if eq_dec x v then y else v) 
    end.
  Lemma substitute_object_height: forall x y o,
    height o = height (substitute_object x y o).
  Proof. intros. icase o. Qed.
  Lemma substitute_object_vars: forall x y o,
    fresh y o -> fresh x (substitute_object x y o).
  Proof.
    intros. icase o. 
    unfold substitute_object. case eq_dec; intro.
    subst v. intro. apply H. icase H0. left. auto.
    intro. icase H0.
  Qed.
  Lemma substitute_object_fresh: forall rho x y obj,
    fresh y obj -> get rho obj = get (upd rho y (rho x)) (substitute_object x y obj).
  Proof.
    intros. icase obj. simpl.
    unfold upd. case (eq_dec x v).
    intros. subst x. case eq_dec; auto.
    intro. exfalso; auto.
    case eq_dec; auto. intros.
    exfalso. apply H. left. auto.
  Qed.
  Lemma substitute_object_change_unused: forall x obj,
    fresh x obj ->
    forall rho v,
    get rho obj = get (upd rho x v) obj.
  Proof.
    intros. icase obj. simpl.
    rewrite upd_neq; auto.
    intro. subst.
    apply H. left. trivial.
  Qed.
  
  (* Substitutions *)
  Definition substitution : Type :=
    {p : (var * object)%type | snd p <> Vobject (fst p)}.
  Definition sbst_var (sbst : substitution) : var := fst (projT1 sbst).
  Definition sbst_object (sbst : substitution) : object := snd (projT1 sbst).
  Program Definition mkCsubstitution (x : var) (sh : share) : substitution :=
    (x, Cobject sh).
  (*Next Obligation. disc. Qed.*)
  Program Definition mkVsubstitution (x : var) (y : var) (pf : x <> y) : substitution :=
    (x, Vobject y).
  (*Next Obligation. unfold fst, snd. intro. apply pf. inv H. trivial. Qed.*)
  
  Instance dec_eq_substitution : EqDec substitution.
  Proof.
    repeat intro. destruct a. destruct a'.
    destruct x. destruct x0.
    case (eq_dec v v0). case (eq_dec o o0).
    left. subst. apply exist_ext. trivial.
    right. intro. inv H. apply n1. trivial.
    right. intro. inv H. apply n1. trivial.
  Qed.

  Definition eval_substitution (ctx : context) (subst : substitution) : Prop :=
    match subst with exist (x, fp) pf => ctx x = get ctx fp end.
  Instance evalable_substitution : evalable context substitution :=
    Evalable eval_substitution.
  Definition height_substitution (s : substitution) : nat :=
    height (sbst_object s).
  
  Definition vars_subst (subst : substitution) : list var :=
   (sbst_var subst) :: (vars (sbst_object subst)).
  Instance varsable_subst : varsable substitution var :=
   Varsable vars_subst.

  Lemma is_height_zero_substitution : is_height_zero_spec height_substitution.
  Proof.
    hnf.
    destruct a. destruct x. unfold height_substitution, sbst_object. simpl projT1. unfold snd.
    apply is_height_zero.
  Qed.
  Instance heightable_substitution : heightable substitution :=
    Heightable height_substitution is_height_zero_substitution.

  Definition cheight_substitution (ctx : context) (s : substitution) : nat :=
   max (cheight ctx ( Vobject (sbst_var s))) (cheight ctx (sbst_object s)).
  Instance cheightable_substitution : cheightable context substitution :=
    Cheightable cheight_substitution.

  (* Since we don't need to do this computationally, we can
     be slow and do extra comparisions. *)
  (* There might be a more elegant way to do this with 
     substitute_object, but it doesn't really matter. *)
  Definition substitute_substitution (v1 v2 : var) (s : substitution) : substitution :=
    match s with
     | exist (v, Cobject c) _ => 
         if eq_dec v v1 then mkCsubstitution v2 c else s
     | exist (v, Vobject v') _ => 
         let vx := if eq_dec v v1 then v2 else v in
         let vy := if eq_dec v' v1 then v2 else v' in
         match eq_dec vx vy with
          | left _ => s (* v2 was not fresh! *)
          | right pf => mkVsubstitution vx vy pf
         end
    end.
  Instance proper_substitution: proper var share substitution.
  Proof.
    apply Proper with substitute_substitution.
    (* prop 1 *)
    destruct c; auto. simpl. destruct x.
    icase o; case eq_dec; auto.
    (* prop 2 *)
    repeat intro.
    destruct obj. destruct x0. destruct o. red in H. unfold IN in *. simpl in *.
    unfold sbst_var in H; simpl in H.
    revert H0. case eq_dec; case eq_dec; case eq_dec; unfold sbst_var, sbst_object; simpl; intros; subst; try tauto.
    destruct H0. auto. destruct H0; auto.
    destruct H0. auto. destruct H0; auto.
    red in H. unfold IN in *. simpl in *. unfold sbst_var, sbst_object, fst, snd in *.
    revert H0. case eq_dec; simpl in *; intros.
    subst v. apply H. left. symmetry. icase H0.
    icase H0.
    (* prop 3 *)
    intros. destruct obj. destruct x0. 
    unfold fresh, IN in H. simpl in H. unfold sbst_var, sbst_object in H. simpl in H, n.
    assert (v <> y /\ ~In y (vars_obj o)) by tauto. clear H. destruct H0.
    destruct o; simpl.
    case eq_dec; case eq_dec; case eq_dec; simpl; intros; subst; try tauto;
    try rewrite upd_eq; try rewrite upd_neq; auto; try tauto.
    simpl in H0. destruct H0. auto.
    simpl in H0. 
    rewrite upd_neq; auto. tauto.
    case eq_dec; simpl; intros; subst.
    rewrite upd_eq. tauto.
    rewrite upd_neq; auto. tauto.
    (* prop 4 *)
    intros. red.
    destruct obj; icase x0; simpl in *.
    unfold fresh, IN in H. simpl in H. unfold sbst_var, sbst_object in H. simpl in H.
    assert (v0 <> x /\ ~In x (vars_obj o)) by tauto. clear H. destruct H0.
    rewrite upd_neq; auto.
    icase o; simpl.
    rewrite upd_neq. tauto. intro. apply H0. simpl. auto.
    tauto.
  Qed.

  Definition upd_context (ctx : context) (sbst : substitution) : context :=
    upd ctx (sbst_var sbst) (get ctx (sbst_object sbst)).
  Lemma upd_context_eq: forall ctx sbst, 
    upd_context ctx sbst (sbst_var sbst) = get ctx (sbst_object sbst).
  Proof.
    unfold upd_context. intros. rewrite upd_eq. trivial.
  Qed.
  Lemma upd_context_equiv: forall ctx sbst,
    ctx (sbst_var sbst) = get ctx (sbst_object sbst) ->
    upd_context ctx sbst = ctx.
  Proof.
    unfold upd_context, upd. intros.
    extensionality a'.
    case (eq_dec (sbst_var sbst) a'); intros. subst a'. rewrite H; trivial.
    trivial.
  Qed.

  Definition upd_context_list (ctx : context) (subst_list : list substitution) : context :=
    fold_right (fun vfp ctx' => upd_context ctx' vfp) ctx subst_list.
  Lemma upd_context_list_equiv: forall ctx (subst_list : list substitution),
    eval_list ctx subst_list ->
    upd_context_list ctx subst_list = ctx. 
  Proof.
    induction subst_list; simpl. trivial.
    destruct a. simpl. intros. destruct H.
    rewrite IHsubst_list; auto. destruct x.
    apply upd_context_equiv; auto.
  Qed.

  (* Equations *)
  Definition equation : Type := 
    (object * object * object)%type.

  Definition vars_eqn (eqn :equation) : list var :=
   match eqn with (obj1,obj2,obj3) => (vars obj1) ++ (vars obj2) ++ (vars obj3) end.
  Instance varsable_eqn : varsable equation var :=
   Varsable vars_eqn.

  (* Unfold fresh componentwise *)
  Lemma unfold_fresh_equation: forall v o1 o2 o3,
    fresh v (o1,o2,o3) <-> (fresh v o1 /\ fresh v o2 /\ fresh v o3).
  Proof.
    split; intros.
    unfold fresh, IN in *. simpl in *.
    split. intro. apply H. 
    apply in_or_app. auto.
    split; intro; apply H; apply in_or_app; right; apply in_or_app; auto.
    destruct H as [? [? ?]].
    intro. hnf in H2. simpl in H2.
    apply in_app_or in H2. icase H2.
    apply in_app_or in H2. icase H2.
  Qed.

  Definition height_equation (eqn : equation) : nat := 
    match eqn with (o1, o2, o3) =>
      max (height o1) (max (height o2) (height o3))
    end.
  Lemma is_height_zero_equation : is_height_zero_spec height_equation.
  Proof.
    hnf.
    destruct a as [[? ?] ?].
    unfold height_equation.
    case (is_height_zero o); intro.
    case (is_height_zero o0); intro.
    case (is_height_zero o1); intro.
    left. rewrite e, e0, e1. trivial.
    right. rewrite e, e0. simpl. trivial.
    right. rewrite e. icase (height o0); icase (height o1).
    right. icase (height o). icase (height o0); icase (height o1).
  Qed.
  Instance heightable_equation : heightable equation :=
    Heightable height_equation is_height_zero_equation.

  Definition cheight_equation (ctx : context)(eqn :equation) : nat :=
   match eqn with (o1,o2,o3) =>
    max (cheight ctx o1) (max (cheight ctx o2) (cheight ctx o3))
   end.
  Instance cheightable_equation : cheightable context equation :=
   Cheightable cheight_equation.

  Definition eval_equation (ctx : context) (eqn : equation) : Prop :=
    match eqn with (fp1, fp2, fp3) => 
      join (get ctx fp1) (get ctx fp2) (get ctx fp3) 
    end.
  Instance evalable_equation : evalable context equation :=
    Evalable eval_equation.
  
  Definition substitute_equation (v1 v2 : var) (e : equation) : equation :=
    match e with (o1, o2, o3) =>
      (substitute_object v1 v2 o1, substitute_object v1 v2 o2, substitute_object v1 v2 o3)
    end.
  Instance proper_equation: proper var share equation.
  Proof.
    apply Proper with substitute_equation.
    destruct c as [[? ?] ?]. simpl.
    do 3 rewrite <- substitute_object_height. trivial.
    destruct obj as [[? ?] ?]. simpl. intro.
    rewrite unfold_fresh_equation in *.
    destruct H as [? [? ?]].
    split. apply substitute_object_vars; auto.
    split; apply substitute_object_vars; auto.
    destruct obj as [[? ?] ?]. simpl. intro.
    rewrite unfold_fresh_equation in H. destruct H as [? [? ?]].
    do 3 (rewrite <- substitute_object_fresh; auto). tauto.
    destruct obj as [[? ?] ?]. simpl. intro.
    rewrite unfold_fresh_equation in H. destruct H as [? [? ?]].
    unfold cequiv. simpl. intros.
    do 3 (rewrite <- substitute_object_change_unused; auto). tauto.
  Qed.
    
  (* Equation Systems *)
  Record equation_system : Type := Equation_system {
    eqs_substitutions : list substitution;
    eqs_equations     : list equation
  }.

  Definition height_equation_system (eqs : equation_system) : nat :=
    max (height (eqs_substitutions eqs)) (height (eqs_equations eqs)).
  Lemma is_height_zero_equation_system : is_height_zero_spec height_equation_system.
  Proof.
    hnf.
    destruct a.
    case (is_height_zero eqs_substitutions0).
    case (is_height_zero eqs_equations0).
    left. unfold height_equation_system, eqs_substitutions, eqs_equations. rewrite e, e0. trivial.
    right. unfold height_equation_system, eqs_substitutions, eqs_equations. rewrite e. icase (height eqs_equations0).
    right. unfold height_equation_system, eqs_substitutions, eqs_equations. icase (height eqs_substitutions0); icase (height eqs_equations0).
  Qed.
  Instance heightable_equation_system : heightable equation_system :=
    Heightable height_equation_system is_height_zero_equation_system.

  Definition cheight_equation_system (ctx : context) (eqs : equation_system) : nat :=
    max (cheight ctx (eqs_substitutions eqs)) (cheight ctx (eqs_equations eqs)).
  Instance cheightable_equation_system : cheightable context equation_system :=
    Cheightable cheight_equation_system.  

  Definition eval_equation_system (ctx : context) (eqs : equation_system) : Prop :=
    eval ctx (eqs_substitutions eqs) /\ eval ctx (eqs_equations eqs).
  Instance evalable_equation_system : evalable context equation_system :=
    Evalable eval_equation_system.

  Definition vars_es (es : equation_system) : list var :=
    vars (eqs_substitutions es) ++ vars (eqs_equations es).
  Instance varsable_es : varsable equation_system var :=
   Varsable vars_es.
  Lemma unfold_fresh_equation_system: forall v sbsts eqns,
    fresh v (Equation_system sbsts eqns) <-> (fresh v sbsts /\ fresh v eqns).
  Proof.
    intros. unfold fresh, IN. simpl. unfold vars_es. simpl.
    split; repeat intro.
    split; intro; apply H; apply in_or_app; auto.
    apply in_app_or in H0. destruct H. icase H0.
  Qed.  

  Definition substitute_equation_system (v1 v2 : var) (eqs : equation_system) : equation_system :=
    match eqs with Equation_system sbsts eqns =>
      Equation_system (substitute v1 v2 sbsts) (substitute v1 v2 eqns)
    end.
  Instance proper_equation_system: proper var share equation_system.
  Proof.
    apply Proper with substitute_equation_system.
    destruct c. simpl height.
    unfold height_equation_system, eqs_substitutions, eqs_equations, substitute_equation_system.
    do 2 rewrite <- substitute_height. trivial.
    intros. destruct obj. unfold substitute_equation_system.
    rewrite unfold_fresh_equation_system in *. 
    destruct H. split; apply substitute_vars; auto.
    intros. destruct obj. unfold substitute_equation_system.
    rewrite unfold_fresh_equation_system in H. destruct H.
    simpl eval. unfold eval_equation_system, eqs_equations, eqs_substitutions.
    do 2 (rewrite <- (substitute_fresh rho); auto). tauto.
    intros. destruct obj. unfold substitute_equation_system.
    rewrite unfold_fresh_equation_system in H. destruct H.
    unfold cequiv. simpl eval. unfold eval_equation_system, eqs_equations, eqs_substitutions.
    generalize (change_unused _ _ H rho v) (change_unused _ _ H0 rho v). unfold cequiv. intros.
    rewrite H1, H2. tauto.
  Qed.

  (* Top level systems, with existentials (and maybe someday nonzeros) *)
  Record top_level : Type := Top_level {
    tl_equation_system  : equation_system;
    tl_exists           : list var;
    tl_nonzeros         : list var
  }.

  Definition height_top_level (tleqs : top_level) : nat :=
    height (tl_equation_system tleqs).
  Lemma is_height_zero_top_level : is_height_zero_spec height_top_level.
  Proof.
    hnf.
    intros.
    apply is_height_zero_equation_system.
  Qed.
  Instance heightable_top_level : heightable top_level :=
    Heightable height_top_level is_height_zero_top_level.

  Definition cheight_top_level (ctx : context)(tleqs : top_level) : nat :=
    max (cheight ctx (tl_equation_system tleqs)) (cheight ctx (tl_nonzeros tleqs)).
  Instance cheightable_top_level : cheightable context top_level :=
    Cheightable cheight_top_level.

  Definition eval_var_nz (ctx : context) (v : var) : Prop :=
   ctx v <> bot.
  Instance evalable_var_nz : evalable context var := Evalable eval_var_nz.

  Definition eval_top_level (ctx : context) (tleqs : top_level) : Prop :=
    exists ctx',
      [(tl_exists tleqs) => ctx'] ctx |= (tl_equation_system tleqs) /\
      [(tl_exists tleqs) => ctx'] ctx |= (tl_nonzeros tleqs).
  Instance evalable_top_level : evalable context top_level :=
    Evalable eval_top_level.

  Record top_es : Type := Top_es {
    tes_equation_system : equation_system;
    tes_exists          : list var
  }.
  Definition height_top_es (tes : top_es) : nat :=
    height (tes_equation_system tes).
  Lemma is_height_zero_top_es : is_height_zero_spec height_top_es.
  Proof.
   hnf.
   intros.
   apply is_height_zero_equation_system.
  Qed.
  Instance heightable_top_es : heightable top_es :=
    Heightable height_top_es is_height_zero_top_es.
  Definition cheight_top_es (ctx : context)(tes : top_es) : nat :=
    cheight ctx (tes_equation_system tes).
  Instance cheightable_top_es : cheightable context top_es :=
    Cheightable cheight_top_es.
  Definition eval_top_es (ctx : context) (tes : top_es) : Prop :=
    exists ctx',
      [(tes_exists tes) => ctx'] ctx |= (tes_equation_system tes).
  Instance evalable_top_es : evalable context top_es :=
    Evalable eval_top_es.

  Definition tl2tes (tl : top_level) : top_es := 
   Top_es (tl_equation_system tl) (tl_exists tl).

  Definition eval_top_level_bounded (ctx : context) (btleqs : (top_level*nat)) : Prop :=
   exists ctx',
      match btleqs with (tleqs,n) =>
      cheight ctx' tleqs <= n /\
      [(tl_exists tleqs) => ctx'] ctx |= (tl_equation_system tleqs) /\
      [(tl_exists tleqs) => ctx'] ctx |= (tl_nonzeros tleqs)
      end.
  Instance evalable_top_level_bounded : evalable context (top_level*nat) :=
    Evalable eval_top_level_bounded.
     

(*
  Instance evalable_top_level : evalable context top_level :=
    Evalable eval_top_level.

  Record ntop_level : Type := NTop_level {
    ntl_tl : top_level;
    ntl_nonzeros : list var
  }.

  Definition height_ntop_level (ntleqs : ntop_level) : nat :=
    height (ntl_tl ntleqs).
  Lemma is_height_zero_ntop_level : is_height_zero_spec height_ntop_level.
  Proof.
   hnf.
   intros.
   apply is_height_zero_top_level.
  Qed.
  Instance heightable_ntop_level : heightable ntop_level :=
    Heightable height_ntop_level is_height_zero_ntop_level.
  Definition cheight_ntop_level (ctx : context)(ntleqs : ntop_level) : nat :=
    max (cheight ctx (ntl_tl ntleqs)) (cheight ctx (ntl_nonzeros ntleqs)).
  Instance cheightable_ntop_level : cheightable context ntop_level :=
    Cheightable cheight_ntop_level.  
  Definition eval_nonzeros (ctx : context)(nl : list var) : Prop :=
    fold_right (fun (v : var)(P : Prop)  => P /\ ~(ctx v = bot)) True nl.
  Instance evalable_nonzeros : evalable context (list var) :=
    Evalable eval_nonzeros.
  Definition eval_ntop_level (ctx : context) (ntleqs : ntop_level) : Prop :=
    eval ctx (ntl_tl ntleqs) /\ eval ctx (ntl_nonzeros ntleqs).
  Instance evalable_ntop_level : evalable context ntop_level :=
    Evalable eval_ntop_level.
*)
End Internal_Equation_System.

*)