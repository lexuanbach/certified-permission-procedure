(* A finite partial maps interface and implmentation in Coq.
   Largely copied from the Coq Std Lib, Msets
   - C.E. Sally, Aquinas Hobor *)

Require Import MMapInterface Utf8.
Require Export OrdersFacts NArith Bool.

Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.


Module Type InfoTyp.
  Parameter t : Set.
End InfoTyp.

(*******		****** 80 character ruler ******		*******)
Module Type Ops (Info:InfoTyp)(Keys:OrderedType).
Include KvpRelations Keys.

Definition key := Keys.t.			Notation kcmp := Keys.compare.

Inductive tree (value:Type) : Type :=
  | E : tree value
  | N : Info.t → tree value → key → value → tree value → tree value.

Definition map_of := @tree.

  Section Vals1.
   Context {val : Type}.

  Notation kvp  := (prod key val).

  Fixpoint min_elt t : option kvp :=
    match t with
    | E           => None
    | N _ E k v _ => Some (k, v)
    | N _ l _ _ _ => min_elt l
    end.

  Fixpoint max_elt t : option kvp :=
    match t with
    | E           => None
    | N _ _ k v E => Some (k, v)
    | N _ _ _ _ r => max_elt r
    end.

Fixpoint mem x (t:@tree val) :=
  match t with
  | N _ l k _ r => match kcmp x k with
                   | Eq => true
                   | Lt => mem x l
                   | Gt => mem x r
                   end
  | _ => false
  end.

(* this is here because Coq appears to be a little buggy generating Functional
   Schemes for min/max _elt when [tree] has implicit arguments *)
  Functional Scheme min_elt_ind := Induction for min_elt Sort Prop.
  Functional Scheme max_elt_ind := Induction for max_elt Sort Prop.

  End Vals1.


Arguments tree {value}.
Arguments E {value}.
Arguments N {value} _ _ _ _ _.


  Section Vals2.
   Context {val val' : Type}.
Notation kvp   := (prod key val).	Notation lkvp := (list kvp).
Notation mv    := (map_of val).		Notation mv'  := (map_of val').

Definition empty : mv := E.

Fixpoint update x y t : mv :=
  match t with
  | E => t
  | N c l k v r => match kcmp x k with
                   | Eq => N c l k y r
                   | Lt => N c (update x y l) k v r
                   | Gt => N c l k v (update x y r)
                   end
  end.

Definition is_empty (t:mv) := if t then true else false.



Fixpoint find x (t:mv) :=
  match t with
  | E           => None
  | N _ l k v r => match kcmp x k with
                   | Eq => Some v
                   | Lt => find x l
                   | Gt => find x r
                   end
  end.

Local Open Scope lazy_bool_scope.


Fixpoint subsetl (subset_l1: tree → bool) k1 (t2:mv') : bool :=
  match t2 with
  | E             => false
  | N _ l k2 _ r => match kcmp k1 k2 with
                     | Eq => subset_l1 l
                     | Lt => subsetl subset_l1 k1 l
                     | Gt => mem k1 r &&& subset_l1 t2
                     end
  end.

Fixpoint subsetr (subset_r1: tree → bool) k1 (t2:mv') : bool :=
  match t2 with
  | E             => false
  | N _ l k2 v2 r => match kcmp k1 k2 with
                     | Eq => subset_r1 r
                     | Lt => mem k1 l &&& subset_r1 t2
                     | Gt => subsetr subset_r1 k1 r
                     end
  end.

Fixpoint subset (t1:mv) (t2:mv') : bool :=
  match t1, t2 with
  | E          , _ => true
  | N _ _ _ _ _, E => false
  | N _ l1 k1 _ r1, N _ l2 k2 _ r2 =>
      match kcmp k1 k2 with
      | Eq => subset l1 l2 &&& subset r1 r2
      | Lt => subsetl (subset l1) k1 l2 &&& subset r1 t2
      | Gt => subsetr (subset r1) k1 r2 &&& subset l1 t2
      end
  end.

Inductive enumeration :=
| End : enumeration
| More : key → mv' → enumeration → enumeration.

Fixpoint econs (t:mv') e : enumeration :=
  match t with
  | E           => e
  | N _ l k _ r => econs l (More k r e)
  end.

(*
Local Notation cb := (prod comparison  bool).
Local Notation eb := (prod enumeration bool).
Local Notation vvb := (val → val → bool).
*)

Local Notation comp := comparison.
Local Notation enum := enumeration.


Definition compare_more k1 (cont: enum → comp) (e2:enum) :=
  match e2 with
  | End              => Gt
  | More k2 r2 e2 => match kcmp k1 k2 with
                     | Eq => cont (econs r2 e2)
                     | Lt => Lt
                     | Gt => Gt
                     end
  end.

Fixpoint compare_cont (m1:mv) (cont: enum → comp) e2 :=
  match m1 with
  | E           => cont e2
  | N _ l k _ r =>
    compare_cont l (compare_more k (compare_cont r cont)) e2
  end.

Definition compare_end (e2 : enum) := if e2 then Eq else Lt.

Definition compare (m:mv) (m':mv') :=
  compare_cont m compare_end (econs m' End).


Inductive enum_ :=
| End_ : enum_
| More_ : key → val' → mv' → enum_ → enum_.

Fixpoint econs_ (t:mv') e : enum_ :=
  match t with
  | E           => e
  | N _ l k v r => econs_ l (More_ k v r e)
  end.

Definition equal_more k1 v1 (cmp:val→val'→bool) (cont: enum_ → bool) (e2:enum_) :=
  match e2 with
  | End_              => false
  | More_ k2 v2 r2 e2 => match kcmp k1 k2 with
                         | Eq => if cmp v1 v2 then cont (econs_ r2 e2) else false
                         | Lt => false
                         | Gt => false
                         end
  end.

Fixpoint equal_cont (m1:mv) cmp (cont: enum_ → bool) e2 :=
  match m1 with
  | E           => cont e2
  | N _ l k v r  =>
    equal_cont l cmp (equal_more k v cmp (equal_cont r cmp cont)) e2
  end.

Definition equal_end (e2 : enum_) := if e2 then true else false.

Definition equal cmp (m:mv) (m':mv') :=
  equal_cont m cmp equal_end (econs_ m' End_).


Fixpoint for_all (f: key → val → bool) t :=
  match t with
  | E           => true
  | N _ l k v r => f k v &&& for_all f l &&& for_all f r
  end.

Fixpoint exists_ (f: key → val → bool) t :=
  match t with
  | E           => false
  | N _ l k v r => f k v ||| exists_ f l ||| exists_ f r
  end.
Local Close Scope lazy_bool_scope.

Fixpoint cardinal (m:mv) :=
  match m with
  | E => O
  | N _ l k v r  => S (cardinal l + cardinal r)
  end.


Fixpoint elements_aux (acc : list kvp) t :=
  match t with
  | E => acc
  | N _ l k v r => elements_aux ((k,v) :: elements_aux acc r) l
  end.

Definition elements := elements_aux nil.

Fixpoint rev_elements_aux (acc : list kvp) t :=
  match t with
  | E => acc
  | N _ l k v r => rev_elements_aux ((k,v) :: rev_elements_aux acc l) r
  end.

Definition rev_elements := rev_elements_aux nil.


Fixpoint kelements_aux (acc : list key) (t:mv) :=
  match t with
  | E => acc
  | N _ l k _ r => kelements_aux (k :: kelements_aux acc r) l
  end.

Definition kelements := kelements_aux nil.

Fixpoint rev_kelements_aux (acc : list key) (t:mv) :=
  match t with
  | E => acc
  | N _ l k _ r => rev_kelements_aux (k :: rev_kelements_aux acc l) r
  end.

Definition rev_kelements := rev_kelements_aux nil.


Fixpoint foldl {A:Type} (f: key → val → A → A) t sd :=
  match t with
  | E => sd
  | N _ l k v r => foldl f r (f k v (foldl f l sd))
  end.

Fixpoint foldr {A: Type} (f: key → val → A → A) t (sd: A) : A :=
  match t with
  | E           => sd
  | N _ l k v r => foldr f l (f k v (foldr f r sd))
  end.

Definition fone {A:Type} (f: key → val → A → A) k v cont sd : A :=
  cont (f k v sd).

Fixpoint fleft {A: Type} (f: key → val → A → A) t cont (sd: A) : A :=
  match t with
  | E => cont sd
  | N _ E k v r => (fleft f r cont) (f k v sd)
  | N _ l k v r => fleft f l (fone f k v (fleft f r cont)) sd
  end.

Definition foldl_cps {A} f t sd := @fleft  A f t (@id A) sd.

Fixpoint fright {A: Type} (f: key → val → A → A) t cont (sd: A) : A :=
  match t with
  | E => cont sd
  | N _ l k v E => (fright f l cont) (f k v sd)
  | N _ l k v r => fright f r (fone f k v (fleft f l cont)) sd
  end.

Definition foldr_cps {A} f t sd := @fright  A f t (@id A) sd.

Definition     elements_cps t := foldr_cps (λ k v L, (k,v) :: L) t nil.
Definition rev_elements_cps t := foldl_cps (λ k v L, (k,v) :: L) t nil.
Definition kelements_cps t := foldr_cps (λ k _ L, k :: L) t nil.


Fixpoint map (f : val → val') (t : mv) : mv' :=
  match t with
  | E => @E val'
  | N c l x y r => N c (map f l) x (f y) (map f r)
  end.


Fixpoint mapi (f : key → val → val') (t : mv) : mv' :=
  match t with
  | E => @E val'
  | N c l x y r => N c (mapi f l) x (f x y) (mapi f r)
  end.


Definition choose := (@min_elt val).

  End Vals2.

End Ops.






























Module Type Props (X:OrderedType)(Info:InfoTyp)(Import M:Ops Info X).
Notation keq  := X.eq.				Notation klt := X.lt.
Notation keqd := X.eq_dec.

Module Import MX := OrderedTypeFacts X.
Hint Resolve MX.eq_refl MX.eq_trans MX.lt_trans.
Hint Immediate MX.eq_sym.

Module L := MMapInterface.MakeListOrdering X.

Ltac clear_inversion H := inversion H; clear H; subst.
Ltac gen_in x := generalize x; intro.

Arguments tree {value}.
Arguments E {value}.
Arguments N {value} _ _ _ _ _.

Section Vals1.
 Context {val : Type}.
 Notation mv   := (map_of val).
 Notation kvp := (prod key val).
 Notation lkvp := (list kvp).
 Notation okvp := (option kvp).
 Notation kvpeq := (Kvpeq val).
 Notation kvplt := (Kvplt val).
 Notation E' := (@E val).
 Instance kvp_eq_lt_comp : Proper (kvpeq==> kvpeq ==> iff) kvplt.
 Proof. refine (@Kvpeq_compat val). Qed.
 Instance kvpEQ : Equivalence kvpeq. Proof. exact (@Kvpeq_equiv val). Qed.
 Instance kvpLT : StrictOrder kvplt. Proof. exact(@Kvplt_strord val). Qed.

Inductive MaT (x : key) (y : val) : mv → Prop :=
  | mRoot  : ∀ c l k r  , keq x k → MaT x y (N c l k y r)
  | mLeft  : ∀ c l k v r, MaT x y l → MaT x y (N c l k v r)
  | mRight : ∀ c l k v r, MaT x y r → MaT x y (N c l k v r).

Inductive InT (x : key) : mv → Prop :=
  | InRoot  : ∀ c l k v r, keq x k → InT x (N c l k v r)
  | InLeft  : ∀ c l k v r, InT x l → InT x (N c l k v r)
  | InRight : ∀ c l k v r, InT x r → InT x (N c l k v r).

Definition MapsTo := MaT.
Definition In k m := ∃v, MapsTo k v m.

Definition Empty       m          := ∀ k v, ¬ MapsTo k v m.
Definition Equal       m m'       := ∀ k v, MapsTo k v m ↔ MapsTo k v m'.
Definition SameKeys    m m'       := ∀ k  , In k m ↔ In k m'.
Definition Restriction m m'       := ∀ k v, MapsTo k v m → MapsTo k v m'.
Definition For_all (P:_→_→Prop) m := ∀ k v, MapsTo k v m → P k v.
Definition Exists  (P:_→_→Prop) m := ∃ k v, MapsTo k v m ∧ P k v.

Notation "s [=] t"   := (Equal s t)       (at level 70, no associativity).
Notation "s [|<=] t" := (Restriction s t) (at level 70, no associativity).
Notation compatb := (Proper (keq==>Logic.eq==>Logic.eq)) (only parsing).
(*Declare Instance eq_equiv : Equivalence Equal.*)


Definition lt_tree k t := ∀ x, InT x t → klt x k.
Definition gt_tree k t := ∀ x, InT x t → klt k x.

Inductive bst : mv → Prop :=
  | BSE : bst E
  | BSN : ∀ c x y l r, bst l → bst r →
      lt_tree x l → gt_tree x r → bst (N c l x y r).

Definition IsOk := bst.

Class Ok (t:mv) : Prop := ok : bst t.

Instance bst_Ok t (Ht : bst t) : Ok t := { ok := Ht }.

Fixpoint ltb_tree x (t:mv) :=
 match t with
  | E => true
  | N _ l k v r =>
     match kcmp x k with
      | Gt => ltb_tree x l && ltb_tree x r
      | _  => false
     end
 end.

Fixpoint gtb_tree x (t:mv) :=
 match t with
  | E => true
  | N _ l k v r =>
     match kcmp x k with
      | Lt => gtb_tree x l && gtb_tree x r
      | _  => false
     end
 end.

Fixpoint isok t :=
 match t with
  | E => true
  | N _ l k _ r => isok l && isok r && ltb_tree k l && gtb_tree k r
 end.

Scheme tree_ind := Induction for tree Sort Prop.
Scheme bst_ind := Induction for bst Sort Prop.


Hint Constructors MaT InT bst.
Hint Unfold lt_tree gt_tree MapsTo In Ok.
Hint Resolve @ok.

Lemma k_kvp_eq x y: keq (fst x) (fst y) -> (snd x) = (snd y) -> kvpeq x y.
Proof. now destruct x, y; split; simpl in *. Qed.
Lemma k_kvp_eq' x y x' y' : keq x x' -> y = y' -> kvpeq (x,y) (x',y').
Proof. now split; simpl. Qed.
Lemma kvp_k_eq_f x y : kvpeq x y -> keq (fst x) (fst y).
Proof. now destruct x, y; destruct 1. Qed.
Lemma kvp_k_eq_f' x y x' y' : kvpeq (x,y) (x',y') -> keq x x'.
Proof. now destruct 1. Qed.
Lemma kvp_k_eq_s x y : kvpeq x y -> (snd x) = (snd y).
Proof. now destruct x, y; destruct 1. Qed.
Lemma kvp_k_eq_s' x y x' y' : kvpeq (x,y) (x',y') -> y = y'.
Proof. now destruct 1. Qed. Hint Resolve k_kvp_eq k_kvp_eq'
kvp_k_eq_f kvp_k_eq_f' kvp_k_eq_s kvp_k_eq_s'.


Ltac inv_ok := match goal with
 | H:Ok (N _ _ _ _ _) |- _ => clear_inversion H; inv_ok
 | H:Ok E |- _ => clear H; inv_ok
 | H:bst ?x |- _ => change (Ok x) in H; inv_ok
 | _ => idtac
end.

Ltac inv_MaT := match goal with
 | H:MapsTo ?a ?b E  |- _ => inversion H
 | H:MapsTo ?a ?b ?x |- _ => change (MaT a b x) in H; inv_MaT
 | H:In _ _ |- _ => destruct H; inv_MaT
 | _ => idtac
end.

Ltac is_tree_constr c :=
  match c with
   | E => idtac
   | N _ _ _ _ _ => idtac
   | _ => fail
  end.

Ltac invtree f :=
  match goal with
     | H:f ?s |- _ => is_tree_constr s; clear_inversion H; invtree f
     | H:f _ ?s |- _ => is_tree_constr s; clear_inversion H; invtree f
     | H:f _ _ ?s |- _ => is_tree_constr s; clear_inversion H; invtree f
     | _ => idtac
  end.

Ltac inv := inv_MaT; invtree MaT; inv_ok; invtree InT.

Ltac intuition_in := repeat progress ((intuition; inv) || subst).

Lemma InInT x m : In x m ↔ InT x m.
Proof with eauto.
  induction m; intuition_in;
  invtree In...
Qed.
Ltac rwiit := rewrite InInT.
Tactic Notation "rwiit" "in" hyp(h) := rewrite InInT in h.
Ltac rwiti := rewrite <- InInT.
Tactic Notation "rwiti" "in" hyp(h) := rewrite <- InInT in h.

Lemma In_InT x m : In x m → InT x m.
Proof. exact (proj1 (InInT x m)). Qed.

Lemma InT_In x m : InT x m → In x m.
Proof. exact (proj2 (InInT x m)). Qed.
Hint Resolve In_InT InT_In.

Ltac InCon1 := rwiit; constructor 1.
Ltac InCon2 := rwiit; constructor 2; rwiti.
Ltac InCon3 := rwiit; constructor 3; rwiti.


Lemma Mt2It x y m : MaT x y m → InT x m.
Proof. intros. rwiti. now exists y. Qed.

Lemma It2Mt x m: InT x m → ∃ y, MaT x y m.
Proof. intros. now rwiti in H. Qed.
Hint Resolve Mt2It It2Mt.

Ltac order := match goal with
 | U: lt_tree _ ?t, V: InT _ ?t |- _ => specialize (U _ V); order
 | U: lt_tree _ ?t, V: MaT _ _ ?t |- _ =>
   specialize (U _ (Mt2It _ _ _ V)); order
 | U: gt_tree _ ?t, V: InT _ ?t |- _ => specialize (U _ V); order
 | U: gt_tree _ ?t, V: MaT _ _ ?t |- _ =>
   specialize (U _ (Mt2It _ _ _ V)); order
 | U: (forall _, InT _ ?t -> _),  V: InT _ ?t |- _
   => specialize (U _ V); order
 | _ => MX.order
end.

Ltac inn :=
  match goal with
   | H:MaT ?a ?b ?t |- MaT ?a ?b (N _ ?t _ _ _) => constructor 2; inn
   | H:MaT ?a ?b ?t |- MaT ?a ?b (N _ _ _ _ ?t) => constructor 3; inn
   | H:MaT ?a ?b _  |- MaT ?a ?b (N _ _ ?a ?b _) => constructor 1; inn
   | _ => auto;eauto
end.

Ltac intuition_inn := repeat progress (intuition; inv); inn.

Lemma ltb_tree_iff : ∀ x t, lt_tree x t ↔ ltb_tree x t = true.
Proof with order.
  induction t as [|c l IHl k v r IHr]; simpl.
  - unfold lt_tree; intuition_in.
  - elim_compare x k.
    + split; [intros|discriminate].
      assert (klt k x) by auto...
    + split; [intros|discriminate].
      assert (klt k x) by auto...
    + rewrite !andb_true_iff, <-IHl, <-IHr;
      unfold lt_tree; intuition_in...
Qed.


Lemma gtb_tree_iff : ∀ x t, gt_tree x t ↔ gtb_tree x t = true.
Proof with order.
  induction t as [|c l IHl k v r IHr]; simpl.
  - unfold gt_tree; intuition_in.
  - elim_compare x k.
    + split; [intros|discriminate].
      assert (klt x k) by auto...
    + rewrite !andb_true_iff, <-IHl, <-IHr;
      unfold gt_tree; intuition_in...
    + split; [intros|discriminate].
      assert (klt x k) by auto...
Qed.

Lemma isok_iff : ∀ t, Ok t ↔ isok t = true.
Proof with intuition_in.
  induction t as [|c l IHl k v r IHr]; simpl.
  - idtac...
  - rewrite !andb_true_iff, <- IHl, <-IHr,
    <- ltb_tree_iff, <- gtb_tree_iff...
Qed.

Instance isok_Ok s : isok s = true -> Ok s | 10.
Proof. now intros; apply <- isok_iff. Qed.

Lemma kcLt {a b} : klt a b → kcmp a b = Lt.
Proof. now elim_compare a b; try order. Qed.
Lemma kcEq {a b} : keq a b → kcmp a b = Eq.
Proof. now elim_compare a b; try order. Qed.
Lemma kcGt {a b} : klt b a → kcmp a b = Gt.
Proof. now elim_compare a b; try order. Qed.

Lemma MapsTo_spec1' a x y m :
  keq a x → MaT a y m → MaT x y m.
Proof.
  induction m; intuition_in.
  constructor; order.
Qed.

Definition MapsTo_spec1 a x y m `{Ok m} := MapsTo_spec1' a x y m.
Hint Resolve MapsTo_spec1 MapsTo_spec1'.

Lemma MapsTo_spec2 x y z m `{Ok m} :
MapsTo x y m → MapsTo x z m → y = z.
Proof. induction m; intuition_in; order.
Qed. Hint Resolve MapsTo_spec2.


Lemma It_1 m x y : keq x y → InT x m → InT y m.
Proof. induction m; intuition_in;
eauto. Qed. Hint Resolve It_1.

Instance Mt_compat : Proper (keq==>Logic.eq==>Logic.eq==>iff) MaT.
Proof.
  intros x x' Hx y y' Hy m1 m2 Hm;
  intuition_in; [|
  symmetry in Hx]; eauto.
Qed.

Lemma Mt_compat' a b k v c l r : kvpeq (a,b) (k,v) → (MaT a b (N c l k v r)).
Proof.
  destruct 1; simpl in *;
  rewrite H, H0. auto.
Qed. Hint Resolve Mt_compat'.

Instance It_compat : Proper (keq==>Logic.eq==>iff) InT.
Proof with auto.
  intros x x' Hx m m' Hm.
  rewrite Hm. split; apply It_1...
Qed. Hint Resolve Mt_compat It_compat.


Lemma Mt_node_iff c l k v r x y :
  MaT x y (N c l k v r) ↔ MaT x y l ∨ keq x k ∧ y = v ∨ MaT x y r.
Proof. intuition_in. Qed.

Lemma Mt_leaf_iff x y :
MaT x y E ↔ False.
Proof. intuition_in. Qed.

Lemma It_node_iff c l k v r x :
  InT x (N c l k v r) ↔ InT x l ∨ keq x k ∨ InT x r.
Proof. intuition_in. Qed.

Lemma It_leaf_iff x :
InT x E ↔ False.
Proof. intuition_in. Qed.
Hint Resolve Mt_node_iff Mt_leaf_iff It_node_iff It_leaf_iff.


(** Results about [lt_tree] and [gt_tree] *)

Lemma lt_leaf x : lt_tree x E.
Proof. red; inversion 1. Qed.

Lemma gt_leaf x: gt_tree x E.
Proof. red; inversion 1. Qed.

Lemma lt_tree_node x k v l r i :
lt_tree x l → lt_tree x r → klt k x → lt_tree x (N i l k v r).
Proof. unfold lt_tree; intuition_in; try order. Qed.

Lemma gt_tree_node x k v l r i :
gt_tree x l → gt_tree x r → klt x k → gt_tree x (N i l k v r).
Proof. unfold gt_tree; intuition_in; order. Qed.
Hint Resolve lt_leaf gt_leaf lt_tree_node gt_tree_node.


Lemma lt_left x c l k v r :
 lt_tree x (N c l k v r) → lt_tree x l.
Proof. intuition_in. Qed.

Lemma lt_right x c l k v r :
 lt_tree x (N c l k v r) → lt_tree x r.
Proof. intuition_in. Qed.

Lemma gt_left x c l k v r :
 gt_tree x (N c l k v r) → gt_tree x l.
Proof. intuition_in. Qed.

Lemma gt_right x c l k v r :
 gt_tree x (N c l k v r) → gt_tree x r.
Proof. intuition_in. Qed.

Lemma lt_tree_not_in x t :
  lt_tree x t → ¬InT x t.
Proof. repeat intro; order. Qed.

Lemma lt_tree_trans x x' :
klt x x' → forall t, lt_tree x t → lt_tree x' t.
Proof. eauto. Qed.

Lemma gt_tree_not_in x t :
  gt_tree x t → ¬InT x t.
Proof. repeat intro; order. Qed.

Lemma gt_tree_trans x x' :
  klt x' x → forall t, gt_tree x t → gt_tree x' t.
Proof. eauto. Qed.

Instance lt_tree_compat : Proper (keq ==> Logic.eq ==> iff) lt_tree.
Proof.
  apply proper_sym_impl_iff_2; auto.
  intros x x' Hx s s' Hs H k H0; subst.
  order.
Qed.

Instance gt_tree_compat : Proper (keq ==> Logic.eq ==> iff) gt_tree.
Proof.
  apply proper_sym_impl_iff_2; auto.
  intros x x' Hx s s' Hs H k H0; subst.
  order.
Qed.

Hint Resolve
lt_tree_not_in lt_tree_trans
gt_tree_not_in gt_tree_trans
lt_left lt_right lt_tree_compat
gt_left gt_right gt_tree_compat.


Ltac induct s x :=
 induction s as [|i l IHl x' y' r IHr]; simpl; intros;
 [|elim_compare x x'; intros; inv].

Ltac auto_tc := auto with typeclass_instances.

Ltac ok :=
 inv; change bst with Ok in *;
 match goal with
   | |- Ok (N _ _ _ _ _) => constructor; auto_tc; ok
   | |- lt_tree _ (N _ _ _ _ _) => apply lt_tree_node; ok
   | |- gt_tree _ (N _ _ _ _ _) => apply gt_tree_node; ok
   | _ => eauto with typeclass_instances
 end.





(** ** Empty set *)

Theorem empty_spec : Empty E'.
Proof. inversion 1. Qed.
Hint Resolve empty_spec.

Instance empty_ok : Ok empty.
Proof. left. Qed.
Hint Immediate empty_ok.

Corollary empty_fact c l x y r : Empty (N c l x y r) → False.
Proof.
  unfold Empty. intro.
  apply (H x y). auto.
Qed. Hint Resolve empty_fact.



(** ** Emptyness test *)

Lemma is_empty_spec' m : is_empty m = true ↔ Empty m.
Proof with auto.
  destruct m as [|c r x y l]; simpl;
  split; auto; [discriminate|].
  intro H. destruct (H x y)...
Qed.
Definition is_empty_spec m `{Ok m} := is_empty_spec' m.



(** ** update *)

Lemma update_spec1 x y m `{Ok m} : In x m → MapsTo x y (update x y m).
Proof with eauto.
  intros. rwiit in H0.
  induct m x; intuition_in; order.
Qed.

Lemma update_spec2'' x y m : ¬In x m → (update x y m) = m.
Proof with eauto.
  intros. rwiit in H.
  induct m x; intuition_in.
  + destruct H...
  + rewrite H1...
  + rewrite H2...
Qed.

Lemma update_spec2' x y m : ¬In x m → (update x y m) [=] m.
Proof.
  intro. rewrite (update_spec2'' x y m); unfold Equal;
  intuition.
Qed.
Definition update_spec2 x y m `{Ok m} := update_spec2' x y m.

Corollary update_fact1 m a x y : InT a m ↔ InT a (update x y m).
Proof. induct m x; intuition_in. Qed.

Instance update_ok x y m `{Ok m}: Ok (update x y m).
Proof with order.
  induct m x; intuition_in; ok; intros a H';
  rewrite <- update_fact1 in H'...
Qed.

 Lemma update_spec3 a x b y (m : mv) `{Ok m}: 
  ¬keq a x → (MapsTo a b (update x y m) ↔ MapsTo a b m).
 Proof with eauto.
  intros. induct m x; intuition_in; order.
 Qed.

(** ** Membership *)

Theorem mem_spec x m `{Ok m} : mem x m = true ↔ In x m.
Proof.
  rwiit. induct m x;
  intuition_in; try discriminate; order.
Qed.

Scheme MaT_ind := Induction for MaT Sort Prop.



(** ** find *)
Lemma find_spec x y m `{Ok m} : find x m = Some y ↔ MapsTo x y m.
Proof.
  induct m x; intuition_in;
  try order. - inversion H0.
  - clear_inversion H. auto.
Qed.



(** ** Elements *)

Lemma elements_spec1'' m acc x y :
 InA kvpeq (x,y) (elements_aux acc m) ↔ MaT x y m ∨ InA kvpeq (x,y) acc.
Proof with auto.
  revert acc x y. induction m as
  [ | c l IHl k v r IHr ]; simpl; auto.
  - intuition. inversion H0.
  - intros. rewrite IHl. destruct (IHr acc x y).
    clear IHl IHr; intuition.
    + inversion_clear H3.
      * left...
      * destruct (H H0); [left|right]...
    + inversion_clear H3;
      [ right
      | left
      | right]...
Qed.

Lemma elements_spec1' x y m :
 InA kvpeq (x,y) (elements m) ↔ MapsTo x y m.
Proof.
  intros; generalize (elements_spec1'' m nil x y).
  intuition. inversion_clear H0.
Qed.
Definition elements_spec1 x y m `{Ok m} := elements_spec1' x y m.

Lemma elements_spec2' m acc `{Ok m} :
 Sorted kvplt acc →
 (∀ k k' : kvp, InA kvpeq k acc → InT (fst k') m → kvplt k' k) →
 Sorted kvplt (elements_aux acc m).
Proof with first [order | auto].
  revert acc H. induction m as
  [| c l IHl x y r IHr]; simpl;
  intuition. inv. apply IHl...
  - constructor 2.
    + apply IHr...
    + apply InA_InfA with (eqA:=kvpeq); eauto with *.
      intros (k,v) H.
      rewrite (elements_spec1'' r acc k v) in H.
      intuition. cbv...
  - intros (k,v) (k',v') H H2.
    inversion_clear H.
    + cbv. destruct H3. simpl in *...
    + rewrite (elements_spec1'' r acc k v) in H3.
      intuition...
Qed.

Theorem elements_spec2 m `{Ok m} : Sorted kvplt (elements m).
Proof with auto.
  unfold elements.
  now apply elements_spec2'.
Qed. Hint Immediate elements_spec2.

Theorem elements_spec3 m `(Ok m) :
 NoDupA kvpeq (elements m).
Proof.
  apply SortA_NoDupA with kvplt; auto_tc.
Qed.

Lemma elements_aux_cardinal : ∀ (m:mv) acc,
 (length acc + cardinal m)%nat = length (elements_aux acc m).
Proof.
  simple induction m; simpl; intuition.
  rewrite <- H. simpl. rewrite <- H0.
  now rewrite (Plus.plus_comm (cardinal t0)),
  <- (Plus.plus_assoc (length acc)),
  <- Plus.plus_Snm_nSm.
Qed.

Lemma elements_cardinal (m:mv) :
 cardinal m = length (elements m).
Proof.
 exact (elements_aux_cardinal m nil).
Qed.

Definition cardinal_spec (m:mv) `{Ok m} := elements_cardinal m.

Lemma elements_app (m:mv) acc :
 elements_aux acc m = elements m ++ acc.
Proof with auto.
  revert acc. induction m; simpl; intros...
  rewrite IHm1, IHm2. unfold elements; simpl.
  now rewrite 2 IHm1, IHm2, !app_nil_r, !app_ass.
Qed.

Lemma elements_node c l x (y:val) r :
 elements (N c l x y r) = elements l ++ (x,y) :: elements r.
Proof.
  unfold elements; simpl. now
  rewrite !elements_app, !app_nil_r.
Qed.

Lemma rev_elements_app (m:mv) acc :
 rev_elements_aux acc m = rev_elements m ++ acc.
Proof with auto.
  revert acc. induction m; simpl; intros...
  rewrite IHm1, IHm2. unfold rev_elements; simpl.
  rewrite IHm1, 2 IHm2, !app_nil_r, !app_ass...
Qed.

Lemma rev_elements_node c l x (y:val) r :
 rev_elements (N c l x y r) = rev_elements r ++ (x,y) :: rev_elements l.
Proof.
  unfold rev_elements; simpl. now
  rewrite !rev_elements_app, !app_nil_r.
Qed.

Lemma rev_elements_rev (m:mv) : rev_elements m = rev (elements m).
Proof with auto.
  induction m as [|c l IHl x y r IHr]...
  rewrite elements_node, rev_elements_node, IHl, IHr, rev_app_distr.
  simpl. rewrite !app_ass...
Qed.


Lemma elements_rev_elements x y m :
InA kvpeq (x,y) (elements m) ↔ InA kvpeq (x,y) (rev_elements m).
Proof with auto.
  rewrite rev_elements_rev,
  InA_rev... tauto.
Qed.


(** ** Kelements *)

Lemma kelements_spec1'' m acc x :
 InA keq x (kelements_aux acc m) ↔ InT x m ∨ InA keq x acc.
Proof with auto.
  revert acc x. induction m as
  [ | c l IHl k v r IHr ]; simpl...
  - intuition. inv.
  - intros. rewrite IHl. destruct (IHr acc x).
    clear IHl IHr; intuition.
    + inversion_clear H3.
      * left...
      * destruct (H H0); [left|right]...
    + inversion_clear H3;
      [ right
      | left
      | right]...
Qed.

Lemma kelements_spec1' x m :
 InA keq x (kelements m) ↔ In x m.
Proof.
  intros; generalize (kelements_spec1'' m nil x).
  rwiti. intuition. inversion_clear H0.
Qed.
Definition kelements_spec1 x m `{Ok m} := kelements_spec1' x m.

Lemma kelements_spec2' m acc `{Ok m} :
 Sorted klt acc → (∀ k k', InA keq k acc → InT k' m → klt k' k)
 → Sorted klt (kelements_aux acc m).
Proof with first [order | auto].
  revert acc H. induction m as
  [| c l IHl x y r IHr]; simpl;
  intuition. inv. apply IHl...
  - constructor 2; [apply IHr|]...
    eapply InA_InfA; eauto with *.
    intros k H. rewrite
    (kelements_spec1'' r acc k) in H.
    intuition.
  - intros k k' H H2. inversion_clear H...
    rewrite (kelements_spec1'' r acc k) in H3.
    intuition...
Qed.

Theorem kelements_spec2 m `{Ok m} : Sorted klt (kelements m).
Proof with auto.
  unfold elements. now apply kelements_spec2'.
Qed. Hint Immediate kelements_spec2.

Theorem kelements_spec3 m `(Ok m) :
 NoDupA keq (kelements m).
Proof.
  apply SortA_NoDupA with klt; auto_tc.
Qed.

Lemma kelements_app (m:mv) acc :
 kelements_aux acc m = kelements m ++ acc.
Proof with auto.
  revert acc. induction m; simpl; intros...
  rewrite IHm1, IHm2. unfold kelements; simpl.
  now rewrite !IHm1, IHm2, !app_nil_r, !app_ass.
Qed.

Lemma kelements_node c l x (y:val) r :
 kelements (N c l x y r) = kelements l ++ x :: kelements r.
Proof.
  unfold kelements; simpl. now
  rewrite !kelements_app, !app_nil_r.
Qed.

Lemma rev_kelements_app (m:mv) acc :
 rev_kelements_aux acc m = rev_kelements m ++ acc.
Proof with auto.
  revert acc. induction m; simpl; intros...
  rewrite IHm1, IHm2. unfold rev_kelements; simpl.
  rewrite !IHm1, !IHm2, !app_nil_r, !app_ass...
Qed.


Lemma rev_kelements_node c l x (y:val) r :
 rev_kelements (N c l x y r) = rev_kelements r ++ x :: rev_kelements l.
Proof.
  unfold rev_kelements; simpl. now
  rewrite !rev_kelements_app, !app_nil_r.
Qed.

Notation mapfst := (List.map (@fst key val)).
Lemma kele_mfele m :
kelements m = mapfst (elements m).
Proof with auto.
  unfold elements, kelements.
  induction m; simpl...
  rewrite elements_app, kelements_app.
  unfold elements, kelements.
  rewrite map_app; simpl;
  rewrite IHm1, IHm2...
Qed.

Lemma rev_kelements_rev (m:mv) : rev_kelements m = rev (kelements m).
Proof with auto.
  induction m as [|c l IHl x y r IHr]...
  rewrite kelements_node, rev_kelements_node, IHl,
  IHr, rev_app_distr; simpl; rewrite !app_ass...
Qed.

Lemma for_all_spec' m P : Proper (keq ==> eq ==> eq) P →
  (for_all P m = true ↔ For_all (λ x y, P x y = true) m).
Proof with auto.
  intros Hf; unfold For_all.
  induction m as [| i l IHl x' y' r IHr]; simpl.
  - intuition_in.
  - rewrite <- !andb_lazy_alt, !andb_true_iff,
    IHl, IHr. intuition_in.
    rewrite H8...
Qed.
Definition for_all_spec m P `{Ok m} := for_all_spec' m P.

Lemma exists__spec' m P : Proper (keq ==>Logic.eq ==>Logic.eq) P →
  (exists_ P m = true ↔ Exists (λ x y, P x y = true) m).
Proof with auto.
  intros Hf; unfold Exists.
  induction m as [| i l IHl x' y' r IHr]; simpl.
  - split; [intros H | intros (x&y&H&_)];
    inversion H.
  - rewrite <- !orb_lazy_alt, !orb_true_iff,
    IHl, IHr. clear IHl IHr. split;
    [ intros [[H|(x&y&H&H')]|(x&y&H&H')] 
    | intros (x&y&H&H')
    ]. + exists x', y'...
    + exists x, y...
    + exists x, y...
    + inv;
      [ left;left
      | left;right
      | right]; eauto.
      rewrite <- H1...
Qed.
Definition exists__spec m P `{Ok m} := exists__spec' m P.


(*"flipped uncurry", not "function"*)
Notation func := (compose flip prod_curry).
Lemma foldl_spec'_aux (m:mv) {X} f (sd:X) acc :
  fold_left (func f) (elements_aux acc m) sd =
  fold_left (func f) acc (foldl f m sd).
Proof.
  revert sd acc. induction m as [| c l IHl k v r IHr];
  simpl; intros; auto. rewrite IHl. simpl. apply IHr.
Qed.

Lemma foldl_spec' (m:mv) {X} f (sd:X) :
  foldl f m sd = fold_left (func f) (elements m) sd.
Proof with auto.
  revert sd. unfold elements. induction m
  as [| c l IHl k v r IHr]; simpl; intros...
  rewrite foldl_spec'_aux, IHr. simpl...
Qed.

Definition foldl_spec (m:mv) {X} f sd `{Ok m}
  := @foldl_spec' m X f sd.


Notation unc := prod_curry.
Lemma foldr_spec'_aux (m:mv) {X} f (sd:X) acc :
foldr f m (fold_right (unc f) sd acc) =
fold_right (unc f) sd (elements_aux acc m).
Proof with auto.
  revert sd acc. induction m as
  [| c l IHl k v r IHr]; simpl;
  intros... rewrite <- IHl.
  simpl. rewrite IHr...
Qed.

Lemma foldr_spec'_aux_byleft (m:mv) {X} f (sd:X) acc :
  fold_left (func f) (rev_elements_aux acc m) sd =
  fold_left (func f) acc (foldr f m sd).
Proof.
  revert sd acc. induction m as [| c l IHl k v r IHr];
  simpl; intros; auto. rewrite IHr. simpl. apply IHl.
Qed.

Lemma foldr_spec'_byleft (m:mv) {X} f (sd:X) :
  foldr f m sd = fold_left (func f) (rev_elements m) sd.
Proof with auto.
  revert sd. unfold rev_elements. induction m as
  [| c l IHl k v r IHr]; simpl; intros... rewrite
  foldr_spec'_aux_byleft. rewrite IHr. simpl...
Qed.

Lemma foldr_spec' (m:mv) {X} f (sd:X) :
  foldr f m sd = fold_right (unc f) sd (elements m).
Proof with auto.
(*
  rewrite <- (rev_involutive (elements m)),
  <- rev_elements_rev, fold_left_rev_right.
  apply foldr_spec'_byleft.
*)
  revert sd. unfold elements. induction m as
  [| c l IHl k v r IHr]; simpl; intros...
  rewrite <- foldr_spec'_aux, IHr. simpl...
Qed.

Definition foldr_spec m {X} f sd {H:Ok m}
  := @foldr_spec' m X f sd.


Theorem min_elt_spec1 x y m `{Ok m} : min_elt m = Some (x,y) → MapsTo x y m.
Proof with auto.
  functional induction (min_elt m) as
  [ |  ? c ? k v r | ? i ? k v r ? i' ll lx ly lr];
  inversion 1...
  - apply IHo in H0; ok.
Qed.

Theorem min_elt_spec2 x y m `{Ok m} :
  min_elt m = Some (x,y) → ∀ a, In a m → ¬klt a x.
Proof with first [order | eauto].
  functional induction (min_elt m) as
  [ |  ? c ? k v r | ? i ? k v r ? c ll lx ly lr].
  - inversion 1.
  - inversion 1. intuition_in...
  - intros; inv;
    assert (Ok (N c ll lx ly lr))...
    + specialize (H9 _
      (Mt2It _ _ _
      (min_elt_spec1 _ _ _ H0)))...
    + specialize (H9 _
      (Mt2It _ _ _
      (min_elt_spec1 _ _ _ H0)))...
Qed.

Lemma min_elt_spec3 m `{Ok m} : min_elt m = None → Empty m.
Proof with eauto.
  functional induction (min_elt m) as
  [ |  ? c ? k v r | ? i ? k v r ? c ll lx ly lr]...
  - inversion 1.
  - intros. apply IHo in H0; ok. exfalso...
Qed.


Definition choose_spec1 := @min_elt_spec1.
Definition choose_spec2 := @min_elt_spec3.
Ltac gen_in x := generalize x; intro.
Theorem choose_spec3 m m' kv1 kv2 `{Ok m, Ok m'} :
choose m = Some kv1 → choose m' = Some kv2 → m [=] m' → kvpeq kv1 kv2.
Proof with auto.
  unfold choose. intros.
  destruct kv1 as [a a'], kv2 as [b b'].
  gen_in (min_elt_spec2 _ _ _ H1).
  gen_in (min_elt_spec2 _ _ _ H2).
  apply min_elt_spec1 in H1...
  apply min_elt_spec1 in H2...
  unfold Equal in H3. elim_compare a b.
  - split... rewrite H3, H6 in H1.
    apply (MapsTo_spec2 b _ _ m')...
  - rewrite H3 in H1. destruct (H5 a)...
    exists a'...
  - rewrite <- H3 in H2.
    destruct (H4 b)... exists b'...
Qed.


Lemma max_elt_spec1 x y m `{Ok m} : max_elt m = Some (x,y) → MapsTo x y m.
Proof with auto.
  functional induction (max_elt m) as
  [ |  ? c l k v ? | ? i l k v ? ? c rl rx ry rr];
  inversion 1...
  - apply IHo in H0; ok.
Qed.

Lemma max_elt_spec2 x y m `{Ok m} :
  max_elt m = Some (x,y) → ∀ a, In a m → ¬klt x a.
Proof with first [order|eauto].
  functional induction (max_elt m) as
  [ |  ? c l k v ? | ? i l k v ? ? i' rl rx ry rr].
  - inversion 1.
  - inversion 1. intuition_in; order.
  - intros; inv;
    assert (Ok (N i' rl rx ry rr))...
    + specialize (H10 _
      (Mt2It _ _ _
      (max_elt_spec1 _ _ _ H0)))...
    + specialize (H10 _
      (Mt2It _ _ _
      (max_elt_spec1 _ _ _ H0)))...
Qed.

Lemma max_elt_spec3 m `{Ok m} : max_elt m = None → Empty m.
Proof with auto.
  functional induction (max_elt m) as
  [ |  ? c l k v ? | ? i l k v ? ? c rl rx ry rr]...
  - inversion 1.
  - intro. apply IHo in H0; ok.
    destruct (H0 rx ry)...
Qed.

  End Vals1.


Section Vals2.
 Context {val val': Type}.
 Notation mv  := (map_of val).
 Notation mv' := (map_of val').
 Notation compatb := (Proper (keq==>Logic.eq==>Logic.eq)) (only parsing).


Hint Unfold Ok MapsTo In lt_tree gt_tree.
Hint Constructors MaT InT bst.
Hint Immediate MX.eq_sym.
Hint Resolve MX.eq_refl MX.eq_trans MX.lt_trans @ok
k_kvp_eq k_kvp_eq' In_InT InT_In Mt2It It2Mt
MapsTo_spec1' MapsTo_spec1 It_1 Mt_node_iff Mt_leaf_iff
It_node_iff It_leaf_iff lt_leaf gt_leaf lt_tree_node
gt_tree_node lt_tree_not_in lt_tree_trans gt_tree_not_in
gt_tree_trans lt_left lt_right lt_tree_compat gt_left gt_right
gt_tree_compat kvp_k_eq_f kvp_k_eq_f' kvp_k_eq_s kvp_k_eq_s'
kelements_spec2.


Ltac inv_ok := match goal with
 | H:Ok (N _ _ _ _ _) |- _ => clear_inversion H; inv_ok
 | H:Ok E |- _ => clear H; inv_ok
 | H:bst ?x |- _ => change (Ok x) in H; inv_ok
 | _ => idtac
end.

Ltac inv_MaT := match goal with
 | H:MapsTo ?a ?b E  |- _ => inversion H
 | H:MapsTo ?a ?b ?x |- _ => change (MaT a b x) in H; inv_MaT
 | H:In _ _ |- _ => destruct H; inv_MaT
 | _ => idtac
end.

Ltac is_tree_constr c :=
  match c with
   | E => idtac
   | N _ _ _ _ _ => idtac
   | _ => fail
  end.

Ltac invtree f :=
  match goal with
     | H:f ?s |- _ => is_tree_constr s; clear_inversion H; invtree f
     | H:f _ ?s |- _ => is_tree_constr s; clear_inversion H; invtree f
     | H:f _ _ ?s |- _ => is_tree_constr s; clear_inversion H; invtree f
     | _ => idtac
  end.

Ltac inv := inv_MaT; invtree (@MaT val); invtree (@MaT val');
inv_ok; invtree (@InT val); invtree (@InT val').

Ltac intuition_in := repeat progress ((intuition; inv) || subst).

Ltac order := match goal with
 | U: lt_tree _ ?t, V: InT _ ?t |- _ => specialize (U _ V); order
 | U: lt_tree _ ?t, V: MaT _ _ ?t |- _ =>
   specialize (U _ (Mt2It _ _ _ V)); order
 | U: gt_tree _ ?t, V: InT _ ?t |- _ => specialize (U _ V); order
 | U: gt_tree _ ?t, V: MaT _ _ ?t |- _ =>
   specialize (U _ (Mt2It _ _ _ V)); order
 | U: (forall _, InT _ ?t -> _),  V: InT _ ?t |- _
   => specialize (U _ V); order
 | _ => MX.order
end.

Ltac inn :=
  match goal with
   | H:MaT ?a ?b ?t |- MaT ?a ?b (N _ ?t _ _ _) => constructor 2; inn
   | H:MaT ?a ?b ?t |- MaT ?a ?b (N _ _ _ _ ?t) => constructor 3; inn
   | H:MaT ?a ?b _  |- MaT ?a ?b (N _ _ ?a ?b _) => constructor 1; inn
   | _ => auto;eauto
end.

Ltac intuition_inn := repeat progress (intuition; inv); inn.


Ltac rwiit := rewrite InInT.
Tactic Notation "rwiit" "in" hyp(h) := rewrite InInT in h.
Ltac rwiti := rewrite <- InInT.
Tactic Notation "rwiti" "in" hyp(h) := rewrite <- InInT in h.

Ltac InCon1 := rwiit; constructor 1.
Ltac InCon2 := rwiit; constructor 2; rwiti.
Ltac InCon3 := rwiit; constructor 3; rwiti.

 Notation E'  := (@E val).
 Notation Ok  := (@Props.Ok val).
 Notation Ok' := (@Props.Ok val').

 Definition Subset   (m:mv) (m':mv') := ∀ k  , In k m → In k m'.
 Notation "s [<=] t" := (Subset s t) (at level 70, no associativity).

 Definition Equivb cmp x y := (∀k, In k x ↔ In k y) ∧ (∀k (v:val) (v':val'),
            MapsTo k v x → MapsTo k v' y → cmp v v' = true).


(** ** Subset *)
Lemma subsetl_spec subset_l1 l1 x1 y1 c1 m2
`{Ok (N c1 l1 x1 y1 E), Ok' m2} :
 (∀ m `{Ok' m}, (subset_l1 m = true ↔ Subset l1 m)) →
 (subsetl subset_l1 x1 m2 = true ↔ Subset (N c1 l1 x1 y1 E) m2).
Proof with first [order|eauto].
  induction m2 as [|c2 l2 IHl2 x2 y2 r2 IHr2]; simpl; intros.
  - unfold Subset; intuition; [discriminate|].
    assert (In x1 (@E val')). { apply H0... } inv.
  - inv. elim_compare x1 x2.
    + rewrite H... clear H IHl2 IHr2.
      unfold Subset. intuition_in; 
    [ InCon1 | InCon2; apply H1
    | assert (In k (N c2 l2 x2 y2 r2)) by
      (apply H1; eauto);intuition_in]...
    + rewrite IHl2... clear H IHl2 IHr2.
      unfold Subset. intuition_in;
      assert (In k (N c2 l2 x2 y2 r2)) by
      (apply H1; eauto); intuition_in...
    + rewrite <-andb_lazy_alt, andb_true_iff, H;
      clear H IHl2 IHr2... unfold Subset. intuition_in;
    [ rewrite mem_spec in H2
    | apply H3
    | rewrite mem_spec; [assert (In x1 (N c2 l2 x2 y2 r2))
        by (apply H1;eauto); intuition_in|]]...
Qed.

Lemma subsetr_spec subset_r1 r1 x1 y1 c1 m2
`{Ok (N c1 E x1 y1 r1), Ok' m2} :
 (∀ m `{Ok' m}, (subset_r1 m = true ↔ Subset r1 m)) →
 (subsetr subset_r1 x1 m2 = true ↔ Subset (N c1 E x1 y1 r1) m2).
Proof with first [order|eauto].
  induction m2 as [|c2 l2 IHl2 x2 y2 r2 IHr2]; simpl; intros.
  - unfold Subset; intuition; [discriminate|].
    assert (In x1 (@E val')). { apply H0... } inv.
  - inv. elim_compare x1 x2.
    + rewrite H... clear H IHl2 IHr2.
      unfold Subset. intuition_in.
      * InCon1...
      * InCon3. apply H1...
      * assert (In k (N c2 l2 x2 y2 r2)). { apply H1... }
        intuition_in; [order|order|eauto].
    + rewrite <-andb_lazy_alt, andb_true_iff, H;
      clear H IHl2 IHr2... unfold Subset. intuition_in.
      * rewrite mem_spec in H2...
      * rewrite mem_spec in H2...
      * rewrite mem_spec; [|eauto].
        assert (In x1 (N c2 l2 x2 y2 r2)) by
        (apply H1; InCon1; order).
        intuition_in...
    + rewrite IHr2... clear H IHl2 IHr2.
      unfold Subset. intuition_in;
      assert (In k (N c2 l2 x2 y2 r2)) by
      (apply H1; eauto); intuition_in...
Qed.

Lemma subset_spec : ∀ m1 m2 `{Ok m1, Ok' m2},
 (subset m1 m2 = true ↔ Subset m1 m2).
Proof with first [order|eauto].
  induction m1 as [| c1 l1 IHl1 x1 y1 r1 IHr1]; simpl; intros.
  - unfold Subset; intuition_in.
  - destruct m2 as [| c2 l2 x2 y2 r2]; simpl; intros.
    + unfold Subset; intuition_in; try discriminate.
      assert (In x1 (@E val')). { apply H; InCon1... }
      inv_MaT.
    + inv. elim_compare x1 x2.
      * rewrite <-andb_lazy_alt, andb_true_iff, IHl1, IHr1...
        clear IHl1 IHr1. unfold Subset; intuition_in;
      [ InCon1; order| InCon2; apply H1; eauto
      | InCon3; apply H2; eauto | |];
        assert (In k (N c2 l2 x2 y2 r2)) by 
        (apply H0;eauto); intuition_in...
      * rewrite <-andb_lazy_alt, andb_true_iff, IHr1...
        rewrite (@subsetl_spec (subset l1) l1 x1 y1 c1)...
        clear IHl1 IHr1. unfold Subset. intuition_in;
      [ InCon2; auto | InCon2; apply H1; inn
      | apply H2; eauto | |]; assert (In k (N c2 l2 x2 y2 r2))
        by (apply H0; eauto); intuition_in...
      * rewrite <-andb_lazy_alt, andb_true_iff, IHl1...
        rewrite (@subsetr_spec (subset r1) r1 x1 y1 c1)...
        clear IHl1 IHr1. unfold Subset. intuition_in;
      [ InCon3; auto | apply H2; eauto
      | InCon3; apply H1; eauto | |];
        assert (In k (N c2 l2 x2 y2 r2)) by
        (apply H0; eauto); intuition_in...
Qed.

Hint Constructors L.lt_list.
Hint Unfold L.lt L.eq.
Hint Resolve L.eq_cons L.cons_CompSpec.


Definition mkeq := L.eq.
Definition mklt := L.lt.


Instance mklt_compat : Proper (mkeq==>mkeq==>iff) mklt
:= L.lt_compat'.

Instance mkeq_equiv : Equivalence mkeq
:= L.eq_equiv.

Instance mklt_strorder : StrictOrder mklt
:= L.lt_strorder.


(** [flatten_e e] returns the list of elements of [e] i.e. the list
    of elements actually compared *)

Fixpoint flatten_e (e : (@enumeration val')) : list key :=
  match e with
  | End => nil
  | More k t r => k :: kelements t ++ flatten_e r
 end.

Lemma flatten_e_kelements :
 forall l k v r c e,
 kelements l ++ flatten_e (More k r e) = kelements (N c l k v r) ++ flatten_e e.
Proof.
  intros. simpl. now rewrite kelements_node, app_ass.
Qed.

Lemma cons_1 m : ∀ e,
  flatten_e (econs m e) = kelements m ++ flatten_e e.
Proof.
 induction m; simpl; auto; intros.
 rewrite IHm1; apply flatten_e_kelements.
Qed.

Definition Cmp c x y :=
 CompSpec L.eq L.lt x y c.

Local Hint Unfold Cmp flip.
Local Hint Transparent L.eq L.lt.

Lemma compare_end_Cmp e2 :
  Cmp (compare_end e2) nil (flatten_e e2).
Proof.
  now destruct e2 as [|];
  simpl; do 2 constructor.
Qed.

Lemma compare_more_Cmp : forall k1 cont k2 r2 e2 l,
Cmp (cont (econs r2 e2)) l (kelements r2 ++ flatten_e e2) →
Cmp (compare_more k1 cont (More k2 r2 e2))
    (k1 :: l)
    (flatten_e (More k2 r2 e2)).
Proof.
  simpl; intros; elim_compare k1 k2; red; auto.
Qed.

Lemma compare_cont_Cmp : ∀ (m1:mv) cont e2 l,
 (∀ e, Cmp (cont e) l (flatten_e e)) →
 Cmp (compare_cont m1 cont e2) (kelements m1 ++ l) (flatten_e e2).
Proof with auto.
  induction m1 as [|c1 l1 Hl1 x1 y1 r1 Hr1];
  simpl; intros... rewrite kelements_node,
  app_ass; simpl. apply Hl1... clear e2.
  intros [|x2 r2 e2]; [simpl|]...
  apply compare_more_Cmp. rewrite <- cons_1...
Qed.

Lemma compare_Cmp (m:mv) (m':mv') :
 Cmp (compare m m') (kelements m) (kelements m').
Proof with auto.
 intros; unfold compare.
 rewrite (app_nil_end (kelements m)).
 replace (kelements m') with (flatten_e (econs m' End)) by
  (rewrite cons_1; simpl; rewrite <- app_nil_end; auto).
 apply compare_cont_Cmp... intros.
 apply compare_end_Cmp...
Qed.

Lemma compare_spec : ∀ m (m':mv') `{Ok m, Ok' m'},
CompSpec mkeq mklt (kelements m) (kelements m') (compare m m').
Proof with auto.
  intros. destruct (compare_Cmp m m');
  constructor...
Qed.



Lemma map_spec1' x y (m:mv) (f:_→val') :
 MapsTo x y m → MapsTo x (f y) (map f m).
Proof with auto.
  induction m as [| i l IHl k v r IHr];
  intros.
  - inversion H.
  - clear_inversion H; unfold map;
    fold (@map val val').
    + constructor...
    + constructor 2. apply IHl...
    + constructor 3. apply IHr...
Qed.

Definition map_spec1 x y m f `{Ok m}
  := map_spec1' x y m f.

Lemma map_spec2' x (m:mv) (f:_→val') : In x (map f m) → In x m.
Proof with auto.
  rewrite !@InInT.
  induction m; inversion 1; subst; inn.
Qed. Hint Resolve map_spec2'.

Definition map_spec2 x m f `{Ok m}
  := map_spec2' x m f.

Instance map_ok (f:val→val') m `{Ok m} : Ok' (map f m).
Proof with auto.
  induction m;[left|right];
  fold (@map val val');
  clear_inversion Ok0; auto;
  intros a H; rewrite <- InInT in H;
  apply map_spec2' in H...
Qed.

Lemma mapi_spec1' x y m (f:key→val→val') :
 compatb f → MapsTo x y m → MapsTo x (f x y) (mapi f m).
Proof with auto.
  induction m as [| i l IHl k v r IHr];
  intros.
  - inversion H0.
  - clear_inversion H0;
    unfold mapi; fold (@mapi val val').
    + replace (f x v) with (f k v).
      constructor... rewrite H2...
    + constructor 2; apply IHl...
    + constructor 3; apply IHr...
Qed.

Definition mapi_spec1 x y m (f:key→val→val') `{Ok m}
  := mapi_spec1' x y m f.

Lemma mapi_spec2' x m (f:key→val→val') : In x (mapi f m) -> In x m.
Proof with auto.
  rewrite !InInT.
  unfold mapi.
  induction m as [| i l IHl k v r IHr];
  fold (@mapi val val') in *; intros.
  - inversion H.
  - clear_inversion H.
    + constructor 1...
    + constructor 2; apply IHl...
    + constructor 3; apply IHr...
Qed.

Definition mapi_spec2 x m (f:key→val→val') `{Ok m}
  := mapi_spec2' x m f.

Instance mapi_ok (f:key→val→val') m `{Ok m}: Ok' (mapi f m).
Proof with auto.
  induction m as [|i l IHl x' y' r IHr];
  [left|right]; clear_inversion Ok0;
  [apply IHl | apply IHr | |];
  fold (@mapi val val'); auto;
  intros a X; rewrite <- InInT in X;
  apply mapi_spec2 in X;
  rewrite InInT in X...
Qed.

  End Vals2.

End Props.