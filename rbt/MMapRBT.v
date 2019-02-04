(* A finite partial maps interface and implmentation in Coq.
   Largely copied from the Coq Std Lib, Msets
   - C.E. Sally, Aquinas Hobor *)

Require Import MMapInterface MMapGenTree Utf8 Orders SetoidList NPeano Pnat.

Inductive colour := Red | Black.
Module Colour.
  Definition t := colour.
End Colour.

Module Imp (K:OrderedType) <: MMapInterface.Funs K.
Include MMapGenTree.Ops Colour K.

Local Notation Rd := (N Red).
Local Notation Bk := (N Black).

  Section Vals1.
   Context {val val':Type}.
   Notation mv  := (map_of val).
   Notation mv' := (map_of val').
   Notation kvp := (prod key val).
   Notation lkvp := (list kvp).
   Notation okvp := (option kvp).

Definition singleton k v : mv := N Red E k v E.

Definition makeBlack (t:mv) :=
  match t with
  | Rd l k v r => Bk l k v r
  | _ => t
  end.

Definition makeRed (t:mv) :=
  match t with
  | Bk l k v r => Rd l k v r
  | _ => t
  end.

Definition lbal l z z' (d:mv) :=
  match l with
  | Rd (Rd a x x' b) y y' c
  | Rd a x x' (Rd b y y' c) => Rd (Bk a x x' b) y y' (Bk c z z' d)
  | _ => Bk l z z' d
  end.

Definition rbal a x x' (r:mv) :=
  match r with
  | Rd (Rd b y y' c) z z' d
  | Rd b y y' (Rd c z z' d) => Rd (Bk a x x' b) y y' (Bk c z z' d)
  | _ => Bk a x x' r
  end.

Fixpoint ins x y (t:mv) :=
  match t with
  | E => Rd E x y E
  | N c l k v r =>
    match kcmp x k with
    | Eq => N c l k y r
    | Lt =>
      match c with
      | Red => Rd (ins x y l) k v r
      | Black => lbal (ins x y l) k v r
      end
    | Gt =>
      match c with
      | Red => Rd l k v (ins x y r)
      | Black => rbal l k v (ins x y r)
      end
    end
  end.

Definition add x y t := makeBlack (ins x y t).

Definition lbalS l k v (r:mv) :=
  match l with
  | Rd a x x' b => Rd (Bk a x x' b) k v r
  | _ =>
    match r with
    | Bk a y y' b => rbal l k v (Rd a y y' b)
    | Rd (Bk a y y' b) z z' c => Rd (Bk l k v a) y y' (rbal b z z' (makeRed c))
    | _ => Rd l k v r
    end
  end.

Definition rbalS l k v (r:mv) :=
  match r with
  | Rd b y y' c => Rd l k v (Bk b y y' c)
  | _ =>
    match l with
    | Bk a x x' b => lbal (Rd a x x' b) k v r
    | Rd a x x' (Bk b y y' c) => Rd (lbal (makeRed a) x x' b) y y' (Bk c k v r)
    | _ => Rd l k v r
    end
  end.

Fixpoint append (l:mv) : mv → mv :=
  match l with
  | E => λ x, x
  | N lc ll lx ly lr =>
    fix append_l (r:mv) : mv :=
    match r with
    | E => l
    | N rc rl rx ry rr =>
      match lc, rc with
      | Red, Red =>
        let lrl := append lr rl in
        match lrl with
        | Rd lr' x y rl' => Rd (Rd ll lx ly lr') x y (Rd rl' rx ry rr)
        | _              => Rd ll lx ly (Rd lrl rx ry rr)
        end
      | Black, Black =>
        let lrl := append lr rl in
        match lrl with
        | Rd lr' x y rl' => Rd (Bk ll lx ly lr') x y (Bk rl' rx ry rr)
        | _              => lbalS ll lx ly (Bk lrl rx ry rr)
        end
      | Black, Red => Rd (append_l rl) rx ry rr
      | Red, Black => Rd ll lx ly (append lr r)
      end
    end
  end.

Fixpoint del x (t:mv) := (* delete by key only *)
  match t with
  | E => t
  | N _ l k v r =>
    match kcmp x k with
    | Eq => append l r
    | Lt =>
      match l with
      | Bk _ _ _ _ => lbalS (del x l) k v r
      | _          => Rd (del x l) k v r
      end
    | Gt =>
      match r with
      | Bk _ _ _ _ => rbalS l k v (del x r)
      | _          => Rd l k v (del x r)
      end
    end
  end.

Definition remove x t := makeBlack (del x t).


(* treeification *)

Notation mvlkvp := (prod mv lkvp).
Definition bogus : mvlkvp := (E, nil).

Notation treeify_t := (lkvp → mvlkvp).
Definition treeify_zero : treeify_t := λ acc, (E,acc).

Definition treeify_one : treeify_t := λ acc,
  match acc with
  | (x,y) :: acc' => (Rd E x y E, acc')
  | _ => bogus
  end.

Definition treeify_cont (f g : treeify_t) : treeify_t := λ lst,
  match f lst with
  | (l, (x,y) :: t) =>
    match g t with
    | (r, t') => (Bk l x y r, t')
    end
  | _ => bogus (* when treeify_cont is called on a empty list *)
  end.

Local Notation parity := bool.
Definition ev : parity := true.
Definition od : parity := false.

Fixpoint treeify_aux (pr:parity)(n:positive) : treeify_t :=
match n with
| xH   => if pr (*is even*) then treeify_zero else treeify_one
| xO m => treeify_cont (treeify_aux pr m) (treeify_aux ev m)
| xI m => treeify_cont (treeify_aux od m) (treeify_aux pr m)
end.

Fixpoint plength_aux (l:lkvp)(acc:positive) :=
  match l with
  | nil    => acc
  | _ :: l => plength_aux l (Pos.succ acc)
  end.

Definition plength lst := plength_aux lst 1.

Definition treeify (l:lkvp) := fst (treeify_aux ev (plength l) l).
(* noitacifieert *)

Local Open Scope positive_scope.
Fixpoint sl_aux x0 (L : lkvp) (acc : bool * positive) :=
  match L with
  | nil        => acc
  | (x,_) :: t => let (b,len) := acc in
                  match kcmp x0 x  with
                  | Lt => sl_aux x t (b,len+1)
                  | _  => (false,len)
                  end
  end.

Definition sorted_length (lst : lkvp) :=
  match lst with
  | nil    => (true,1)
  | (x,_) :: t => sl_aux x t (true,2)
  end.
Local Close Scope positive_scope.

Definition fromList (lst : lkvp) :=
  let (b,len) := sorted_length lst in
  if b then fst (treeify_aux ev len lst)
  else fold_left (λ t kv, add (fst kv) (snd kv) t) lst empty.

Fixpoint filter_aux (P:_→_→bool) (m:mv) acc :=
  match m with
  | E => acc
  | N _ l k v r => 
    let new_acc := filter_aux P r acc in
    if P k v
      then filter_aux P l ((k,v) :: new_acc)
      else filter_aux P l new_acc
  end.

Definition filter P t : mv := treeify (filter_aux P t nil).

Fixpoint partition_aux (f:_→_→bool) (m:mv) ac1 ac2 :=
  match m with
  | E => (ac1,ac2)
  | N _ sl k v sr =>
    let (nac1,nac2) := partition_aux f sr ac1 ac2 in
    if f k v
      then partition_aux f sl ((k,v) :: nac1) nac2
      else partition_aux f sl nac1 ((k,v) :: nac2)
  end.

Definition partition f m : mv * mv :=
  let (L,R) := partition_aux f m nil nil in 
  (treeify L, treeify R).



Definition skp_R m : mv := (*skip red*)
  match m with
  | Rd l _ _ _ => l
  | _ => m
  end.

Definition skp_B m : mv :=
  match skp_R m with
  | Bk l _ _ _ => l
  | m' => m'
  end.

Fixpoint compare_bheight sx2 s t tx2 : comparison :=
  match skp_R sx2, skp_R s, skp_R t, skp_R tx2 with
  | N _ a _ _ _, N _ b _ _ _,
    N _ c _ _ _, N _ d _ _ _   => compare_bheight (skp_B a) b c (skp_B d)

  | _, E, _, N _ _ _ _ _       => Lt
  | N _ _ _ _ _, _, E, _       => Gt

  | N _ a _ _ _, N _ b _ _ _,
    N _ c _ _ _, E             => compare_bheight (skp_B a) b c E

  | E,           N _ b _ _ _,
    N _ c _ _ _, N _ d _ _ _   => compare_bheight E b c (skp_B d)

  | _, _, _, _ => Eq
  end.

  End Vals1.
  Section Vals2.
   Context {val val':Type}.
   Notation mv  := (map_of val).
   Notation mv' := (map_of val').

(* Intersection *)
Notation kvp' := (prod key val').
Notation kvp := (prod key val).
Notation lkvp := (list kvp).
Notation lkvp' := (list kvp').
Notation vv' := (prod val val').
Notation v'v := (prod val' val).
Notation mvv' := (map_of (prod val val')).
Notation mv'v := (map_of (prod val' val)).
Notation lkvv'p := (list (prod key vv')).
Notation lkv'vp := (list (prod key v'v)).
Notation lk := (λ X, (list (prod key X))).

Fixpoint inter_list (sl:key→val→val→val) l1 : lkvp → lkvp → lkvp :=
  match l1 with
  | nil => λ _ acc, acc
  | (x,y) :: t1 =>
    fix inter_l1 l2 acc :=
    match l2 with
    | nil => acc
    | (a,b) :: t2 =>
      match kcmp x a with
      | Eq => inter_list sl t1 t2 ((x, sl x y b) :: acc)
      | Lt => inter_l1 t2 acc
      | Gt => inter_list sl t1 l2 acc
      end
    end
  end.


Fixpoint filter_inter_aux {X:Type} sl (sub min:mv) (acc:lk X) : lk X :=
  match min with
  | E => acc
  | N _ l x y r =>
    let new_acc := @filter_inter_aux X sl sub r acc in
    match find x sub with
    | None   => @filter_inter_aux X sl sub l new_acc
    | Some b => @filter_inter_aux X sl sub l ((x,sl x y b) :: new_acc)
    end
  end.

Definition linear_inter sl t1 t2 :=
  treeify (inter_list sl (rev_elements t1) (rev_elements t2) nil).

Definition filter_inter {X:Type} sl sub min : map_of X :=
 treeify (filter_inter_aux (X:=X) sl sub min nil).


Definition inter sl t1 t2 :=
linear_inter sl t1 t2.
(*
  match compare_bheight t1 t1 t2 t2 with
  | Eq => linear_inter (X:=X) sl t1 t2
  | Lt => filter_inter (X:=X) sl t2 t1
  | Gt => filter_inter (X:=X) sl t1 t2
  end.
*)

(* Intersection *)


(* Difference *)
Fixpoint diff_list l1 : lkvp → lkvp → lkvp :=
  match l1 with
  | nil => λ _ acc, acc
  | (x,y) :: l1' =>
    fix diff_l1 l2 acc :=
    match l2 with
    | nil => rev_append l1 acc
    | (x2,y2) :: l2' =>
      match kcmp x x2 with
      | Eq => diff_list l1' l2' acc
      | Lt => diff_l1 l2' acc
      | Gt => diff_list l1' l2 ((x,y)::acc)
      end
    end
  end.

Definition linear_diff s1 s2 :=
  treeify (diff_list (rev_elements s1) (rev_elements s2) nil).

Definition diff t1 t2 :=
  match compare_bheight t1 t1 t2 t2 with
  | Eq => linear_diff t1 t2
  | Lt => filter (λ k _, negb (mem k t2)) t1
  | Gt => foldl (λ k v, remove k) t2 t1
  end.
(* Difference *)



(* Union *)
Fixpoint union_list l1 : lkvp → lkvp → lkvp :=
  match l1 with
  | nil => @rev_append _
  | (x,y) :: t1 =>
    fix union_l1 l2 acc :=
    match l2 with
    | nil => rev_append l1 acc
    | (a,b) :: t2 =>
      match kcmp x a with
      | Eq => union_list t1 t2 ((x,y) :: acc)
      | Lt => union_l1 t2 ((a,b) :: acc)
      | Gt => union_list t1 l2 ((x,y) :: acc)
      end
    end
  end.

Definition linear_union t1 t2 :=
  treeify (union_list (rev_elements t1) (rev_elements t2) nil).

Definition union t1 t2 := linear_union t1 t2.

  End Vals2.

End Imp.

(*
Require Import OrdersEx.
Module test <: A.Funs Nat_as_OT := Imp Nat_as_OT.
Export test.
Definition en := @empty nat.
Fixpoint addr n acc :=
match n with
| O => acc
| S x => addr x (add n n acc)
end.
Definition t := Eval compute in addr 10 en.
Eval compute in
. *)




























































Require MSetRBT.
Module Type MakeRaw (K:OrderedType) <: MMapInterface.RawMaps K.
Include Imp K.
Include MMapGenTree.Props K Colour.



Import MX.
Notation Rd := (N Red).
Notation Bk := (N Black).

Section Vals.
 Context {val : Type}.
 Notation mv := (map_of val).
 Notation kvp := (prod key val).
 Notation kvpeq := (Kvpeq val).
 Notation kvplt := (Kvplt val).
 Notation pkeq := (Pkeq val).
 Notation lkvp := (list kvp).
 Notation okvp := (option kvp).
 Notation kvpEQ := (@kvpEQ val).
 Notation kvpLT := (@kvpLT val).
 Notation "s [=] t"   := (Equal s t) (at level 70, no associativity).
 Notation compatb := (Proper (keq==>(@Logic.eq val)==>Logic.eq)) (only parsing).
(*
 Instance kvpeq_equiv : Equivalence kvpeq. apply Kvpeq_equiv. Defined.
 Instance kvpeq_refl  : Reflexive kvpeq.  apply Kvpeq_equiv. Defined.
 Instance kvpeq_trans : Transitive kvpeq. apply Kvpeq_equiv. Defined.
 Instance kvpeq_symm  : Symmetric kvpeq.  apply Kvpeq_equiv. Defined.
 Instance pkeq_equiv  : Equivalence pkeq. apply Pkeq_equiv.  Defined.
 Instance pkeq_refl   : Reflexive pkeq.   apply Pkeq_equiv.  Defined.
 Instance pkeq_trans  : Transitive pkeq.  apply Pkeq_equiv.  Defined.
 Instance pkeq_symm   : Symmetric pkeq.   apply Pkeq_equiv.  Defined.
 Instance kvplt_strord : StrictOrder kvplt. apply Kvplt_strord. Defined.
 Instance kvplt_irrefl : Irreflexive kvplt. apply Kvplt_strord. Defined.
 Instance kvplt_trans  : Transitive kvplt.  apply Kvplt_strord. Defined.
*)


Instance mtcg : Proper (keq ==> eq ==> eq ==> iff) (@MaT val).
apply Mt_compat. Defined.

Hint Immediate MX.eq_sym (@elements_spec2 val)
empty_ok (@Kvpeq_equiv val) (@Pkeq_equiv val) (@Kvplt_strord val)
(@Kvpeq_refl val) (@Kvpeq_trans val) (@Kvpeq_symm val)
(@Pkeq_refl val) (@Pkeq_trans val) (@Pkeq_symm val)
(@Kvplt_irrefl val) (@Kvplt_trans val).
Hint Resolve MX.eq_refl MX.eq_trans MX.lt_trans @ok.
Hint Unfold lt_tree gt_tree MapsTo In.
Hint Constructors MaT InT bst.
Hint Resolve @Mt_node_iff @Mt_leaf_iff @It_node_iff @It_leaf_iff.
Hint Resolve (@lt_leaf val) (@gt_leaf val)
             (@lt_tree_node val) (@gt_tree_node val).
Hint Resolve @lt_left @lt_right @gt_left @gt_right.
Hint Resolve @lt_tree_not_in @gt_tree_not_in.
Hint Resolve @lt_tree_trans @gt_tree_trans.
Hint Resolve (@lt_tree_compat val) (@gt_tree_compat val).
Hint Resolve (@Kvpeq_compat val) (@Kvpeq_equiv val).
Hint Resolve (@Kvplt_strord val).
Hint Resolve @k_kvp_eq @k_kvp_eq'
@kvp_k_eq_f @kvp_k_eq_f'
@kvp_k_eq_s @kvp_k_eq_s'.

Ltac rwiit := rewrite (@InInT val).
Tactic Notation "rwiit" "in" hyp(h) := rewrite (@InInT val) in h.
Ltac rwiti := rewrite <- (@InInT val).
Tactic Notation "rwiti" "in" hyp(h) := rewrite <- (@InInT val) in h.

Ltac gen_in h := generalize (h); intro.
Ltac rwp1 h := rewrite (proj1 h).
Tactic Notation "rwp1" "<-" hyp(h) := rewrite <- (proj1 h).


Ltac clear_inversion H := inversion H; clear H; subst.

Ltac inv_ok := match goal with
 | H:Ok (N _ _ _ _ _) |- _ => clear_inversion H; inv_ok
 | H:Ok E |- _ => clear H; inv_ok
 | H:bst ?x |- _ => change (Ok x) in H; inv_ok
 | _ => idtac
end.

Ltac inv_MaT := match goal with
 | H:MapsTo ?k ?v ?t |- _ => change (MaT k v t) in H; inv_MaT
 | H:In ?k ?t |- _ => destruct H; inv_MaT
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

Ltac inv := invtree (@MaT val); inv_ok; inv_MaT; invtree (@InT val).

Ltac intuition_in := repeat progress (intuition; inv; subst).


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
   | H:MaT ?k ?v _  |- MaT ?k ?v (N _ _ ?k ?v _) => constructor 1; inn
   | H:MaT ?k ?v ?t |- MaT ?k ?v (N _ ?t _ _  _) => constructor 2; inn
   | H:MaT ?k ?v ?t |- MaT ?k ?v (N _ _  _ _ ?t) => constructor 3; inn
(*   | H:MaT ?k ?v ?t |- In ?k*)
   | _ => auto;eauto
end.

Ltac intuition_inn := repeat progress (intuition; inv; subst); inn.

Ltac induct s x :=
 induction s as [|i l IHl x' y' r IHr]; simpl; intros;
 [|elim_compare x x'; intros; inv].

Ltac auto_tc := auto with typeclass_instances.

Ltac ok :=
 inv; change bst with (@Ok val) in *;
 match goal with
   | |- Ok (N _ _ _ _ _) => constructor; auto_tc; ok
   | |- lt_tree _ (N _ _ _ _ _) => apply lt_tree_node; ok
   | |- gt_tree _ (N _ _ _ _ _) => apply gt_tree_node; ok
   | _ => eauto with typeclass_instances
 end.

























Local Notation E' := (@E val).
Local Notation Ok' := Ok.
Local Notation Ok := (@Ok val).
Local Notation Mt_compat := (@Mt_compat val).


(*
Lemma bi: forall (X:Type) (sl:key->val->val->X) (x:key) (y:val) (z:val),
sl x y z = (unwrap sl) (func x y z).
reflexivity. Defined.


Goal forall (X:Type) (sl:key->val->val->X) l1 l2,
inter_list sl l1 l2 nil =
List.map (fun x => (fst x, unwrap sl x)) (inter_list func l1 l2 nil).
Proof with auto.
intros; simpl.

  induction l1 as [simpl| (x,y) l1 IH1]...
  induction l2 as [| (a,b) l2 IH2]; simpl...

  case K.compare_spec; intro C.

  simpl.
  simpl.
. intros.


Lemma inter_list_spec sl x y b l1 l2 acc :
 sort kvplt (rev l1) →
 sort kvplt (rev l2) →
 (InA kvv'peq (x,) (inter_list func l1 l2 acc) ↔
   (InA kvpeq (x,y) l1 ∧ InA kvpeq (x,b) l2) ∨ InA kvv'peq (x,(y,b)) acc).
*)


Lemma singleton_spec a x b (y:val) :
MaT a b (singleton x y) ↔ keq a x /\ b = y.
Proof with auto.
  unfold singleton.
  intuition_in.
Qed.

Instance singleton_ok x (y:val) : Ok (singleton x y).
Proof with auto.
  constructor; try inversion 1...
Qed.

Lemma makeBlack_spec1 x y (m:mv) : MaT x y (makeBlack m) ↔ MaT x y m.
Proof with auto.
  induction m as [|c l IHl k v r IHr].
  - intuition_in.
  - destruct c; cbv; split; inversion 1... 
Qed.

Lemma makeBlack_spec2 x (m:mv) : InT x (makeBlack m) ↔ InT x m.
Proof with auto.
  induction m as [|c l IHl k v r IHr].
  - intuition_in.
  - destruct c; cbv; split; inversion 1... 
Qed.


Instance makeBlack_ok m `{Ok m} : Ok (makeBlack m).
Proof with auto.
  induction m as [|c l IHl k v r IHr].
  - simpl...
  - destruct c; cbv; inversion Ok0...
Qed.


Lemma makeRed_spec1 x y (m:mv) : MaT x y (makeRed m) ↔ MaT x y m.
Proof with auto.
  induction m as [|c l IHl k v r IHr].
  - intuition.
  - destruct c; cbv; split; inversion 1...
Qed.

Lemma makeRed_spec2 x (m:mv) : InT x (makeRed m) ↔ InT x m.
Proof with auto.
  induction m as [|c l IHl k v r IHr].
  - intuition.
  - destruct c; cbv; split; inversion 1...
Qed.


Instance makeRed_ok m `{Ok m} : Ok (makeRed m).
Proof with auto.
  induction m as [|c l IHl k v r IHr].
  - simpl...
  - destruct c; cbv; inversion Ok0...
Qed.



Definition isblack (t:mv) :=
 match t with Bk _ _ _ _ => True | _ => False end.

Definition notblack (t:mv) :=
 match t with Bk _ _ _ _ => False | _ => True end.

Definition notred (t:mv) :=
 match t with Rd _ _ _ _ => False | _ => True end.

Definition rcase {A} f g (t:mv) : A :=
 match t with
 | Rd a k v b => f a k v b
 | _ => g t
 end.

Inductive rspec {A} f g : @tree val -> A -> Prop :=
 | rred a k v b : rspec f g (Rd a k v b) (f a k v b)
 | relse t : notred t -> rspec f g t (g t).

Fact rmatch {A} f g t : rspec (A:=A) f g t (rcase f g t).
Proof.
  destruct t as [| [|] l k v r]; simpl; now constructor.
Qed.

Definition rrcase {A} f g (t:mv) : A :=
 match t with
 | Rd (Rd a x x' b) y y' c => f a x x' b y y' c
 | Rd a x x' (Rd b y y' c) => f a x x' b y y' c
 | _ => g t
 end.

Notation notredred := (rrcase (fun _ _ _ _ _ _ _ => False)
                      (fun _ => True)).

Inductive rrspec {A} f g : mv -> A -> Prop :=
 | rrleft a x x' b y y' c : rrspec f g
                            (Rd (Rd a x x' b) y y' c)
                            (f a x x' b y y' c)
 | rrright a x x' b y y' c : rrspec f g
                             (Rd a x x' (Rd b y y' c))
                             (f a x x' b y y' c)
 | rrelse t : notredred t -> rrspec f g t (g t).

Fact rrmatch {A} f g t : rrspec (A:=A) f g t (rrcase f g t).
Proof.
destruct t as [|[|] l x y r]; simpl; try now constructor.
destruct l as [|[|] ll lx ly lr], r as [|[|] rl rx ry rr]; now constructor.
Qed.

Definition rrcase' {A} f g (t:mv) : A :=
 match t with
 | Rd a x x' (Rd b y y' c) => f a x x' b y y' c
 | Rd (Rd a x x' b) y y' c => f a x x' b y y' c
 | _ => g t
 end.

Fact rrmatch' {A} f g t : rrspec (A:=A) f g t (rrcase' f g t).
Proof.
destruct t as [|[|] l x y r]; simpl; try now constructor.
destruct l as [|[|] ll lx ly lr], r as [|[|] rl rx ry rr]; now constructor.
Qed.

Fact lbal_match l k v r :
 rrspec
   (fun a x x' b y y' c => Rd (Bk a x x' b) y y' (Bk c k v r))
   (fun l => Bk l k v r)
   l
   (lbal l k v r).
Proof. refine (rrmatch _ _ _). Qed.

Fact rbal_match l k v r :
 rrspec
   (fun a x x' b y y' c => Rd (Bk l k v a) x x' (Bk b y y' c))
   (fun r => Bk l k v r)
   r
   (rbal l k v r).
Proof.
 exact (rrmatch _ _ _).
Qed.

Fact lbalS_match l x x' r :
 rspec
  (fun a y y' b => Rd (Bk a y y' b) x x' r)
  (fun l =>
    match r with
    | Bk a y y' b => rbal l x x' (Rd a y y' b)
    | Rd (Bk a y y' b) z z' c => Rd (Bk l x x' a) y y' (rbal b z z' (makeRed c))
    | _ => Rd l x x' r
    end)
  l
  (lbalS l x x' r).
Proof.
  exact (rmatch _ _ _).
Qed.

Fact rbalS_match l x x' r :
 rspec
  (fun a y y' b => Rd l x x' (Bk a y y' b))
  (fun r =>
    match l with
    | Bk a y y' b => lbal (Rd a y y' b) x x' r
    | Rd a y y' (Bk b z z' c) => Rd (lbal (makeRed a) y y' b) z z' (Bk c x x' r)
    | _ => Rd l x x' r
    end)
  r
  (rbalS l x x' r).
Proof.
  exact (rmatch _ _ _).
Qed.

Lemma lbal_spec1 l x y r k (v:val) :
   MaT x y (lbal l k v r) ↔
   MaT x y l ∨ keq x k ∧ y = v ∨ MaT x y r.
Proof. case lbal_match; intuition_in. Qed.

Lemma lbal_spec2 l x r k (v:val) :
   InT x (lbal l k v r) ↔
   InT x l ∨ keq x k ∨ InT x r.
Proof. case lbal_match; intuition_in. Qed.

Instance lbal_ok l x y r `(Ok l, Ok r,
  lt_tree x l, gt_tree x r) : Ok (lbal l x y r).
Proof. destruct (lbal_match l x y r); ok. Qed.

Lemma rbal_spec1 l x y r k (v:val) :
   MaT x y (rbal l k v r) ↔
   MaT x y l ∨ keq x k ∧ y = v ∨ MaT x y r.
Proof. case rbal_match; intuition_in. Qed.

Lemma rbal_spec2 l x r k (v:val) :
   InT x (rbal l k v r) ↔
   InT x l ∨ keq x k ∨ InT x r.
Proof. case rbal_match; intuition_in. Qed.

Instance rbal_ok l x y r `(Ok l, Ok r,
    lt_tree x l, gt_tree x r) : Ok (rbal l x y r).
Proof. destruct (rbal_match l x y r); ok. Qed.

Hint Rewrite (@Mt_node_iff val) (@Mt_leaf_iff val)
 makeRed_spec1 lbal_spec1
 makeRed_spec2 lbal_spec2
 makeBlack_spec1 rbal_spec1
 makeBlack_spec2 rbal_spec2
(@It_node_iff val) (@It_leaf_iff val) : rb.

Ltac descolour := destruct_all Colour.t.
Ltac destree t := destruct t as [|[|] ? ? ?].
Ltac autorew := autorewrite with rb.
Tactic Notation "autorew" "in" ident(H) := autorewrite with rb in H.



Lemma ins_spec1 x y (m:mv) :
  MaT x y (ins x y m).
Proof.
  induct m x; descolour;
  autorew; intuition_in.
Qed.

Hint Immediate ins_spec1.

Lemma ins_spec2 a x b y (m:mv) :
  ~ keq a x -> (MaT a b (ins x y m) ↔ MaT a b m).
Proof.
  induct m x;
  [ cbv; split; intros
  | intuition_in;order
  | descolour; autorew
  | descolour; autorew
  ]; intuition_in.
Qed.

Hint Rewrite ins_spec2 : rb.



Lemma ins_spec3 a b c m `{Ok m} :
MaT a b (ins a c m) → b = c.
Proof with first [order|auto].
  induct m a; intuition_inn;
  try order; descolour.
  - clear_inversion H...
  - apply lbal_spec1 in H. destruct H
    as [H|[(H,H')|H]]...
  - clear_inversion H...
  - apply rbal_spec1 in H. destruct H
    as [H|[(H,H')|H]]...
Qed. Hint Immediate ins_spec3.


Lemma ins_fact1 a b x y (m:mv) `{Ok m}:
MaT a b (ins x y m) ↔ IF keq a x then b = y else MaT a b m.
Proof with eauto.
  split.
  - intro. destruct (keqd a x) as [Eq | Eq].
    + left;split... rewrite Eq in H...
    + right. split... autorew in H...
  - intros [(H,H')|(H,H')] .
    + rewrite H, H'... + autorew...
Qed.


Lemma ins_fact2 a x y (m:mv) :
InT a (ins x y m) ↔ keq a x ∨ ~keq a x /\ InT a m.
Proof with auto.
  do 2 rwiti. split; intros.
  - destruct (keqd a x)...
    right; split... inv.
    exists x0; autorew in H...
  - destruct H as [H|[H H']];
    [| inv; exists x0; autorew]...
    induct m x; [| exists y | |]; inn; descolour.
    + exists x1; inn...
    + exists x1; rewrite lbal_spec1...
    + exists x0; inn.
    + exists x0; rewrite rbal_spec1...
Qed.

(*
Hint Rewrite ins_spec3 : rb.
Local Hint Immediate ins_spec3. *)

Instance ins_ok m x y `{Ok m} : Ok (ins x y m).
Proof.
  induct m x; descolour;
  (ok || apply lbal_ok || apply rbal_ok);
  auto; intros a H'; rewrite ins_fact2 in H';
  destruct H' as [|[neq H']]; order.
Qed.


Lemma add_spec1' k v (m:mv) : MaT k v (add k v m).
Proof. unfold add. rewrite makeBlack_spec1. auto. Qed.
Definition add_spec1 k v m `{Ok m} := add_spec1' k v m.


Theorem add_spec2' a x b y (m:mv) :
  ¬keq a x → (MaT a b (add x y m) ↔ MaT a b m).
Proof.
  unfold add, MapsTo. intros A.
  destruct (ins_spec2 a x b y m A).
  autorew; intuition_in.
Qed.
Definition add_spec2 a x b y m `{Ok m} := add_spec2' a x b y m.

Corollary add_fact1 a b c m `{Ok m} :
MaT a b (add a c m) → b = c.
Proof with auto.
  unfold add. rewrite makeBlack_spec1.
  apply ins_spec3...
Qed.

Instance add_ok x y m `{(Ok m)} : Ok (add x y m).
Proof.
  unfold add; auto_tc.
Qed.

Lemma lbalS_spec1 l x y r k v :
  MaT k v (lbalS l x y r) ↔ MaT k v l ∨ kvpeq (k,v) (x,y) ∨ MaT k v r.
Proof with autorew; intuition_inn.
  case lbalS_match.
  - intros...
  - clear l. intros l _.
   destruct r as [|[|] rl rx ry rr];
   [|destree rl|]...
Qed.

Lemma lbalS_spec2 l x y (r:mv) k :
  InT k (lbalS l x y r) ↔ InT k l ∨ keq k x ∨ InT k r.
Proof with autorew; intuition_inn.
  case lbalS_match.
  - intros...
  - clear l. intros l _.
   destruct r as [|[|] rl rx ry rr];
   [|destree rl|]...
Qed.

Instance lbalS_ok l x y r : forall `(Ok l, Ok r, lt_tree x l, gt_tree x r),
 Ok (lbalS l x y r).
Proof.
 case lbalS_match; intros.
 - ok.
 - destruct r as [|[|] rl rx ry rr];
   [| |apply rbal_ok]; ok.
   * destruct rl as [|[|] rll rlx rly rlr]; intros; ok.
     + apply rbal_ok; ok. intros w. autorew. auto.
     + intros w. autorew. destruct 1 as [Hw|[Hw|Hw]];
       try rewrite Hw; eauto.
Qed.

Lemma rbalS_spec1 l x y r k v :
  MaT k v (rbalS l x y r) ↔ MaT k v l ∨ kvpeq (k,v) (x,y) ∨ MaT k v r.
Proof with autorew; intuition_in.
 case rbalS_match.
 - intros...
 - intros t _.
   destruct l as [|[|] ll lx ly lr];
   [|destruct lr as [|[|] lrl lrx lry lrr]|]...
Qed.

Lemma rbalS_spec2 l x y (r:mv) k :
  InT k (rbalS l x y r) ↔ InT k l ∨ keq k x ∨ InT k r.
Proof with autorew; intuition_in.
 case rbalS_match.
 - intros...
 - intros t _.
   destruct l as [|[|] ll lx ly lr];
   [|destruct lr as [|[|] lrl lrx lry lrr]|]...
Qed.

Instance rbalS_ok l x y r : ∀ `(Ok l, Ok r, lt_tree x l, gt_tree x r),
  Ok (rbalS l x y r).
Proof with ok.
  case rbalS_match; intros...
  destruct l as [|[|] ll lx ly lr];
  [| |apply lbal_ok]...
  destruct lr as [|[|] lrl lrx lry lrr]; intros...
  + apply lbal_ok... intros w; autorew; auto.
  + intros w; autorew. destruct 1 as [Hw|[Hw|Hw]];
  try rewrite Hw; eauto.
Qed.

Hint Rewrite lbalS_spec1 rbalS_spec1 lbalS_spec2 rbalS_spec2 : rb.

Ltac append_tac l r :=
 induction l as [| lc ll _ lx ly lr IHlr];
 [intro r; simpl
 |induction r as [| rc rl IHrl rx ry rr _];
   [simpl
   |destruct lc, rc;
     [specialize (IHlr rl); clear IHrl
     |simpl;
      assert (Hr:notred (Bk rl rx ry rr)) by (simpl; trivial);
      set (r:=Bk rl rx ry rr) in *; clearbody r; clear IHrl rl rx ry rr;
      specialize (IHlr r)
     |change (append _ _) with (Rd (append (Bk ll lx ly lr) rl) rx ry rr);
      assert (Hl:notred (Bk ll lx ly lr)) by (simpl; trivial);
      set (l:=Bk ll lx ly lr) in *; clearbody l; clear IHlr ll lx ly lr
     |specialize (IHlr rl); clear IHrl]]].

Fact append_rr_match ll lx ly lr rl rx ry rr :
 rspec
  (fun a x y b => Rd (Rd ll lx ly a) x y (Rd b rx ry rr))
  (fun t => Rd ll lx ly (Rd t rx ry rr))
  (append lr rl)
  (append (Rd ll lx ly lr) (Rd rl rx ry rr)).
Proof.
  exact (rmatch _ _ _).
Qed.

Fact append_bb_match ll lx ly lr rl rx ry rr :
 rspec
  (fun a x y b => Rd (Bk ll lx ly a) x y (Bk b rx ry rr))
  (fun t => lbalS ll lx ly (Bk t rx ry rr))
  (append lr rl)
  (append (Bk ll lx ly lr) (Bk rl rx ry rr)).
Proof.
  exact (rmatch _ _ _).
Qed.

Lemma append_spec1 l r x (y:val) :
 MaT x y (append l r) ↔ MaT x y l \/ MaT x y r.
Proof.
 revert r.
 append_tac l r; autorew; try tauto.
 - (* Red / Red *)
   revert IHlr; case append_rr_match;
    [intros a k v b | intros t Ht]; autorew; tauto.
 - (* Black / Black *)
   revert IHlr; case append_bb_match;
    [intros a k v b | intros t Ht]; autorew; intuition.
Qed.

Lemma append_spec2 l (r:mv) x :
 InT x (append l r) ↔ InT x l \/ InT x r.
Proof.
  revert r. append_tac l r; autorew; try tauto.
 - (* Red / Red *)
   revert IHlr; case append_rr_match;
    [intros a k v b | intros t Ht]; autorew; tauto.
 - (* Black / Black *)
   revert IHlr; case append_bb_match;
    [intros a k v b | intros t Ht]; autorew; intuition.
Qed.


Hint Rewrite append_spec1 append_spec2 : rb.

Lemma append_ok : forall x l r `{Ok l, Ok r},
 lt_tree x l -> gt_tree x r -> Ok (append l r).
Proof.
  append_tac l r; trivial.
  (* Leaf / _ *)
  (* _ / Leaf *)
  - (* Red / Red *)
    intros; inv.
    assert (IH : Ok (append lr rl)) by (apply IHlr; eauto). clear IHlr.
    assert (K.lt lx rx) by (transitivity x; eauto).
    assert (G : gt_tree lx (append lr rl)).
      { intros w. autorew. destruct 1; [|transitivity x]; eauto. }
    assert (L : lt_tree rx (append lr rl)).
      { intros w. autorew. destruct 1; [transitivity x|]; eauto. }
    revert IH G L; case append_rr_match; intros; ok.
 - (* Red / Black *)
   intros; ok.
   intros w; autorew; destruct 1; eauto.
 - (* Black / Red *)
   intros; ok.
   intros w; autorew; destruct 1; eauto.
 - (* Black / Black *)
   intros; inv.
   assert (IH : Ok (append lr rl)) by (apply IHlr; eauto). clear IHlr.
   assert (K.lt lx rx) by (transitivity x; eauto).
   assert (G : gt_tree lx (append lr rl)).
     { intros w. autorew. destruct 1; [|transitivity x]; eauto. }
   assert (L : lt_tree rx (append lr rl)).
     { intros w. autorew. destruct 1; [transitivity x|]; eauto. }
   revert IH G L; case append_bb_match; intros; ok.
    apply lbalS_ok; ok.
Qed.

(** ** Deletion *)

Lemma del_spec m x k `{Ok m} :
 InT k (del x m) ↔ InT k m ∧ ~keq k x.
Proof with order.
  induct m x.
  - intuition_in.
  - autorew; intuition_in;
    [ assert (K.lt k x') by eauto
    | assert (K.lt x' k) by eauto
    |]...
  - destruct l as [|[|] ll lx ly lr]; autorew;
    rewrite ?IHl by trivial; intuition_in...
  - destruct r as [|[|] rl rx ry rr]; autorew;
    rewrite ?IHr by trivial; intuition_in...
Qed.

Lemma del_spec' m x k v `{Ok m} :
 MaT k v (del x m) ↔ MaT k v m ∧ ¬keq k x.
Proof with order.
  induct m x.
  - intuition_in.
  - autorew; intuition_in;
    [ gen_in (@Mt2It val _ _ _ H9);
      assert (K.lt k x') by eauto
    | gen_in (@Mt2It val _ _ _ H9);
      assert (K.lt x' k) by eauto
    |]...
  - destruct l as [|[|] ll lx ly lr]; autorew;
    rewrite ?IHl by trivial; intuition_in;
    [| | | |destruct H5; simpl in *|]...
  - destruct r as [|[|] rl rx rr]; autorew;
    rewrite ?IHr by trivial; intuition_in;
    [| | | | |destruct H5; simpl in *]...
Qed. Hint Rewrite del_spec del_spec' : rb.

Instance del_ok m x `{Ok m} : Ok (del x m).
Proof with auto.
  induct m x...
  - apply (append_ok x')...
  -   assert (lt_tree x' (del x l)).
      { intro w. autorew; trivial. destruct 1. eauto. }
    destruct l as [|[|] ll lx ly lr]; auto_tc;
    intuition; ok.
  -   assert (gt_tree x' (del x r)).
      { intro w. autorew; trivial. destruct 1. eauto. }
    destruct r as [|[|] rl rx ry rr]; auto_tc;
    intuition; ok.
Qed.

Lemma remove_spec1 a x m `{Ok m} :
  keq a x → ¬In a (remove x m).
Proof.
  rwiit. unfold remove.
  autorew; tauto.
Qed.

Theorem remove_spec2 a x b m `{Ok m} :
  ¬keq a x → MapsTo a b m → MapsTo a b (remove x m).
Proof. intros. unfold remove. autorew; tauto. Qed.

Theorem remove_spec3 a x b m `{Ok m} :
  MapsTo a b (remove x m) → MapsTo a b m.
Proof. unfold remove, MapsTo. autorew; tauto. Qed.
Hint Resolve remove_spec2 remove_spec3.

Corollary remove_fact1 a x b m `{Ok m} :
MapsTo a b (remove x m) ↔ MapsTo a b m ∧ ¬keq a x.
Proof.
  intuition;
[ apply remove_spec3 with (x:=x)
| apply (remove_spec1 a x m);
  [|exists b]]; auto.
Qed.

Instance remove_ok x m `{Ok m} : Ok (remove x m).
Proof. unfold remove; auto_tc. Qed.

(** ** Treeify *)

Notation ifpred p n := (if p then pred n else n%nat).

Notation mvlkvp := (prod mv lkvp).
Notation treeify_t := (lkvp → mvlkvp).

Definition treeify_invariant size (f:treeify_t) :=
 ∀ acc, size <= length acc → let (t,acc') := f acc in
 cardinal t = size ∧ acc = elements t ++ acc'.

Lemma treeify_zero_spec : treeify_invariant 0 treeify_zero.
Proof. intro. simpl. auto. Qed.

Lemma treeify_one_spec : treeify_invariant 1 treeify_one.
Proof.
  intros [|x acc]; inversion 1;
  destruct x;simpl; auto.
Qed.

Lemma treeify_cont_spec f g size1 size2 size :
  treeify_invariant size1 f →
  treeify_invariant size2 g →
  size = S (size1 + size2) →
  treeify_invariant size (treeify_cont f g).
Proof with trivial.
  intros Hf Hg EQ acc LE. unfold treeify_cont.
    assert (H : size1 ≤ length acc).
    { transitivity size... subst. auto with arith. }
  specialize (Hf acc H). destruct
  (f acc) as (t1,[|x acc1]), Hf as (Hf1,Hf2).
  - exfalso. revert LE. apply Nat.lt_nge. subst. rewrite
    <- app_nil_end, <- elements_cardinal; auto with arith.
  - specialize (Hg acc1). destruct (g acc1) as (t2,acc2),
    Hg as (Hg1,Hg2).
    + revert LE. subst. rewrite app_length,
      <- elements_cardinal. simpl.
      rewrite Nat.add_succ_r, <- Nat.succ_le_mono.
      apply Nat.add_le_mono_l.
    + destruct x as [x y]. simpl. rewrite elements_node,
    app_ass. now subst.
Qed.


Lemma treeify_aux_spec n (p:bool) :
 treeify_invariant (ifpred p (Pos.to_nat n)) (treeify_aux p n).
Proof.
  revert p.
  induction n as [n|n|]; intros p; simpl treeify_aux.
  - eapply treeify_cont_spec; [ apply (IHn false) | apply (IHn p) | ].
    rewrite Pos2Nat.inj_xI. assert (H := Pos2Nat.is_pos n).
    apply Nat.neq_0_lt_0 in H. destruct p; simpl; intros;
    rewrite Nat.add_0_r; trivial. now rewrite <- Nat.add_succ_r,
    Nat.succ_pred; trivial.
  - eapply treeify_cont_spec; [ apply (IHn p) | apply (IHn true) | ].
    rewrite Pos2Nat.inj_xO. assert (H := Pos2Nat.is_pos n).
    apply Nat.neq_0_lt_0 in H. rewrite <- Nat.add_succ_r,
    Nat.succ_pred by trivial. destruct p; simpl; intros;
    rewrite Nat.add_0_r; trivial. symmetry.
    now apply Nat.add_pred_l.
  - destruct p;
    [ apply treeify_zero_spec
    | apply treeify_one_spec].
Qed.

Lemma plength_aux_spec (l:lkvp) p :
  Pos.to_nat (plength_aux l p) = length l + Pos.to_nat p.
Proof.
 revert p. induction l; simpl; trivial.
 intros. now rewrite IHl, Pos2Nat.inj_succ, Nat.add_succ_r.
Qed.

Lemma plength_spec (l:lkvp) : Pos.to_nat (plength l) = S (length l).
Proof.
 unfold plength. rewrite plength_aux_spec. apply Nat.add_1_r.
Qed.

Lemma treeify_elements (l:lkvp) : elements (treeify l) = l.
Proof.
  assert (H := treeify_aux_spec (plength l) true l).
  unfold treeify, ev. destruct (@treeify_aux val) as (t,acc);
  simpl in *. destruct H as (H,H'). { now rewrite plength_spec. }
  subst l. rewrite plength_spec, app_length,
  <- (@elements_cardinal val) in *. destruct acc.
  * now rewrite app_nil_r.
  * exfalso. revert H. simpl.
    rewrite Nat.add_succ_r, Nat.add_comm.
    apply Nat.succ_add_discr.
Qed.

Lemma treeify_spec x y l : MaT x y (treeify l) <-> InA kvpeq (x,y) l.
Proof.
 intros. now rewrite
 <- elements_spec1', treeify_elements.
Qed.


Notation mapfst := (List.map (@fst key val)).
Lemma HR_kvp_k x lst :
HdRel kvplt x lst → HdRel klt (fst x) (mapfst lst).
Proof with auto.
  induction lst; intro; simpl;[left | right].
  clear_inversion H. red in H1...
Qed. Hint Resolve HR_kvp_k.

Lemma sorted_kvp_k lst :
sort kvplt lst → sort klt (mapfst lst).
Proof with auto.
  induction lst; intros; simpl;
  [constructor|clear_inversion H; right]...
Qed.

Lemma InA_kvp_k x lst:
InA kvpeq x lst → InA keq (fst x) (mapfst lst).
Proof with auto.
  induction lst; intros; simpl;
  clear_inversion H; [left|
  destruct H1]...
Qed.

Lemma sorted_app_inv_mf l1 l2 :
  sort kvplt (l1++l2) →
  sort kvplt l1 ∧ sort kvplt l2 ∧
  ∀ (x1 x2:kvp), InA keq (fst x1) (mapfst l1) →
  InA keq (fst x2) (mapfst l2) → klt (fst x1) (fst x2).
Proof with auto.
  induction l1 as [|(a,b) l1 IHl1].
 - simpl; repeat split...
   intros. now rewrite InA_nil in *.
 - simpl. inversion_clear 1 as [ | ? ? Hs Hhd ].
   destruct (IHl1 Hs) as (H1&H2&H3).
   repeat split...
   * constructor...
     destruct l1; simpl in *; inversion_clear Hhd...
   * intros (x1,y1) (x2,y2) Hx1 Hx2.
     apply InA_cons in Hx1. destruct Hx1...
     simpl in *. rewrite H.
     apply sorted_kvp_k in Hs. apply sorted_kvp_k in H1.
     apply sorted_kvp_k in H2. apply HR_kvp_k in Hhd. simpl.
     apply SortA_InfA_InA with (eqA:=keq)(l:=(mapfst (l1++l2)));
     auto_tc. rewrite map_app. rewrite InA_app_iff; auto_tc.
Qed.


Lemma sorted_app_inv l1 l2 :
 sort kvplt (l1++l2) →
 sort kvplt l1 ∧ sort kvplt l2 ∧
 ∀ x1 x2, InA kvpeq x1 l1 → InA kvpeq x2 l2 → klt (fst x1) (fst x2).
Proof with auto.
  intros. destruct (sorted_app_inv_mf _ _ H)
  as (H1 & H2 & H3). repeat split...
  intros; apply H3; apply InA_kvp_k...
Qed.

Lemma InA_pk_k x lst :
InA pkeq x lst <-> InA keq (fst x) (mapfst lst).
Proof with auto.
  induction lst; split; intros H; clear_inversion H;
  simpl; [|right; apply IHlst| |right; apply IHlst]...
Qed.

Lemma sorted_app_inv' l1 l2 :
 sort kvplt (l1++l2) →
 sort kvplt l1 ∧ sort kvplt l2 ∧
 ∀ x1 x2, InA pkeq x1 l1 → InA pkeq x2 l2 → klt (fst x1) (fst x2).
Proof with auto.
  intros. destruct (sorted_app_inv_mf _ _ H)
  as (H1 & H2 & H3). repeat split...
  intros; apply H3; rewrite <- InA_pk_k...
Qed.

(*
Lemma sorted_app_inv l1 l2 :
 sort kvplt (l1++l2) →
 sort kvplt l1 ∧ sort kvplt l2 ∧
 ∀ x1 x2, InA kvpeq x1 l1 → InA kvpeq x2 l2 → kvplt x1 x2.
Proof with auto.
  intros. destruct (sorted_app_inv_mf _ _ H)
  as (H1 & H2 & H3). repeat split...
  intros; apply H3; apply InA_kvp_k...
Qed.

(*
Lemma sorted_app_inv_diff l1 l2 :
  sort kvplt (l1++l2) →
  sort kvplt l1 ∧ sort kvplt l2 ∧
  ∀ x1 x2, InA kvpeq x1 l1 →
  InA keq (fst x2) (mapfst l2) → kvplt x1 x2.
Proof with auto.
  intros. destruct (sorted_app_inv' _ _ H)
  as (H1 & H2 & H3). repeat split...
  intros; apply H3... apply InA_kvp_k...
Qed.
*) *)

Lemma sorted_app_inv_diff l1 l2 :
  sort kvplt (l1++l2) →
  sort kvplt l1 ∧ sort kvplt l2 ∧
  ∀ x1 x2, InA keq (fst x1) (mapfst l1) →
  InA kvpeq x2 l2 → kvplt x1 x2.
Proof with auto.
  intros. destruct (sorted_app_inv_mf _ _ H)
  as (H1 & H2 & H3). repeat split...
  intros; apply H3... apply InA_kvp_k...
Qed.

Lemma elements_sort_ok m : sort kvplt (elements m) -> Ok m.
Proof.
 induction m as [|c l IHl x y r IHr].
 - constructor.
 - rewrite elements_node.
   intros H. destruct (sorted_app_inv _ _ H) as (H1 & H2 & H3).
   inversion_clear H2.
   constructor; ok.
   * intros k Hk. rwiti in Hk.
     destruct Hk as [v ?]. apply (H3 (k,v) (x,y)).
     + now rewrite elements_spec1'.
     + rewrite InA_cons. now left.
   * intros k Hk. rwiti in Hk. destruct Hk as [v ?].
     change (kvplt (x,y) (k,v)).
     apply SortA_InfA_InA with (eqA:=kvpeq)(l:=elements r)
     (x := (k,v)) (a := (x,y)); auto_tc.
     now rewrite elements_spec1'.
Qed.

Lemma treeify_ok l : sort kvplt l → Ok (treeify l).
Proof.
 intros. apply elements_sort_ok. rewrite treeify_elements; auto.
Qed.


(** ** Filter *)

Lemma filter_app A f (l l':list A) :
 List.filter f (l ++ l') = List.filter f l ++ List.filter f l'.
Proof.
 induction l as [|x l IH]; simpl; trivial.
 destruct (f x); simpl; now rewrite IH.
Qed.


Notation unc := (@prod_curry key val bool).
Lemma filter_aux_elements s f acc :
 filter_aux f s acc = List.filter (unc f) (elements s) ++ acc.
Proof.
 revert acc. induction s as [|c l IHl x y r IHr];
 simpl; trivial. intros acc. unfold prod_curry.
 rewrite elements_node, filter_app. simpl.
 destruct (f x y); now rewrite IHl, IHr, app_ass.
Qed.

Lemma filter_elements f m :
 elements (filter f m) = List.filter (unc f) (elements m).
Proof.
  unfold filter. now rewrite treeify_elements,
  filter_aux_elements, app_nil_r.
Qed.

Lemma filter_spec' x y (m:mv) P : Proper (keq==>Logic.eq==>Logic.eq) P →
  (MapsTo x y (filter P m) ↔ MapsTo x y m ∧ P x y = true).
Proof.
  intros H. rewrite <- elements_spec1',
  filter_elements, filter_InA, elements_spec1';
  auto_tc. - intuition. - intros (a,a') (b,b')
  (H0,H1). unfold prod_curry. simpl in *.
  rewrite H0, H1. trivial.
Qed.
Definition filter_spec x y (m:mv) P `{Ok m} := filter_spec' x y m P.


Instance filter_ok f m `(Ok m) : Ok (filter f m).
Proof.
 apply elements_sort_ok.
 rewrite filter_elements.
 apply filter_sort with kvpeq; auto_tc.
Qed.


Lemma partition_aux_spec (m:mv) P acc1 acc2 :
 partition_aux P m acc1 acc2 =
  (filter_aux P m acc1, filter_aux (λ k v, negb (P k v)) m acc2).
Proof with auto.
  revert acc1 acc2.
  induction m as [ | c l Hl x y r Hr ]; simpl...
  intros acc1 acc2.
  destruct (P x y); simpl; now rewrite Hr, Hl.
Qed.


Lemma partition_spec1 m P : compatb P → (fst (partition P m)) [=] (filter P m).
Proof.
  intro. unfold partition, filter, Equal.
  rewrite partition_aux_spec. simpl; intuition.
Qed.

Notation neg := (λ P x y, negb (P x y)).
Lemma partition_spec2 m P : compatb P →
  snd (partition P m) [=] filter (neg P) m.
Proof.
  intro. unfold partition, filter, Equal.
  rewrite partition_aux_spec. simpl; intuition.
Qed.

Lemma partition_spec m P : let (x,y) := partition P m in compatb P →
      x [=] filter P m ∧ y [=] filter (neg P) m.
Proof.
  generalize (partition_spec1 m P),
  (partition_spec2 m P); intros.
  destruct (partition P m) as (x,y).
  split; auto.
Qed.


Instance partition_ok1 P m `(Ok m) : Ok (fst (partition P m)).
Proof.
  unfold partition. rewrite partition_aux_spec,
  filter_aux_elements, List.app_nil_r. simpl.
  apply treeify_ok, filter_sort with kvpeq; auto.
Qed.

Instance partition_ok2 P m `(Ok  m) : Ok (snd (partition P m)).
Proof.
  unfold partition. rewrite partition_aux_spec,
  (filter_aux_elements m (neg P)), List.app_nil_r.
  simpl. apply treeify_ok, filter_sort with kvpeq; auto.
Qed.


(* fromList *)

Open Scope positive.
Lemma sl_aux_fst_spec x y (t:lkvp) acc :
  fst (sl_aux x t acc) = true → sort kvplt ((x,y) :: t).
Proof with auto.
  revert x y acc. induction t...
  intros x y (b, len) H. destruct a as [a a'].
  unfold sl_aux in H. elim_compare x a.
  + inversion H.
  + right... apply (IHt _ _ (b,len+1))...
  + inversion H.
Qed.

Lemma sorted_length_fst_spec t :
fst (sorted_length t) = true → sort kvplt t.
Proof with auto.
  induction t...
  intro. destruct a as [a a'].
  unfold sorted_length in H.
  apply sl_aux_fst_spec with (acc:=(true,2))...
Qed.


Lemma plength_aux_1_plus (l:lkvp) p :
  (plength_aux l (1 + p)) = plength l + p.
Proof with auto.
  revert p. induction l;
  unfold plength...
  intro. remember (1+p) as p'.
  simpl; subst.
  rewrite <- (Pos.add_1_l (1+p)).
  rewrite (IHl (1+p)). replace 2 with (1+1)...
  rewrite (IHl 1). rewrite Pos.add_assoc...
Qed.


Lemma plength_cons h (t:lkvp) :
plength (h :: t) = 1 + plength t.
Proof with auto.
  unfold plength at 1.
  remember (1 + plength t) as Malcolm.
  simpl. replace 2 with (1+1)...
  rewrite plength_aux_1_plus; subst.
  rewrite Pos.add_comm...
Qed.


Lemma sl_aux_cons (t:lkvp) h h' b p : Sorted kvplt ((h,h') :: t) →
  snd (sl_aux h t (b,2+p)) = (snd (sorted_length ((h,h') :: t)) + p).
Proof with auto.
  revert b h h' p. induction t; [reflexivity |].
  intros. clear_inversion H. clear_inversion H3.
  destruct a as [a a']. red in H0. simpl in H0.
  remember (2+p) as P. simpl. rewrite (kcLt H0).
  subst. rewrite <- (Pos.add_assoc 2 p 1).
  rewrite (IHt b a a' (p+1) H2).
  replace 3 with (2+1)...
  rewrite (IHt true a a' 1 H2).
  rewrite (Pos.add_comm p), Pos.add_assoc...
Qed.

Lemma sort_fact1 {h x t} :
sort kvplt (h :: x :: t) → sort kvplt (h :: t).
Proof with auto.
  induction t; inversion 1...
  subst. clear_inversion H2. right...
  right. destruct (@Kvplt_strord val).
  transitivity x. inversion H3... inversion H5...
Qed.

Lemma sl_length_cons h (t:lkvp) : Sorted kvplt (h :: t) →
snd (sorted_length (h :: t)) = 1 + snd (sorted_length t).
Proof with auto.
  revert h. induction t; destruct h as [h h'];
  [reflexivity |].
  intros. gen_in (sort_fact1 H).
  clear_inversion H. clear_inversion H4.
  destruct a as [a a']. red in H1. simpl in H1.
  remember (1 + snd (sorted_length ((a,a') :: t))).
  simpl. rewrite (kcLt H1). replace 3 with (2+1)...
  rewrite (sl_aux_cons t a a' true 1 H3); subst.
  rewrite Pos.add_comm...
Qed.
  


Lemma sorted_length_spec (lst:lkvp) :
  fst (sorted_length lst) = true →  
  snd (sorted_length lst) = plength lst.
Proof with auto.
  gen_in (sorted_length_fst_spec lst).
  destruct (fst (sorted_length lst));
  [|inversion 1]. assert (Sorted kvplt lst)...
  clear H. intro H; clear H. induction lst...
  rewrite plength_cons, sl_length_cons...
  clear_inversion H0. rewrite (IHlst H2)...
Qed.

Notation cur := (λ f t kv , f (fst kv) (snd kv) t).
Instance fold_left_add_ok lst m `{Ok m} : Ok (fold_left (cur add) lst m).
Proof with auto.
  generalize dependent m.
  induction lst...
  intros. induction m; simpl;
  apply IHlst; auto_tc.
Qed.

(*
Instance fold_left_add_mt lst m `{Ok m} : MaT (fold_left (cur add) lst m).
Proof with auto.
  generalize dependent m.
  induction lst...
  intros. induction m; simpl;
  apply IHlst; auto_tc.
Qed. *)

(*
Lemma bob x y (l:lkvp) :
min_elt (treeify ((x,y) :: l)) = Some (x,y).
Proof with auto.
  induction l... rewrite <- IHl.
  unfold treeify. remember plength 
  compute.
  unfold treeify.
*)
(*
treeify_spec x y l : MaT x y (treeify l) <-> InA kvpeq (x,y) l.
*)


Lemma kvp_pk x l :
InA kvpeq x l → InA pkeq x l.
Proof with auto.
  induction l; inversion 1; subst.
  - left. destruct H1...
  - right. apply IHl...
Qed.

Lemma pk_kvp x y l :
InA pkeq (x,y) l → exists y, InA kvpeq (x,y) l.
Proof with auto.
  induction l; inversion 1; subst.
  - exists (snd a). left...
  - destruct IHl... exists x0. right...
Qed.

Lemma fromList_spec1_sorted x (lst:lkvp) :
In x (treeify lst) ↔ ∃y, InA pkeq (x,y) lst.
Proof with auto.
  split; destruct 1 as [y H].
  - exists y. apply kvp_pk.
    rewrite <- treeify_spec...
  - destruct (pk_kvp x y lst)...
    exists x0. rewrite treeify_spec...
Qed.

Hint Immediate add_spec1' add_spec1.

Lemma fromList_spec1_unsorted x lst (acc:mv) :
In x (fold_left (cur add) lst acc) ↔
 (∃y, InA pkeq (x,y) lst \/ In x acc).
Proof with auto.
  revert acc. induction lst; simpl. {
  destruct acc.
  - split; destruct 1;
    inversion H... inversion H0.
  - split; intros. + exists v...
    + destruct H as [y [H|H]]...
      inversion H. }
  intros acc; split.
  - intros H. apply IHlst in H.
    destruct H as [y [H|H]].
    + exists y. left...
    + exists y. destruct H as [x' H], a as [a b].
      simpl in H. destruct (keqd x a) as [Heq|Heq].
      left... rewrite add_spec2' in H...
      right. exists x'...
  - destruct 1 as [y [H|H]].
    + rewrite IHlst. clear_inversion H.
      * red in H1. exists y. right.
        exists (snd a). rewrite H1...
      * exists y. left...
    + rewrite IHlst.
      destruct (keqd x (fst a)) as [Heq|Heq]; exists y; right.
      * exists (snd a). rewrite Heq...
      * destruct H as [x' H]. exists x'. rewrite add_spec2'...
Qed.

Theorem fromList_spec1 x (lst:lkvp) :
 In x (fromList lst) ↔ ∃ y, InA pkeq (x,y) lst.
Proof with auto.
  unfold fromList. gen_in (sorted_length_spec lst).
  destruct (sorted_length lst) as [[|] len].
  - simpl in *. rewrite H... apply fromList_spec1_sorted.
  - clear H len. induction lst; simpl.
    + intuition_in; inversion H. inversion H0.
    + split; intros.
      * rewrite fromList_spec1_unsorted in H.
        destruct H as [y [H|H]]; eauto. inv.
        unfold add in H. simpl in H.
        clear_inversion H; try inversion H1...
        exists y. left...
      * rewrite fromList_spec1_unsorted.
        destruct H as [y H]. clear_inversion H;
        [|exists y; left]... exists y. right.
        exists (snd a); red in H1. rewrite H1...
Qed.

Lemma fromList_spec2_unsorted x lst y (acc:mv) `{Ok acc}:
MaT x y (fold_left (cur add) lst acc) →
 InA kvpeq (x,y) lst ∨ MaT x y acc.
Proof with auto.
  generalize dependent acc. induction lst; simpl.
  { destruct acc... }
  intros acc Ok_ H. apply IHlst in H; auto_tc.
  destruct H as [H|H].
  - left. right...
  - destruct a as [a b]. destruct (keqd x a)
    as [Heq|Heq]; simpl in H.
    + do 2 left. rewrite Heq in H. unfold add in H.
      rewrite makeBlack_spec1 in H.
      rewrite (ins_spec3 _ _ _ _ H). split...
    + right. rewrite add_spec2' in H...
Qed.

Theorem fromList_spec2 x y lst :
  MapsTo x y (fromList lst) → InA kvpeq (x,y) lst.
Proof with auto.
  unfold fromList. gen_in (sorted_length_spec lst).
  destruct (sorted_length lst) as [[|] len].
  - simpl in *. rewrite H, (treeify_spec x y lst)...
  - clear H. revert x y. induction lst; simpl.
    + inversion 1.
    + intros. destruct (fromList_spec2_unsorted _ _ _ _ H);
      auto_tc. left. unfold add in H0. simpl in H0.
      inversion H0 ; try inversion H2. split...
Qed.


Lemma fromList_spec3_unsorted1 x (y:val) lst (acc:mv) :
¬InA pkeq (x,y) lst → MaT x y acc →
MaT x y (fold_left (cur add) lst acc).
Proof with auto.
  generalize dependent acc. induction lst; simpl...
  - intros. destruct (keqd x (fst a)).
    + destruct H. left. simpl...
    + apply IHlst; auto_tc.
      rewrite add_spec2'...
Qed.

Lemma fls3lemmaa a (b:val) lst m m2 `{Ok m, Ok m2} :
m [=] m2 → MaT a b (fold_left (cur add) lst m) →
MaT a b (fold_left (cur add) lst m2).
Proof with auto.
  revert m m2 Ok0 Ok1.
  induction lst;[|destruct a0 as (x,y)];
  simpl; intros. red in H. rewrite <- H...
  apply IHlst with (add x y m); auto_tc.
  intros k v. clear IHlst H0. destruct (keqd k x).
  - rewrite e. split; intro;
    rewrite (add_fact1 _ _ _ _ H0)...
  - repeat rewrite add_spec2'...
Qed.


Lemma fls3lemmab x a y b (m:mv) `{Ok m} :
¬keq a x → add x y (add a b m) [=] add a b (add x y m).
Proof with auto.
  generalize add_spec2', add_fact1; intros U V.
  intros Ne k v. destruct (keqd k a), (keqd k x);
[ order
| rewrite (U k), e;[split; intro H; rewrite (V a v b _ _ H)|]
| rewrite (U k a), e; [split; intro H; rewrite (V x v y _ _ H)|]
| rewrite !U; auto; split ]...
Qed. Hint Resolve fls3lemmab.

Lemma fromList_spec3_unsorted2 x a (y b:val) lst (acc:mv) `{Ok acc}:
¬InA pkeq (x,y) lst → ¬keq x a →
MaT a b (fold_left (cur add) lst acc) →
MaT a b (fold_left (cur add) lst (add x y acc)).
Proof with auto_tc.
  generalize dependent acc.
  induction lst; simpl; intros;
  [rewrite add_spec2'|]...
  destruct a0 as (k,v); simpl in *.
  destruct (keqd x k).
  - destruct H. left...
  - apply fls3lemmaa with (add x y (add k v acc))...
Qed.


Theorem fromList_spec3 x y (lst:lkvp) : NoDupA pkeq lst →
 InA kvpeq (x,y) lst → MapsTo x y (fromList lst).
Proof with auto.
  unfold fromList. gen_in (sorted_length_spec lst).
  destruct (sorted_length lst) as [[|] len]; intros.
  - simpl in H. rewrite H... fold (@treeify val lst).
    rewrite treeify_spec...
  - clear H len. induction lst;[inversion H1|]. simpl.
    destruct a as (a,b); simpl. clear_inversion H1.
    + destruct H2; simpl in *. rewrite H, H1.
      apply fromList_spec3_unsorted1; auto_tc;
      clear_inversion H0...
    + clear_inversion H0.
      apply fromList_spec3_unsorted2; auto_tc;[|apply IHlst]...
      intro. apply H3. clear IHlst H4. induction lst;
      clear_inversion H2; [left|right; apply IHlst]...
      destruct H1; red; simpl. rewrite H...
Qed.


Instance fromList_ok (lst:lkvp) : Ok (fromList lst).
Proof with auto.
  unfold fromList.
  gen_in (sorted_length_spec lst).
  gen_in (sorted_length_fst_spec lst).
  destruct (sorted_length lst) as (b,len).
  simpl in *. destruct b.
  - gen_in (treeify_ok _ (H0 (Logic.eq_refl _))).
    unfold treeify in H1. rewrite H...
  - apply fold_left_add_ok; constructor.
Qed.



Ltac inA := rewrite ?InA_app_iff, ?InA_cons, ?InA_nil, ?InA_rev in *; auto_tc.

(** ** diff correctness*)
Lemma diff_list_spec x y l1 l2 acc :
 sort kvplt (rev l1) →
 sort kvplt (rev l2) →
 (InA kvpeq (x,y) (diff_list l1 l2 acc) ↔
   (InA kvpeq (x,y) l1 ∧ ¬InA keq x (List.map (@fst key val) l2)) ∨ InA kvpeq (x,y) acc).
Proof with auto.
  revert l2 acc.
  induction l1 as [|(a,b) l1 IH1].
  - intros l2 acc; simpl. inA. tauto.
  - induction l2 as [|(c,d) l2 IH2]; intros acc.
   * intros; simpl. rewrite rev_append_rev. inA. tauto.
   * simpl. intros U V.
     destruct (sorted_app_inv _ _ U) as (U1 & U2 & U3)...
     destruct (sorted_app_inv_diff _ _ V) as (V1 & V2 & V3)...
     case K.compare_spec; intro C.
     + rewrite IH1... f_equiv. inA. intuition;
       [assert (kvplt (x,y) (a,b)) by (apply U3; inA);
        red in H; simpl in H | destruct H, H0; simpl in H]; order.
     + rewrite (IH2 acc)... f_equiv. inA. intuition;
       [destruct H; simpl in H | assert (kvplt (x,y) (a,b))
        by (apply U3; inA); red in H0; simpl in H0]; order.
     + rewrite IH1... inA. intuition; [
       left; split;[|destruct 1; apply H1; [left|simpl; right]]

     | left; split; auto; destruct 1, H; simpl in *; [|
       assert (kvplt (x,y) (c,d)) by (apply V3; rewrite ?map_rev; inA);
       red in H2; simpl in H2]; order

     | left; split; [|
       intro; apply H2; clear_inversion H1;
       [contradiction|]]
     ]...
Qed.


Lemma linear_diff_spec m1 m2 x y `(Ok m1, Ok m2) :
  MaT x y (linear_diff m1 m2) ↔ MaT x y m1 ∧ ¬In x m2.
Proof with auto_tc.
  unfold linear_diff. rewrite !rev_elements_rev, treeify_spec,
  diff_list_spec by (rewrite rev_involutive; auto_tc).
  rewrite map_rev, <- kele_mfele, !InA_rev, InA_nil,
  !kelements_spec1 by auto_tc. intuition.
  - rewrite <- elements_spec1'...
  - left; split... rewrite elements_spec1'...
Qed.


Lemma fold_remove_spec x y (m1 m2:mv) `(Ok m2) :
  MaT x y (foldl (λ k v, remove k) m1 m2) ↔ MaT x y m2 ∧ ¬InT x m1.
Proof with auto.
  rewrite foldl_spec', <- fold_left_rev_right.
  rwiti. rewrite <- (kelements_spec1'), <- InA_rev by auto_tc.
  rewrite kele_mfele, <- map_rev.
  induction (rev (elements m1)); simpl.
  - rewrite InA_nil. intuition.
  - unfold compose, flip, prod_curry in *.
    destruct a as (a,b). simpl. rewrite remove_fact1,
    IHl, InA_cons; [tauto|]. clear IHl.
    induction l;[|destruct a0]; simpl; auto_tc.
Qed.

Local Instance mem_proper m `(Ok m) :
Proper (keq ==> eq) (λ k, mem k m).
Proof.
  intros x y EQ. apply Bool.eq_iff_eq_true;
  rewrite !mem_spec; auto. now split;
  destruct 1 as [v H]; exists v;
  [rewrite EQ in H | rewrite EQ].
Qed.

Theorem diff_spec x y m m2 `{Ok m, Ok m2} :
 MaT x y (diff m m2) ↔ MaT x y m ∧ ¬In x m2.
Proof.
 unfold diff. destruct @compare_bheight.
 - now apply linear_diff_spec.
 - rewrite filter_spec, Bool.negb_true_iff,
     <- Bool.not_true_iff_false, mem_spec;
    intuition.
    intros x1 x2 EQk y1 y2 EQv. f_equal. now apply mem_proper.
 -  rwiit. now apply fold_remove_spec.
Qed.
(** ** end diff correctness*)



(** ** inter correctness*)

Lemma inter_list_spec1 sl x y b l1 l2 acc :
 sort kvplt (rev l1) →
 sort kvplt (rev l2) →
 (InA kvpeq (x,sl x y b) (inter_list sl l1 l2 acc) →
   (∃ (y b:val), InA kvpeq (x,y) l1 ∧ InA kvpeq (x,b) l2)
    ∨ InA kvpeq (x,sl x y b) acc).
Proof with auto.
  revert l2 acc. induction l1 as [|(x1,y1) l1 IH1]. 
  - intros l2 acc; simpl. inA.
  - induction l2 as [|(x2,y2) l2 IH2]; intros acc; simpl;[inA|].
    simpl. intros U V.
    destruct (sorted_app_inv _ _ U) as (U1 & U2 & U3); auto.
    destruct (sorted_app_inv _ _ V) as (V1 & V2 & V3); auto.
    case K.compare_spec; intro C.
    + intros. apply IH1 in H...
      destruct H as [(v1&v2&H&H')|H].
      * left. exists v1, v2. inA...
      * clear_inversion H... destruct H1.
        left; exists y1, y2. inA. split; left;
        split... simpl in *; order.
    + intros. apply IH2 in H... destruct H as [(v1&v2&H&H')|]...
      clear_inversion H.
      * destruct H1; simpl in *.
        left; exists y1, v2; split;[left|right]...
      * left; exists v1, v2; split...
    + intros. apply IH1 in H... destruct H as [(v1&v2&H&H')|]...
      clear_inversion H'.
      * destruct H1; simpl in *.
        left; exists v1, y2; split; [right|left]...
      * left; exists v1, v2; split...
Qed.

Lemma inter_list_spec2 sl x y b l1 l2 acc :
 Proper (keq==>Logic.eq==>Logic.eq==>Logic.eq) sl →
 sort kvplt (rev l1) →
 sort kvplt (rev l2) →
 InA kvpeq (x,y) l1 ∧ InA kvpeq (x,b) l2 ∨ InA kvpeq (x,sl x y b) acc →
 InA kvpeq (x,sl x y b) (inter_list sl l1 l2 acc).
Proof with auto.
  revert l2 acc. induction l1 as [|(x1,y1) l1 IH1]. 
  - intros l2 acc; simpl. inA. destruct 3; tauto.
  - induction l2 as [|(x2,y2) l2 IH2]; intros acc; simpl;[inA; tauto|].
    intros compatb U V.
    destruct (sorted_app_inv _ _ U) as (U1 & U2 & U3); auto.
    destruct (sorted_app_inv _ _ V) as (V1 & V2 & V3); auto.
    case K.compare_spec; intro C; inA.
    + intros [[[L|R] [L'|R']]| H]; apply IH1...
      * right. left. destruct L, L'; split;
        simpl in *; subst... rewrite H...
      * assert (klt (fst (x,b)) (fst (x2,y2)))
        by (apply V3; inA). destruct L;
        simpl in *; order.
      * assert (klt (fst (x,y)) (fst (x1,y1)))
        by (apply U3; inA). destruct L';
        simpl in *; order.
    + intros H. apply IH2...
      destruct H as [[[L|R] [L'|R']]|]...
      * destruct L, L'; simpl in *; order.
      * assert (klt (fst (x,y)) (fst (x1,y1)))
        by (apply U3; inA). destruct L';
        simpl in *; order.
    + intros H. apply IH1...
      destruct H as [[[L|R] [L'|R']]|]...
      * destruct L, L'; simpl in *; order.
      * assert (klt (fst (x,b)) (fst (x2,y2)))
        by (apply V3; inA). destruct L;
        simpl in *; order.
Qed.

Lemma linear_inter_spec1 (sl:key->val->val->val) x y b (m1:mv) m2 `{Ok m1, Ok m2} :
 MapsTo x (sl x y b) (linear_inter sl m1 m2) →
   In x m1 ∧ In x m2.
Proof with auto.
  unfold linear_inter. rewrite treeify_spec.
  intro. apply inter_list_spec1 in H; try
  (rewrite rev_elements_rev, rev_involutive;
  apply elements_spec2)...
  destruct H as [(v1&v2&H&H')|H];[|inversion H].
  split; [exists v1|exists v2]; apply elements_spec1',
  InA_rev; auto; rewrite <- rev_elements_rev...
Qed.

Lemma linear_inter_spec2 (sl:key->val->val->val) x y b (m1:mv) m2 `{Ok m1, Ok m2} :
 Proper (keq==>Logic.eq==>Logic.eq==>Logic.eq) sl →
 MapsTo x y m1 ∧ MapsTo x b m2 →
 MapsTo x (sl x y b) (linear_inter sl m1 m2).
Proof with auto.
  unfold linear_inter. intros compatb [H H'].
  apply treeify_spec, inter_list_spec2; try
  (rewrite rev_elements_rev, rev_involutive;
  apply elements_spec2)... left; split;
  rewrite rev_elements_rev; apply InA_rev;
  [auto| |auto|]; apply elements_spec1'...
Qed.



Theorem inter_spec1 x b y m m2 (sl:key→val→val→val) `{Ok m, Ok m2} :
  MapsTo x (sl x y b) (inter sl m m2) →
  In x m ∧ In x m2.
Proof with auto.
  unfold inter.
  - apply linear_inter_spec1...
Qed.


Theorem inter_spec2 x b y m m2 (sl:key→val→val→val) `{Ok m, Ok m2} :
Proper (keq==>eq==>eq==>eq) sl
→ MapsTo x y m ∧ MapsTo x b m2 → MapsTo x (sl x y b) (inter sl m m2).
Proof with auto.
  unfold inter.
  - apply linear_inter_spec2...
Qed.

Lemma filter_inter_aux_spec1 (X:Type) x y b (sl:key->val->val->X)
      sub min acc `{Ok min, Ok sub} :
InA (Kvpeq X) (x,sl x y b) (filter_inter_aux (X:=X) sl sub min acc) →
  (∃ y b, MapsTo x y min ∧ MapsTo x b sub) ∨
  InA (Kvpeq X) (x,sl x y b) acc.
Proof with auto.
  revert acc. induction min as [|c l IHl k v r IHr];
  simpl; intros; [right|]... remember (find k sub) as EQ.
  symmetry in HeqEQ. destruct EQ.
  - apply IHl in H; [|ok]. destruct H as [(v1&v2&H&H')|H].
    + left; exists v1, v2; split...
    + clear_inversion H. destruct H1; simpl in *.
      * left; exists v, v0. rewrite !H. split...
        apply find_spec...
      * apply IHr in H1;[|ok]. destruct H1 as [(v1&v2&H&H0)|H];
        [ left; exists v1, v2; split;[inn|]
        | right]...
  - apply IHl in H;[|ok]. destruct H as [(v1&v2&H&H')|H].
    + left; exists v1, v2; split...
    + apply IHr in H;[|ok]. destruct H as [(v1&v2&H&H')|H].
      * left; exists v1, v2. split...
      * right...
Qed.


Theorem linear_inter_spec (sl:key->val->val->val) x (m1:mv) m2 `{Ok m1, Ok m2} :
 Proper (keq==>Logic.eq==>Logic.eq==>Logic.eq) sl →
 ((∃ y b, MapsTo x (sl x y b) (inter sl m1 m2)) ↔
   In x m1 ∧ In x m2).
Proof with auto.
  intros compat; split; intros H.
  - destruct H as (y&b&H);
    apply inter_spec1 in H...
  - destruct H as [(y&H) (b&H')];
    exists y, b; apply inter_spec2...
Qed.


Theorem inter_spec x (m m2:mv) (sl:key→val→val→val) `{Ok m, Ok m2} :
Proper (keq==>Logic.eq==>Logic.eq==>Logic.eq) sl →
((∃ y b, MapsTo x (sl x y b) (inter sl m m2)) ↔ In x m ∧ In x m2).
Proof with auto.
  unfold inter.
   - apply linear_inter_spec...
Qed.


(** ** end inter correctness*)

(** ** union correctness*)

Lemma union_list_spec1 x y l1 l2 acc :
 sort kvplt (rev l1) →
 sort kvplt (rev l2) →
 InA kvpeq (x,y) (union_list l1 l2 acc) →
 (InA kvpeq (x,y) l1 ∨ InA kvpeq (x,y) l2) ∨ InA kvpeq (x,y) acc.
Proof with auto.
  revert l2 acc. induction l1 as [|(x1,y1) t1 IH1]; simpl.
  - intros. rewrite rev_append_rev in H1. inA; tauto.
  - induction l2 as [|(x2,y2) t2 IH2]; simpl; [intros;
    rewrite rev_append_rev in H1; inA; tauto|].
    intros acc U V.
    destruct (sorted_app_inv _ _ U) as (U1&_&U3)...
    destruct (sorted_app_inv _ _ V) as (V1&_&V3)...
    case K.compare_spec; intro C; intro H;
  [ apply IH1 in H
  | apply IH2 in H
  | apply IH1 in H]; inA; tauto.
Qed.

Lemma union_list_spec2 x y l1 l2 acc :
 sort kvplt (rev l1) →
 sort kvplt (rev l2) →
 (InA kvpeq (x,y) l1 ∨
 ((∀v,¬InA kvpeq (x,v) l1) ∧ InA kvpeq (x,y) l2)) ∨
  InA kvpeq (x,y) acc →
 InA kvpeq (x,y) (union_list l1 l2 acc).
Proof with auto.
  revert l2 acc. induction l1 as [|(x1,y1) t1 IH1]; simpl.
  - intros. rewrite rev_append_rev. inA; tauto.
  - induction l2 as [|(x2,y2) t2 IH2]; simpl; [intros;
    rewrite rev_append_rev; inA; tauto|].
    intros acc U V.
    destruct (sorted_app_inv _ _ U) as (U1 & U2 & U3)...
    destruct (sorted_app_inv _ _ V) as (V1 & V2 & V3)...
    case K.compare_spec; intro C; intro H.
    + apply IH1; inA. destruct H as [[[|]|[? [|]]]|]...
      * destruct (H y1). left; split...
        rewrite (proj1 H0). simpl; symmetry...
      * left; right; split... intros v H'.
        apply (H v); right...
    + apply IH2... inA; tauto.
    + apply IH1; inA. destruct H as [[[|]|[H [E|E]]]|]; auto;
      left; right; split; auto; intros v H'; apply (H v); inA.
Qed.

Theorem linear_union_spec1 x y m m2 `{Ok m, Ok m2} :
MapsTo x y (linear_union m m2) → MapsTo x y m ∨ MapsTo x y m2.
Proof with auto.
  unfold linear_union. rewrite treeify_spec.
  intro H. apply union_list_spec1 in H;
  (try rewrite rev_elements_rev, rev_involutive;auto).
  inA. destruct H as [[H|H]|[]]; rewrite
  rev_elements_rev in H; inA;
  apply elements_spec1' in H...
Qed.


Theorem linear_union_spec2 x y m m2 `{Ok m, Ok m2} :
MapsTo x y m ∨ ¬In x m ∧ MapsTo x y m2 →
MapsTo x y (linear_union m m2).
Proof with auto.
  unfold linear_union. rewrite treeify_spec.
  intro H. apply union_list_spec2; (try rewrite
  rev_elements_rev, rev_involutive;auto).
  destruct H as [|[H H']]; left.
  - left. rewrite rev_elements_rev,
    InA_rev, elements_spec1'...
  - right; split; [|rewrite
    rev_elements_rev, InA_rev,
    elements_spec1']...
    do 2 intro. apply H; exists v.
    rewrite rev_elements_rev, InA_rev,
    elements_spec1' in H0...
Qed.



Theorem union_spec1 x y m m2 `{Ok m, Ok m2} :
MapsTo x y (union m m2) → MapsTo x y m ∨ MapsTo x y m2.
Proof.
  unfold union.
  - apply linear_union_spec1; auto.
Qed.

Theorem union_spec2 x y m m2 `{Ok m, Ok m2} :
MapsTo x y m ∨ ¬In x m ∧ MapsTo x y m2 → MapsTo x y (union m m2).
Proof with auto.
  unfold union.
  - apply linear_union_spec2; auto.
Qed.

(** ** end union correctness*)


Record INV l1 l2 acc : Prop := {
 l1_sorted : sort kvplt (rev l1);
 l2_sorted : sort kvplt (rev l2);
 acc_sorted : sort kvplt acc;
 l1_lt_acc x y : InA pkeq x l1 → InA pkeq y acc → kvplt x y;
 l2_lt_acc x y : InA pkeq x l2 → InA pkeq y acc → kvplt x y}.
Local Hint Resolve l1_sorted l2_sorted acc_sorted.

Lemma Sorted_kvplt_key x y z acc :
Sorted kvplt ((x, y) :: acc) → Sorted kvplt ((x, z) :: acc).
Proof with auto.
  intro H; clear_inversion H.
  right... clear H2.
  induction acc; [|inversion H3]; auto.
Qed.

Lemma INV_key x y z l1 l2 acc :
INV l1 l2 ((x,y) :: acc) →INV l1 l2 ((x,z) :: acc).
Proof with auto.
  destruct 1. split...
  - apply Sorted_kvplt_key with y...
  - intros. apply l1_lt_acc0...
    clear_inversion H0...
  - intros. apply l2_lt_acc0...
    clear_inversion H0...
Qed.

Lemma INV_init s1 s2 `(Ok s1, Ok s2) :
 INV (rev_elements s1) (rev_elements s2) nil.
Proof.
  rewrite !rev_elements_rev.
  split; rewrite ?rev_involutive; auto; intros; now inA.
Qed.

Lemma INV_sym l1 l2 acc : INV l1 l2 acc → INV l2 l1 acc.
Proof. destruct 1; now split. Qed.

Lemma INV_drop x1 l1 l2 acc :
  INV (x1 :: l1) l2 acc → INV l1 l2 acc.
Proof.
 intros (l1s,l2s,accs,l1a,l2a). simpl in *.
 destruct (sorted_app_inv _ _ l1s) as (U & V & W); auto.
 split; auto.
Qed.

Lemma INV_eq x1 x2 l1 l2 acc :
  INV (x1 :: l1) (x2 :: l2) acc → pkeq x1 x2 →
  INV l1 l2 (x1 :: acc).
Proof with auto.
 intros (U,V,W,X,Y) EQ. simpl in *.
 destruct (sorted_app_inv' _ _ U) as (U1 & U2 & U3)...
 destruct (sorted_app_inv' _ _ V) as (V1 & V2 & V3)...
 split...
 - constructor; auto. apply InA_InfA with pkeq; auto_tc.
 - intros x y; inA; intros Hx [Hy|Hy].
   + apply U3; inA.
   + apply X; inA.
 - intros x y; inA; intros Hx [Hy|Hy].
   + destruct x, y; red; simpl in *.
     red in Hy, EQ. simpl in Hy. rewrite Hy, EQ.
     assert (kvplt (t,v) x2) by (apply V3; inA).
     red in H; simpl in H...
   + apply Y; inA.
Qed.

Lemma INV_lt x1 x2 l1 l2 acc :
  INV (x1 :: l1) (x2 :: l2) acc → kvplt x1 x2 →
  INV (x1 :: l1) l2 (x2 :: acc).
Proof with auto.
 intros (U,V,W,X,Y) EQ. simpl in *.
 destruct (sorted_app_inv' _ _ U) as (U1 & U2 & U3)...
 destruct (sorted_app_inv' _ _ V) as (V1 & V2 & V3)...
 split...
 - constructor; auto. apply InA_InfA with pkeq; auto_tc.
 - intros x y; inA; intros Hx [Hy|Hy].
   + assert (kvplt x x2). destruct Hx;
     [ red in H, Hy, EQ; simpl in *; order|].
     destruct (@Kvplt_strord val). transitivity x1...
     apply U3; inA. { red. red in H.
     red in Hy. rewrite Hy... }
   + apply X; inA.
 - intros x y; inA; intros Hx [Hy|Hy].
   + assert (kvplt x x2) by (apply V3; inA).
     { red. red in H. red in Hy. rewrite Hy... }
   + apply Y; inA.
Qed.

Lemma INV_rev l1 l2 acc :
 INV l1 l2 acc → Sorted kvplt (rev_append l1 acc).
Proof.
 intros. rewrite rev_append_rev.
 apply SortA_app with pkeq; eauto with *.
 intros x y. inA. eapply l1_lt_acc; eauto.
Qed.



Local Instance mem_proper' m `(Ok m) :
Proper (keq ==> eq ==> eq) (λ k (_:val), mem k m).
Proof.
  intros x y EQ _ _ _. apply Bool.eq_iff_eq_true;
  rewrite !mem_spec; auto. now split;
  destruct 1 as [v H]; exists v;
  [rewrite EQ in H | rewrite EQ].
Qed.

(** ** diff well-formedness *)
Instance fold_remove_ok (m1 m2:mv) `(@Ok m2) :
 Ok (foldl (λ k _, remove k) m1 m2).
Proof.
 rewrite foldl_spec', <- fold_left_rev_right.
 induction (rev (elements m1)); simpl;
 [|unfold flip, prod_curry, compose;destruct a];
 auto_tc.
Qed.

Lemma diff_list_ok l1 l2 acc :
 INV l1 l2 acc -> sort kvplt (diff_list l1 l2 acc).
Proof.
 revert l2 acc. induction l1 as [|(x,y) l1 IH1];
 [intro l2 | induction l2 as [|(a,b) l2 IH2]];
 intros acc inv.
 - eauto.
 - unfold diff_list. eapply INV_rev; eauto.
 - simpl. case K.compare_spec; intro C.
   * apply IH1. eapply INV_drop, INV_sym, INV_drop, INV_sym; eauto.
   * apply (IH2 acc). eapply INV_sym, INV_drop, INV_sym; eauto.
   * apply IH1. eapply INV_sym, INV_lt; eauto. now apply INV_sym.
Qed.

Instance linear_diff_ok m1 m2 `(Ok m1, Ok m2) :
 Ok (linear_diff m1 m2).
Proof.
  now apply treeify_ok, diff_list_ok, INV_init.
Qed.

Instance diff_ok m1 m2 `(Ok m1, Ok m2) : Ok (diff m1 m2).
Proof.
 unfold diff. destruct (@compare_bheight); auto_tc.
Qed.



Lemma union_list_ok l1 l2 acc :
 INV l1 l2 acc -> sort kvplt (union_list l1 l2 acc).
Proof.
 revert l2 acc. induction l1 as [|(x,y) l1 IH1];
 [intro l2 | induction l2 as [|(a,b) l2 IH2]];
 intros acc inv.
 - eapply INV_rev; eapply INV_sym; eauto.
 - eapply INV_rev; eauto.
 - simpl. case K.compare_spec; intro C.
   * apply IH1. apply INV_eq in inv; auto.
   * apply (IH2 ((a,b)::acc)). eapply INV_lt; eauto.
   * apply IH1. eapply INV_sym, INV_lt; eauto. now apply INV_sym.
Qed.

Instance linear_union_ok m1 m2 `(Ok m1, Ok m2) :
 Ok (linear_union m1 m2).
Proof.
  now apply treeify_ok, union_list_ok, INV_init.
Qed.

Instance union_ok m m2 `(Ok m, Ok m2) : Ok (union m m2).
Proof.
 unfold union. auto_tc.
Qed.



Lemma inter_list_ok (sl:key->val->val->val) l1 l2 acc :
 INV l1 l2 acc -> sort kvplt (inter_list sl l1 l2 acc).
Proof with auto.
 revert l2 acc. induction l1 as [|(x,y) l1 IH1];
 [intro l2 | induction l2 as [|(a,b) l2 IH2]];
 intros acc inv.
 - eauto.
 - eauto.
 - unfold inter_list. case K.compare_spec; intro C.
   * apply IH1. apply INV_eq in inv... apply INV_key with y...
   * apply IH2. eapply INV_sym, INV_drop, INV_sym; eauto.
   * apply IH1. eapply INV_drop; eauto.
Qed.


Instance linear_inter_ok sl m m2 `(Ok m, Ok m2) :
Ok (linear_inter sl m m2).
Proof.
  now apply treeify_ok, inter_list_ok, INV_init.
Qed.

Instance inter_ok sl m m2 `(Ok m, Ok m2) : Ok (inter sl m m2).
Proof.
 unfold inter. auto_tc.
Qed.

  End Vals.

End MakeRaw.



Module Make (K:OrderedType) <: Maps K.


Module Raw <: MMapInterface.RawMaps K.
Include (MakeRaw K).
End Raw.
Include MMapInterface.Raw2Maps K Raw.
End Make.

(*

Require Import OrdersEx.
Module test <: MMapInterface.Maps Nat_as_OT := Make Nat_as_OT.
Export test.

Definition en := @empty nat.

Fixpoint addr n acc :=
match n with
| O => acc
| S x => addr x (add n n acc)
end.
Definition t := Eval compute in addr 10 en.

Eval compute in
 filter (fun x y => even x)
(add 10 true (singleton 5 true)).
*)