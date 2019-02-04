(* A finite partial maps interface and implmentation in Coq.
   Largely copied from the Coq Std Lib, Msets
   - C.E. Sally, Aquinas Hobor *)

Require Import Utf8.
Require Export Bool Orders NArith SetoidList OrdersFacts.

Module Type Kvp (K : OrderedType).

 Section Vals.
 Variable val:Type.
 Notation kvp := (prod K.t val).
 Notation keq := K.eq.
 Notation klt := K.lt.

  Definition Kvpeq : relation kvp := λ a b,
    keq (fst a) (fst b) ∧ (snd a) = (snd b).

  Definition Kvplt : relation kvp := λ a b,
    klt (fst a) (fst b).

  Definition Pkeq : relation kvp :=  λ a b,
    keq  (fst a) (fst b).

 End Vals.
End Kvp. 

(*******		     The functions on maps			*******)
Module Type Funs (K : OrderedType). (* The functions on maps *)
  Notation key := K.t.
  Notation klt := K.lt.
  Notation keq := K.eq.

  Parameter map_of : ∀ x : Type, Type. (* abstract type of maps *)

(* "binding" and "key-value pair" are used interchangably and have the obvious
   meaning. "key-value pair" just refers to the key and it's associated
   value, i.e. an abstract pair. It generally does not refer to Coq pairs,
   i.e. not of type [prod] *)

  Section Vals.
   Context {val : Type}.
   Notation mv := (map_of val).
   Notation kvp := (prod key val).


(*******			  Constructors				*******)

  Parameter empty : mv. (*gen*)
  (* the empty map *)

  Parameter singleton : key → val → mv.
  (* [singleton x y] creates a map with a single binding [x-y] *)

  Parameter add : key → val → mv → mv.
  (* [add x y m] adds the binding [x-y] to the map [m]. If [x] was already
     present, [y] shadows (replaces) the previously bound value *)

  Parameter update : key → val → mv → mv. (*gen*)
  (* If [x] is in [m], [update x y m] shadows the value previously bound to
     [x] with [y]; if [x] is not in [m], [m] itself is returned *)

  Parameter remove : key → mv → mv.
  (* [remove x m] deletes a binding of [x] (and the value that was bound to it)
     from [m]; returns [m] if [x] was not present. *)

  Parameter fromList : list kvp → mv.
  (* [fromList l] constructs a map from a list of key-value pairs. If the list
     has repeat keys, the binding later in the list is added to the map. *)



(*******			 Tests/Queries				*******)

  Parameter is_empty : mv → bool. (*gen*)
  (* returns true if its argument is empty and false otherwise *)

  Parameter mem : key → mv → bool. (*gen*)
  (* [mem x m] returns true if some value is bound to [x] in [m] *)

  Parameter cardinal : mv → nat. (*gen*)
  (* returns the number of bindings in the map *)

  Parameter find : key → mv → option val. (*gen*)
  (* [find x m] returns "Some" of the value bound to [x] if [x] is in [m] and
     "None" otherwise *)

  Context {val' val'' : Type}.
  Notation mv' := (map_of val').		Notation mv'' := (map_of val'').

  Parameter subset : mv → mv' → bool. (*gen*)
  (* [subset m m'] returns true if all the keys in [m] are in [m'] *)

  Parameter equal : (val → val' → bool) → mv → mv' → bool. (*gen*)
  (* [equal cmp m' m2] returns true if [m'] and [m2] have 1) the same keys wrt
     K.eq and 2) the same values modulo some comparison function [cmp] *)

  Parameter compare : mv → mv' → comparison. (*gen*)
  (* Total ordering between the domain (set of keys) of maps. If thought of as
     a decision procedure for equality (same keys), it is sound & complete;
     Yes := Eq, No := Lt, Gt. For subset, it is only complete (only "no" 
     answers can be trusted). *)

  Parameter for_all : (key → val → bool) → mv → bool. (*gen*)
  (* [for_all P m] returns true if every binding the in the map satisfies [P] *)

  Parameter exists_ : (key → val → bool) → mv → bool. (*gen*)
  (* [exists_ P m] returns true if there exists a binding in the map satisfying
     [P] *)



(*******			 Map operators  			*******)

  Parameter union : mv → mv → mv.
  (* [union m m2] returns a map containing bindings where the keys are found
     in either [m] or [m2]. When both [m] & [m2] have a key in common, union
     is left-favouring: it returns the value from [m].*)

  Parameter inter : (key→val→val→val) → mv → mv → mv.
  (* [inter sl m m2] maps [x] to [sl x y z] iff [(x,y)] is in [m] and
     [(x,z)] is in [m2]. *)

  Parameter diff : mv → mv → mv.
  (* [diff m' m2] returns a map containing bindings where the keys are found in
     [m'] but not [m2]. Analogous to set difference, not symmetric difference *)

(* Dear Pierre, for union and intersection, we tried to generalize the types
   so that you could union a map of nats and a map of bools for exampl, but
   this proved to be extremely painful, in terms of the specs. We were also
   not exactly sure of the specs for them. In the interests of time, we
   prototyped these above functions first. We are not terribly happy with
   them; any comments/suggestions for improvements would be appreciated.

   The functions we would have liked to have are below. Are they too much?

  Parameter inter {X:Type} : (key → val → val' → X) → mv → mv' → map_of X.
  (* [inter comb m m'] returns a map containing keys that are in both [m] & [m'].
     A user supplied function, taking the key and both values determines the
     new value to be bound in the result *)

  Parameter union : (key→val→X)→(key→val'→X)→(key→val→val'→X)→mv→mv'→map_of X.
  (* [union left right pair m m'], returns a map containing bindings where the
     keys are found in either [m] or [m2]. If the key [x] is bound to [y] in
     only one of the maps, then [x] is bound to [left x y] in the result if
     [x] is in [m]. Alternatively, [x] is bound to [right x y] in the result,
     if [x] was in [m']. When [(x,y)] & [(x,z)] are in [m] & [m'] respectively,
     the value bound in the result is [sl x y z] *)
*)

(*******			 Map functions				*******)

  Parameter foldl : ∀ {A : Type}, (key → val → A → A) → mv → A → A. (*gen*)
  (* [fold f m acc] computes (f xN yN ... (f x2 y2 (f x1 y1 acc))...), where
     x1 y1 .. xN yN are the bindings of [m]. Takes the bindings in increasing
     order *)

  Parameter foldr : ∀ {A : Type}, (key → val → A → A) → mv → A → A. (*gen*)
  (* [fold f m acc] computes (f x1 y1 (f x2 y2 ... (f xN yN acc))...), where
     x1 y1 .. xN yN are the bindings of [m]. Takes the bindings in decreasing
     order *)

  Parameter filter : (key → val → bool) → mv → mv.
  (* [filter P m] is a map with all the bindings in [m] that satisfy [P]. *)

  Parameter partition : (key → val → bool) → mv → mv * mv.
  (* [partition P m] returns a pair of maps [(m', m2)], where [m'] is a map
     containing all key-value pairs that satisfy P, and [m2], the map containing
     the bindings that do not *)

  Parameter map : (val → val') → mv → mv'. (*gen*)
  (* [map f m] returns a map with same domain as [m], where the value [a] in
     each binding of [m] has been replaced by [f a] *)

  Parameter mapi : (key → val → val') → mv → mv'. (*gen*)
  (* Same as [map], but the function receives both key and value as arguments
     for each binding of the map *)
(*
  Parameter map2 : (option val → option val' → option val'') → mv → mv' → mv''.
  (* [map2 f m m'] creates a new map whose bindings belong to the ones of
     either m or m'. The presence and value for a key [k] is determined by
     [f e1 e2] where e1 and e2 are the (optional) bindings of k in m and m2. *)
*)


(*******		       Element selectors			*******)

  Parameter elements : mv → list kvp. (*gen*)
  (* Returns a list of bindings of the map sorted by keys. *)

  Parameter kelements : mv → list key. (*gen*)
  (* Returns a sorted list of keys of the map *)

  Parameter choose : mv → option kvp. (*gen*)
  (* Return one binding of the map, as [Some] of a pair of key and value. 
     Returns None if the map is empty. Which element is chosen is unspecified.
     [Equal] sets could return different elements. *)

  Parameter min_elt : mv → option kvp. (*gen*)
  (* Returns the binding with the smallest key (with respect to the X.compare
     ordering), or None if the set is empty. *)

  Parameter max_elt : mv → option kvp. (*gen*)
  (* Returns the binding with the largest key (with respect to the X.compare
     ordering), or None if the set is empty. *)


  End Vals.

End Funs.



(*******		       The specifications			*******)
Module Type Maps (K:OrderedType).
  Include Funs K.  (* First, we get all the functions *)
  Include Kvp K.

(*******		  Some Predicate & Definitions			*******)
Section Preds1.
  Context {val : Type}.
  Notation mv := (map_of val).

  Parameter MapsTo : key → val → mv → Prop.
  (* [MapsTo k v m] is true when [v] is bound to [k] in [m]. i.e. the key-value
     pair [k-v] is in [m] *)
  Declare Instance Mt_compat : Proper (keq==>Logic.eq==>Logic.eq==>iff) MapsTo.

  Definition In k m := ∃v, MapsTo k v m.

End Preds1.
Section Preds2.
  Context {val val' : Type}.
  Notation mv := (map_of val).
  Notation mv' := (map_of val').

  Definition Empty       (m:mv)     := ∀ k v, ¬ MapsTo k v m.
  Definition Equal       (m1 m2:mv) := ∀ k v, MapsTo k v m1 ↔ MapsTo k v m2.
  Definition Restriction (m1 m2:mv) := ∀ k v, MapsTo k v m1 → MapsTo k v m2.
  Definition SameKeys    (m1 m2:mv) := ∀ k  , In k m1 ↔ In k m2.
  Definition Subset   (m:mv)(m':mv'):= ∀ k  , In k m → In k m'.
  Definition For_all (P:_→_→Prop) (m:mv) := ∀ k v, MapsTo k v m → P k v.
  Definition Exists  (P:_→_→Prop) (m:mv) := ∃ k v, MapsTo k v m ∧ P k v.
  Definition Equivb cmp (m:mv) (m':mv')  := (∀ x, In x m ↔ In x m') ∧
  (∀ x (v:val) (v':val'), MapsTo x v m → MapsTo x v' m' → cmp v v' = true).

  Parameter mkeq : relation (list key).
  Declare Instance mkeq_equiv : Equivalence mkeq.
  Parameter mklt : relation (list key).
  Declare Instance mklt_strorder : StrictOrder mklt.

End Preds2.




(*******			     Specs				*******)
Section Specs.
  Context {val val': Type}.
  Notation mv  := (map_of val).
  Notation mv' := (map_of val').
  Notation kvp := (prod key val).
  Notation kvpeq := (Kvpeq val).
  Notation kvplt := (Kvplt val).
  Notation pkeq := (Pkeq val).

  Notation "s [=] t"   := (Equal s t)       (at level 70, no associativity).
  Notation "s [|<=] t" := (Restriction s t) (at level 70, no associativity).
  Notation "s [<=] t"  := (Subset s t)      (at level 70, no associativity).

  Variable x a : key.
  Variable y b : val.
  Variable m m1 m2 : mv.


    (** Specification of [MapsTo] *)
      Parameter MapsTo_spec1 : keq a x → MapsTo a y m → MapsTo x y m.
      Parameter MapsTo_spec2 : MapsTo x b m → MapsTo x y m → b = y.

    (** Specification of [empty] *)
      Parameter empty_spec : Empty (@empty val).

    (** Specification of [add] *)
      Parameter add_spec1 : MapsTo x y (add x y m).
      Parameter add_spec2 : ¬keq a x → (MapsTo a b (add x y m) ↔ MapsTo a b m).

    (** Specification of [singleton] *)
      Parameter singleton_spec : MapsTo a b (singleton x y) ↔ kvpeq (a,b) (x,y).

    (** Specification of [update] *)
      Parameter update_spec1 : In x m → MapsTo x y (update x y m).
      Parameter update_spec2 : ¬In x m → (update x y m) [=] m.
      Parameter update_spec3: ¬keq a x → (MapsTo a b (update x y m) ↔ MapsTo a b m).

    (** Specification of [remove] *)
      Parameter remove_spec1 : keq a x → ¬In a (remove x m).
      Parameter remove_spec2 : ¬keq a x → MapsTo a b m →
                               MapsTo a b (remove x m).
      Parameter remove_spec3 : MapsTo a b (remove x m) → MapsTo a b m.

    (** Specification of [fromList] *)
    Variable lst : list kvp.
(*    is this spec needed?
      Parameter fromList_spec1 : In x (fromList lst) ↔ ∃y, InA pkeq (x,y) lst.
 *)
      Parameter fromList_spec2 : MapsTo x y (fromList lst) →
                                 InA kvpeq (x,y) lst.
      Parameter fromList_spec3 : NoDupA pkeq lst → InA kvpeq (x,y) lst →
                                 MapsTo x y (fromList lst).

    (** Specification of [is_empty] *)
      Parameter is_empty_spec : is_empty m = true ↔ Empty m.

    (** Specification of [mem] *)
      Parameter mem_spec : mem x m = true ↔ In x m.

    (** Specification of [cardinal] *)
      Parameter cardinal_spec : cardinal m = length (elements m).

    (** Specification of [find] *)
      Parameter find_spec : find x m = Some y ↔ MapsTo x y m.


  Variable m' : mv'.

    (** Specification of [subset] *)
      Parameter subset_spec : subset m m' = true ↔ m [<=] m'.
(*
    (** Specification of [equal] *)
    Variable cmp : val → val' → bool.
      Parameter equiv_spec : equiv cmp m m' = true ↔ Equivb cmp m m'.
*)
    (** Specification of [compare] *)
      Parameter compare_spec : CompSpec mkeq mklt
                              (kelements m1) (kelements m') (compare m1 m').


  Variable P : key → val → bool.
    (** Specification of [for_all] *)
    Notation compatb := (Proper (keq==>Logic.eq==>Logic.eq)) (only parsing).
    Notation P' := (λ x y, P x y = true).
      Parameter for_all_spec : compatb P → (for_all P m = true ↔ For_all P' m).

    (** Specification of [exists_] *)
      Parameter exists__spec : compatb P → (exists_ P m = true ↔ Exists  P' m).

  Variable sl : key → val → val → val.
    Notation compatbb := (Proper (keq==>Logic.eq==>Logic.eq==>Logic.eq)).

    (** Specification of [union] *)
      Parameter union_spec1 : MapsTo x y (union m m2) →
                              MapsTo x y m ∨ MapsTo x y m2.
      Parameter union_spec2 : MapsTo x y m ∨ (¬In x m ∧ MapsTo x y m2) →
                              MapsTo x y (union m m2).

    (** Specification of [inter] *)
      Parameter inter_spec : compatbb sl →
                           ((∃ y b, MapsTo x (sl x y b) (inter sl m m2)) ↔
                             In x m ∧ In x m2).
      Parameter inter_spec1 : MapsTo x (sl x y b) (inter sl m m2) →
                              In x m ∧ In x m2.
      Parameter inter_spec2 : compatbb sl →
                              MapsTo x y m ∧ MapsTo x b m2 →
                              MapsTo x (sl x y b) (inter sl m m2).

    (** Specification of [diff] *)
      Parameter diff_spec : MapsTo x y (diff m m2) ↔
                            MapsTo x y m ∧ ¬In x m2.



    (** Specification of [foldl] *)
      Notation func := (compose flip prod_curry).
      (*"flipped uncurry", not "function"*)
      Parameter foldl_spec : ∀ {X : Type} f (sd : X),
                foldl f m sd = fold_left (func f) (elements m) sd.


    (** Specification of [foldr] *)
      Notation unc := prod_curry.
      Parameter foldr_spec : ∀ {X : Type} f (sd : X),
                foldr f m sd = fold_right (unc f) sd (elements m).


    (** Specification of [filter] *)
      Parameter filter_spec : compatb P →
               (MapsTo x y (filter P m) ↔ MapsTo x y m ∧ P x y = true).


    (** Specification of [partition] *)
      Notation nP := (λ x y, negb (P x y)).
      Parameter partition_spec : compatb P → let (x,y) := partition P m in
                x [=] filter P m ∧ y [=] filter nP m.
      Parameter partition_spec1 : compatb P →
                fst (partition P m) [=] filter P m.
      Parameter partition_spec2 : compatb P →
                snd (partition P m) [=] filter nP m.


  Variable f  :       val → val'.
  Variable f' : key → val → val'.
    (** Specification of [map] *)
      Parameter map_spec1 : MapsTo x y m → MapsTo x (f y) (map f m).
      Parameter map_spec2 : In x (map f m) → In x m.

    (** Specification of [mapi] *)
      Parameter mapi_spec1 : compatb f' →
                             MapsTo x y m → MapsTo x (f' x y) (mapi f' m).
      Parameter mapi_spec2 : In x (mapi f' m) → In x m.

    (** Specification of [elements] *)
      Parameter elements_spec1 : InA kvpeq (x,y) (elements m) ↔ MapsTo x y m.
      Parameter elements_spec2 : Sorted kvplt (elements m).
      Parameter elements_spec3 : NoDupA kvpeq (elements m).

    (** Specification of [kelements] *)
      Parameter kelements_spec1 : InA keq x  (kelements m) ↔ In x m.
      Parameter kelements_spec2 : Sorted klt (kelements m).
      Parameter kelements_spec3 : NoDupA keq (kelements m).

    (** Specification of [choose] *)
    Variable kv1 kv2 : kvp.
      Parameter choose_spec1 : choose m = Some (x,y) → MapsTo x y m.
      Parameter choose_spec2 : choose m = None → Empty m.

(*    should we make [choose] select some kind of principal element, or let
      it take a random element?
      Parameter choose_spec3 : choose m = Some kv1 → choose m2 = Some kv2 →
                               m [=] m2 → kvpeq kv1 kv2.
*)
    (** Specification of [min_elt] *)
      Parameter min_elt_spec1 : min_elt m = Some (x,y) → MapsTo x y m.
      Parameter min_elt_spec2 : min_elt m = Some (x,y) →
                                   ∀ a, In a m → ¬klt a x.
      Parameter min_elt_spec3 : min_elt m = None → Empty m.

    (** Specification of [max_elt] *)
      Parameter max_elt_spec1 : max_elt m = Some (x,y) → MapsTo x y m.
      Parameter max_elt_spec2 : max_elt m = Some (x,y) →
                                   ∀ a, In a m → ¬klt x a.
      Parameter max_elt_spec3 : max_elt m = None → Empty m.

  End Specs.

End Maps.



















































(*   A specification for maps well formed in the underlying implementation    *)

Module Type RawMaps (K:OrderedType). (* this is the analog of Maps *)
  Include Funs K. (* First, we get all the functions *) 
  Include Kvp K.

(*******		  Some Predicate & Definitions			*******)
Section Preds1.
  Context {val : Type}.
  Notation mv := (map_of val).

  Parameter MapsTo : key → val → mv → Prop.
  (* [MapsTo k v m] is true when [v] is bound to [k] in [m]. i.e. the key-value
     pair [k-v] is in [m] *)
  Declare Instance Mt_compat : Proper (keq==>Logic.eq==>Logic.eq==>iff) MapsTo.

  Definition In k m := ∃v, MapsTo k v m.

End Preds1.
Section Preds2.
  Context {val val' : Type}.
  Notation mv := (map_of val).
  Notation mv' := (map_of val').

  Definition Empty       (m:mv)     := ∀ k v, ¬ MapsTo k v m.
  Definition Equal       (m1 m2:mv) := ∀ k v, MapsTo k v m1 ↔ MapsTo k v m2.
  Definition Restriction (m1 m2:mv) := ∀ k v, MapsTo k v m1 → MapsTo k v m2.
  Definition SameKeys    (m1 m2:mv) := ∀ k  , In k m1 ↔ In k m2.
  Definition Subset   (m:mv)(m':mv'):= ∀ k  , In k m → In k m'.
  Definition For_all (P:_→_→Prop) (m:mv) := ∀ k v, MapsTo k v m → P k v.
  Definition Exists  (P:_→_→Prop) (m:mv) := ∃ k v, MapsTo k v m ∧ P k v.
  Definition Equivb cmp (m:mv) (m':mv')  := (∀x, In x m ↔ In x m') ∧
  (∀x (v:val) (v':val'), MapsTo x v m → MapsTo x v' m' → cmp v v' = true).


  Parameter IsOk : mv → Prop.
  Class Ok (m:mv) : Prop := ok : IsOk m.

  Parameter isok : mv → bool.
  Declare Instance isok_Ok s `(isok s = true) : Ok s | 10.

  Parameter mkeq : relation (list key).
  Declare Instance mkeq_equiv : Equivalence mkeq.
  Parameter mklt : relation (list key).
  Declare Instance mklt_strorder : StrictOrder mklt.


End Preds2.

  Declare Instance empty_ok v : Ok (@empty v).
  Declare Instance singleton_ok v x y : Ok (@singleton v x y).
  Declare Instance add_ok v x y m `{@Ok v m} : Ok (add x y m).
  Declare Instance update_ok v x y m `{@Ok v m}: Ok (update x y m).
  Declare Instance remove_ok v x m `{@Ok v m} : Ok (remove x m).
  Declare Instance fromList_ok val (l:list (key*val)) : Ok (fromList l).
  Declare Instance union_ok v m m2 `{@Ok v m, @Ok v m2} : Ok (union m m2).
  Declare Instance inter_ok v sl m m2 `{@Ok v m, @Ok v m2} : Ok (inter sl m m2).
  Declare Instance diff_ok v m m2 `{@Ok v m, @Ok v m2}: Ok (diff m m2).
  Declare Instance map_ok v v' (f:v→v') m `{@Ok v m}: Ok (map f m).
  Declare Instance mapi_ok v v' (f:key→v→v') m `{@Ok v m}: Ok (mapi f m).
  Declare Instance filter_ok v (P:key→v→bool) m `{@Ok v m} : Ok (filter P m).
  Declare Instance partition_ok1 v P m `{@Ok v m} : Ok (fst (partition P m)).
  Declare Instance partition_ok2 v P m `{@Ok v m} : Ok (snd (partition P m)).



(*******			     Specs				*******)
Section Specs.
  Context {val val' : Type}.
  Notation mv    := (map_of val).
  Notation mv'   := (map_of val').
  Notation kvp   := (prod key val).
  Notation kvpeq := (Kvpeq val).
  Notation kvplt := (Kvplt val).
  Notation Ok    := (@Ok val).
  Notation Ok'   := RawMaps.Ok.

  Notation "s [=] t"   := (Equal s t)       (at level 70, no associativity).
  Notation "s [|<=] t" := (Restriction s t) (at level 70, no associativity).
  Notation "s [<=] t"  := (Subset s t)      (at level 70, no associativity).

  Variable a x  : key.
  Variable b y  : val.
  Variable m m2 : mv.
  Notation compatb := (Proper (keq==>Logic.eq==>Logic.eq)) (only parsing).


  Parameter MapsTo_spec1 : ∀ `{Ok m}, keq a x → MapsTo a y m → MapsTo x y m.
  Parameter MapsTo_spec2 : ∀ `{Ok m}, MapsTo x b m → MapsTo x y m → b = y.

  Parameter empty_spec : Empty (@empty val).

  Parameter singleton_spec : MapsTo a b (singleton x y) ↔ kvpeq (a,b) (x,y).

  Parameter add_spec1 : ∀ `{Ok m}, MapsTo x y (add x y m).
  Parameter add_spec2 : ∀ `{Ok m}, ¬keq a x →
                        (MapsTo a b (add x y m) ↔ MapsTo a b m).

  Parameter update_spec1 : ∀ `{Ok m},  In x m → MapsTo x y (update x y m).
  Parameter update_spec2 : ∀ `{Ok m}, ¬In x m → (update x y m) [=] m.
  Parameter update_spec3 : ∀ `{Ok m}, ¬keq a x →
                        (MapsTo a b (update x y m) ↔ MapsTo a b m).

  Parameter remove_spec1 : ∀ `{Ok m}, keq a x → ¬In a (remove x m).
  Parameter remove_spec2 : ∀ `{Ok m}, ¬keq a x → MapsTo a b m →
                           MapsTo a b (remove x m).
  Parameter remove_spec3 : ∀ `{Ok m}, MapsTo a b (remove x m) → MapsTo a b m.
  
  Variable lst : list kvp.
  Notation pkeq := (fun x y => keq (fst x) (fst y)).
(*
  Parameter fromList_spec1 : In x (fromList lst) ↔ ∃ y, InA pkeq (x,y) lst.
 *)
  Parameter fromList_spec2 : MapsTo x y (fromList lst) → InA kvpeq (x,y) lst.
  Parameter fromList_spec3 : NoDupA pkeq lst → InA kvpeq (x,y) lst →
                             MapsTo x y (fromList lst).

  Parameter is_empty_spec : ∀ `{Ok m}, is_empty m = true ↔ Empty m.

  Parameter mem_spec : ∀ `{Ok m}, mem x m = true ↔ In x m.

  Parameter cardinal_spec : ∀ `{Ok m}, cardinal m = length (elements m).

  Parameter find_spec : ∀ `{Ok m}, find x m = Some y ↔ MapsTo x y m.


  Variable m'  : mv'.
  Variable cmp : val → val' → bool.
  Parameter subset_spec : ∀ `{Ok m, Ok' m'}, subset m m' = true ↔ m[<=]m'.
(*
  Parameter equiv_spec : equiv cmp m m' = true ↔ Equivb cmp m m'.
*)
  Parameter compare_spec : ∀ `{Ok m, Ok' m'},
                           CompSpec mkeq mklt
                          (kelements m) (kelements m') (compare m m').


  Variable P  : key → val → bool.
  Notation P' := (λ x y, P x y = true).
  Notation nP := (λ x y, negb (P x y)).
  Parameter for_all_spec : ∀ `{Ok m}, compatb P →
                          (for_all P m = true ↔ For_all P' m).

  Parameter exists__spec : ∀ `{Ok m}, compatb P →
                          (exists_ P m = true ↔ Exists  P' m).

  Variable sl : key → val → val → val.
  Notation compatbb := (Proper (keq==>Logic.eq==>Logic.eq==>Logic.eq)).
  Parameter union_spec1 : ∀ `{Ok m, Ok m2}, MapsTo x y (union m m2) →
                          MapsTo x y m ∨ MapsTo x y m2.
  Parameter union_spec2 : ∀ `{Ok m, Ok m2},
                          MapsTo x y m ∨ (¬In x m ∧ MapsTo x y m2) →
                          MapsTo x y (union m m2).


  Parameter inter_spec : ∀ `{Ok m, Ok m2}, compatbb sl →
                       ((∃ y b, MapsTo x (sl x y b) (inter sl m m2)) ↔
                         In x m ∧ In x m2).
  Parameter inter_spec1 : ∀ `{Ok m, Ok m2},
                          MapsTo x (sl x y b) (inter sl m m2) →
                          In x m ∧ In x m2.
  Parameter inter_spec2 : ∀ `{Ok m, Ok m2}, compatbb sl →
                          MapsTo x y m ∧ MapsTo x b m2 →
                          MapsTo x (sl x y b) (inter sl m m2).


  Parameter diff_spec : ∀ `{Ok m, Ok m2}, MapsTo x y (diff m m2) ↔
                            MapsTo x y m ∧ ¬In x m2.


  (*"flipped uncurry", not "function"*)
  Notation func := (compose flip prod_curry).
  Parameter foldl_spec : ∀ {X : Type} f (sd : X) `{Ok m},
            foldl f m sd = fold_left (func f) (elements m) sd.


  Notation unc := prod_curry.
  Parameter foldr_spec : ∀ {X : Type} f (sd : X) `{Ok m},
            foldr f m sd = fold_right (unc f) sd (elements m).


  Parameter filter_spec : ∀ `{Ok m}, compatb P → 
           (MapsTo x y (filter P m) ↔ MapsTo x y m ∧ P x y = true).

  Parameter partition_spec : let (x,y) := partition P m in compatb P →
            x [=] filter P m ∧ y [=] filter nP m.
  Parameter partition_spec1 : compatb P → fst (partition P m) [=] filter  P m.
  Parameter partition_spec2 : compatb P → snd (partition P m) [=] filter nP m.


  Variable f  :       val → val'.
  Variable f' : key → val → val'.
  Parameter map_spec1 : ∀ `{Ok m}, MapsTo x y m → MapsTo x (f y) (map f m).
  Parameter map_spec2 : ∀ `{Ok m}, In x (map f m) → In x m.

  Parameter mapi_spec1 : ∀ `{Ok m}, compatb f' →
                         MapsTo x y m → MapsTo x (f' x y) (mapi f' m).
  Parameter mapi_spec2 : ∀ `{Ok m}, In x (mapi f' m) → In x m.

  Parameter elements_spec1 : ∀ `{Ok m}, InA kvpeq (x,y) (elements m) ↔
                             MapsTo x y m.
  Parameter elements_spec2 : ∀ `{Ok m}, Sorted kvplt (elements m).
  Parameter elements_spec3 : ∀ `{Ok m}, NoDupA kvpeq (elements m).

  Parameter kelements_spec1 : ∀ `{Ok m}, InA keq x (kelements m) ↔ In x m.
  Parameter kelements_spec2 : ∀ `{Ok m}, Sorted klt (kelements m).
  Parameter kelements_spec3 : ∀ `{Ok m}, NoDupA keq (kelements m).

(*  Variable kv1 kv2 : kvp. *)
  Parameter choose_spec1 : ∀ `{Ok m}, choose m = Some (x,y) → MapsTo x y m.
  Parameter choose_spec2 : ∀ `{Ok m}, choose m = None → Empty m.
(*  Parameter choose_spec3 : ∀ `{Ok m, Ok m2}, choose m = Some kv1 →
                           choose m2 = Some kv2 → m [=] m2 → kvpeq kv1 kv2. *)

  Parameter min_elt_spec1 : ∀ `{Ok m}, min_elt m = Some (x,y) → MapsTo x y m.
  Parameter min_elt_spec2 : ∀ `{Ok m}, min_elt m = Some (x,y) →
                                ∀ a, In a m → ¬klt a x.
  Parameter min_elt_spec3 : ∀ `{Ok m}, min_elt m = None → Empty m.


  Parameter max_elt_spec1 : ∀ `{Ok m}, max_elt m = Some (x,y) → MapsTo x y m.
  Parameter max_elt_spec2 : ∀ `{Ok m}, max_elt m = Some (x,y) →
                                ∀ a, In a m → ¬klt x a.
  Parameter max_elt_spec3 : ∀ `{Ok m}, max_elt m = None → Empty m.


 End Specs.

End RawMaps.





















(***  Functor to bring well-formed specification to vanilla specification  ***)
Module Raw2Maps (K:OrderedType)(M:RawMaps K) <: Maps K.
Notation key := K.t.
Notation keq := K.eq.				Notation klt := K.lt.

  (** We avoid creating induction principles for the Record *)
  Local Unset Elimination Schemes.
  Local Unset Case Analysis Schemes.

  Record t_ (typ : Type) := Mkt {v :> M.map_of typ ; is_ok : M.Ok v}.
  Definition map_of := t_.
  Arguments Mkt {typ} v {is_ok}.
  Arguments v {typ} t.
  Hint Resolve is_ok : typeclass_instances.

Section Preds1.
  Context {val val':Type}.
  Notation wm := (map_of val). (* well formed map of val *)

  Definition MapsTo x y (m:wm) := M.MapsTo x y m.(v).
  Instance Mt_compat : Proper (K.eq==>Logic.eq==>Logic.eq==>iff) MapsTo.
  Proof with auto.
    cbv; intros. apply M.Mt_compat... rewrite H1...
  Qed.

  Definition In x (m:wm) := M.In x m.(v).

End Preds1.
Section Preds2.
  Context {val val':Type}.
  Notation wm := (map_of val). (* well formed map of val *)
  Notation w' := (map_of val').
  Notation kvp := (prod key val).

  Definition Empty       (m:wm)     := M.Empty m.
  Definition Equal       (m1 m2:wm) := M.Equal m1 m2.
  Definition Restriction (m1 m2:wm) := M.Restriction m1 m2.
  Definition SameKeys    (m1 m2:w') := M.SameKeys m1 m2.
  Definition Subset   (m:wm)(m':w') := M.Subset m m'.
  Definition For_all (P:_→_→Prop) (m:wm) := M.For_all P m.
  Definition Exists  (P:_→_→Prop) (m:wm) := M.Exists P m.
  Definition Equivb cmp (m:wm) (m':w')  := M.Equivb cmp m m'.
  Definition Kvpeq := M.Kvpeq val.
  Definition Kvplt := M.Kvplt val.
  Definition Pkeq := M.Pkeq val.

  Definition mkeq : relation (list key) := M.mkeq.
  Instance mkeq_equiv : Equivalence mkeq.
  Proof.
    generalize M.mkeq_equiv.
    unfold mkeq. firstorder.
  Qed.

  Definition mklt : relation (list key) := M.mklt.
  Instance mklt_strorder: StrictOrder mklt.
  Proof.
    generalize M.mklt_strorder.
    unfold mklt. firstorder.
  Qed.


(*
  Definition Restriction (m1 m2:wm) := ∀ k v, MapsTo k v m1 → MapsTo k v m2.
  Definition SameKeys (m:wm)(m':w'):= ∀ k  , In k m ↔ In k m'.
  Definition Subset   (m:wm)(m':w'):= ∀ k  , In k m → In k m'.
  Definition For_all (P:_→_→Prop) (m:wm) := ∀ k v, MapsTo k v m → P k v.
  Definition Exists  (P:_→_→Prop) (m:wm) := ∃ k v, MapsTo k v m ∧ P k v.
  Definition Equivb cmp (m:wm) (m':w')  := (∀x, In x m ↔ In x m') ∧
  (∀x (v:val) (v':val'), MapsTo x v m → MapsTo x v' m' → cmp v v' = true).
  Definition Kvp_eq := @M.Kvp_eq val.
  Definition Kvp_lt := @M.Kvp_lt val.
*)

  Definition empty : wm               := Mkt M.empty.
  Definition singleton x y : wm       := Mkt (M.singleton x y).
  Definition add x y m : wm           := Mkt (M.add x y m.(v)).
  Definition is_empty (m:wm)          := M.is_empty m.(v).
  Definition mem x (m:wm)             := M.mem x m.(v).
  Definition cardinal (m:wm)          := M.cardinal m.(v).
  Definition update x y m : wm        := Mkt (M.update x y m.(v)).
  Definition remove x m : wm          := Mkt (M.remove x m.(v)).
  Definition fromList l : wm          := Mkt (M.fromList l).
  Definition find x (m:wm)            := M.find x m.(v).
  Definition subset (m:wm) (m':w')    := M.subset m.(v) m'.(v).
  Definition equal cmp (m:wm) (m2:w') := M.equal cmp m.(v) m2.(v).
  Definition compare (m:wm) (m':w')   := M.compare m.(v) m'.(v).
  Definition for_all P (m:wm)         := M.for_all P m.(v).
  Definition exists_ P (m:wm)         := M.exists_ P m.(v).
  Definition union (m m2:wm)          := Mkt (M.union m.(v) m2.(v)).
  Definition inter sl (m m2:wm)       := Mkt (M.inter sl m.(v) m2.(v)).
  Definition diff (m m2:wm)           := Mkt (M.diff m.(v) m2.(v)).
  Definition foldl {A} f m sd         := @M.foldl val A f m.(v) sd.
  Definition foldr {A} f m sd         := @M.foldr val A f m.(v) sd.
  Definition filter P (m:wm)          := Mkt (M.filter P m.(v)).
  Definition partition P (m:wm)       := let x := M.partition P m.(v) in
                                        (Mkt (fst x), Mkt (snd x)).
  Definition map  (f:val→val')     m  := Mkt (M.map  f m.(v)).
  Definition mapi (f:key→val→val') m  := Mkt (M.mapi f m.(v)).
  Definition elements (m:wm)          := M.elements m.(v).
  Definition kelements (m:wm)         := M.kelements m.(v).
  Definition choose (m:wm)            := M.choose m.(v).
  Definition min_elt (m:wm)           := M.min_elt m.(v).
  Definition max_elt (m:wm)           := M.max_elt m.(v).

End Preds2.


Section Vals.
 Context {val val':Type}.
 Notation mv := (map_of val).
 Notation mv' := (map_of val').
 Notation kvp := (prod key val).

 Variable x a     : key.
 Variable y b     : val.
 Variable m m1 m2 : mv.
 Variable kv1 kv2 : kvp.
 Variable m'      : mv'.
 Variable P       : key → val → bool.
 Variable lst     : list kvp.
 Variable cmp     : val → val' → bool.
 Variable sl      : key → val → val → val.
 Variable f       :       val → val'.
 Variable f'      : key → val → val'.
 Notation "s [=] t"   := (Equal s t)       (at level 70, no associativity).
 Notation "s [|<=] t" := (Restriction s t) (at level 70, no associativity).
 Notation "s [<=] t"  := (Subset s t)      (at level 70, no associativity).
 Notation compatb := (Proper (keq==>Logic.eq==>Logic.eq)) (only parsing).
 Notation compatbb := (Proper (keq==>Logic.eq==>Logic.eq==>Logic.eq)).

Lemma MapsTo_spec1 : keq a x → MapsTo a y m → MapsTo x y m.
Proof. refine (@M.MapsTo_spec1 _ _ _ _ _ _). Qed.
Lemma MapsTo_spec2 : MapsTo x b m → MapsTo x y m → b = y.
Proof. refine (@M.MapsTo_spec2 _ _ _ _ _ _). Qed.
Lemma empty_spec : Empty (@empty val).
Proof. refine M.empty_spec. Qed.
Lemma add_spec1 : MapsTo x y (add x y m).
Proof. refine (@M.add_spec1 _ _ _ _ _). Qed.
Lemma add_spec2 : ¬keq a x → (MapsTo a b (add x y m) ↔ MapsTo a b m).
Proof. refine (@M.add_spec2 _ _ _ _ _ _ _). Qed.
Lemma singleton_spec : MapsTo a b (singleton x y) ↔ Kvpeq (a,b)(x,y).
Proof. refine (@M.singleton_spec _ _ _ _ _). Qed.
Lemma update_spec1 : In x m → MapsTo x y (update x y m).
Proof. refine (@M.update_spec1 _ _ _ _ _). Qed.
Lemma update_spec2 : ¬In x m → (update x y m) [=] m.
Proof. refine (@M.update_spec2 _ _ _ _ _). Qed.
Lemma update_spec3 : ¬keq a x → (MapsTo a b (update x y m) ↔ MapsTo a b m).
Proof. refine (@M.update_spec3 _ _ _ _ _ _ _). Qed.
Lemma remove_spec1 : keq a x → ¬In a (remove x m).
Proof. refine (@M.remove_spec1 _ _ _ _ _). Qed.
Lemma remove_spec2 : ¬keq a x → MapsTo a b m → MapsTo a b (remove x m).
Proof. refine (@M.remove_spec2 _ _ _ _ _ _). Qed.
Lemma remove_spec3 : MapsTo a b (remove x m) → MapsTo a b m.
Proof. refine (@M.remove_spec3 _ _ _ _ _ _). Qed. (*
Lemma fromList_spec1 : In x (fromList lst) ↔ ∃ y, InA pkeq (x,y) lst.
Proof. refine (@M.fromList_spec1 _ _ _). Qed. *)
Lemma fromList_spec2 : MapsTo x y (fromList lst) → InA Kvpeq (x,y) lst.
Proof. refine (@M.fromList_spec2 _ _ _ _). Qed.
Lemma fromList_spec3 : NoDupA Pkeq lst → InA Kvpeq (x,y) lst →
                       MapsTo x y (fromList lst).
Proof. refine (@M.fromList_spec3 _ _ _ _). Qed.
Lemma is_empty_spec : is_empty m = true ↔ Empty m.
Proof. refine (@M.is_empty_spec _ _ _). Qed.
Lemma mem_spec : mem x m = true ↔ In x m.
Proof. refine (@M.mem_spec _ _ _ _). Qed.
Lemma cardinal_spec : cardinal m = length (elements m).
Proof. refine (@M.cardinal_spec _ _ _). Qed.
Lemma find_spec : find x m = Some y ↔ MapsTo x y m.
Proof. refine (@M.find_spec _ _ _ _ _). Qed.
Lemma subset_spec : subset (m:mv) (m':mv') = true ↔ m [<=] m'.
Proof. refine (@M.subset_spec _ _ _ _ _ _). Qed. (*
Lemma equiv_spec : equiv cmp m m' = true ↔ Equivb cmp m m'.
Proof. refine (@M.equiv_spec _ _ _ _ _). Qed. *)
Lemma compare_spec : CompSpec mkeq mklt 
                     (kelements m) (kelements m') (compare m m').
Proof. refine (@M.compare_spec _ _ _ _ _ _). Qed.
  Notation P' := (λ x y, P x y = true).
Lemma for_all_spec : compatb P → (for_all P m = true ↔ For_all P' m).
Proof. refine (@M.for_all_spec val _ _ _). Qed.
Lemma exists__spec : compatb P → (exists_ P m = true ↔ Exists  P' m).
Proof. refine (@M.exists__spec val _ _ _). Qed.
Lemma union_spec1 : MapsTo x y (union m m2) → MapsTo x y m ∨ MapsTo x y m2.
Proof. refine (@M.union_spec1 _ _ _ _ _ _ _). Qed.
Lemma union_spec2 : MapsTo x y m ∨ (¬In x m ∧ MapsTo x y m2) →
                    MapsTo x y (union m m2).
Proof. refine (@M.union_spec2 _ _ _ _ _ _ _). Qed.
Lemma inter_spec : compatbb sl →
                 ((∃ y b, MapsTo x (sl x y b) (inter sl m m2)) ↔
                   In x m ∧ In x m2).
Proof. refine (@M.inter_spec _ _ _ _ _ _ _). Qed.
Lemma inter_spec1 : MapsTo x (sl x y b) (inter sl m m2) →
                    In x m ∧ In x m2.
Proof. refine (@M.inter_spec1 _ _ _ _ _ _ _ _ _). Qed.
Lemma inter_spec2 : compatbb sl →
                    MapsTo x y m ∧ MapsTo x b m2 →
                    MapsTo x (sl x y b) (inter sl m m2).
Proof. refine (@M.inter_spec2 _ _ _ _ _ _ _ _ _). Qed.
Lemma diff_spec : MapsTo x y (diff m m2) ↔ MapsTo x y m ∧ ¬In x m2.
Proof. refine (@M.diff_spec _ _ _ _ _ _ _). Qed.
  Notation func := (compose flip prod_curry).
Lemma foldl_spec : ∀ {X : Type} f (sd : X),
  foldl f m sd = fold_left (func f) (elements m) sd.
Proof. intros. refine (@M.foldl_spec _ _ _ _ _ _). Qed.
  Notation unc := prod_curry.
Lemma foldr_spec : ∀ {X : Type} f (sd : X),
  foldr f m sd = fold_right (unc f) sd (elements m).
Proof. intros. refine (@M.foldr_spec _ _ _ _ _ _). Qed.
Lemma filter_spec : compatb P →
  (MapsTo x y (filter P m) ↔ MapsTo x y m ∧ P x y = true).
Proof. refine (@M.filter_spec _ _ _ _ _ _). Qed.
  Notation nP := (λ x y, negb (P x y)).
Lemma partition_spec1 : compatb P → fst (partition P m) [=] filter P m.
Proof. refine (@M.partition_spec1 _ _ _). Qed.
Lemma partition_spec2 : compatb P → snd (partition P m) [=] filter nP m.
Proof. refine (@M.partition_spec2 _ _ _). Qed.
Lemma partition_spec : let (x,y) := partition P m in compatb P →
  x [=] filter P m ∧ y [=] filter nP m.
Proof. intro H. generalize (partition_spec1 H),
(partition_spec2 H) ; simpl; intros. split; auto. Qed.
Lemma map_spec1 : MapsTo x y m → MapsTo x (f y) (map f m).
Proof. refine (@M.map_spec1 _ _ _ _ _ _ _). Qed.
Lemma map_spec2 : In x (map f m) → In x m.
Proof. refine (@M.map_spec2 val val' _ _ _ _). Qed.
Lemma mapi_spec1 : compatb f' → MapsTo x y m → MapsTo x (f' x y) (mapi f' m).
Proof. refine (@M.mapi_spec1 val val' _ _ _ _ _). Qed.
Lemma mapi_spec2 : In x (mapi f' m) → In x m.
Proof. refine (@M.mapi_spec2 val val' _ _ _ _). Qed.
Lemma elements_spec1 : InA Kvpeq (x,y) (elements m) ↔ MapsTo x y m.
Proof. refine (@M.elements_spec1 _ _ _ _ _). Qed.
Lemma elements_spec2 : Sorted Kvplt (elements m).
Proof. refine (@M.elements_spec2 _ _ _). Qed.
Lemma elements_spec3 : NoDupA Kvpeq (elements m).
Proof. refine (@M.elements_spec3 _ _ _). Qed.
Lemma kelements_spec1 : InA keq x (kelements m) ↔ In x m.
Proof. refine (@M.kelements_spec1 _ _ _ _). Qed.
Lemma kelements_spec2 : Sorted klt (kelements m).
Proof. refine (@M.kelements_spec2 _ _ _). Qed.
Lemma kelements_spec3 : NoDupA keq (kelements m).
Proof. refine (@M.kelements_spec3 _ _ _). Qed.
Lemma choose_spec1 : choose m = Some (x,y) → MapsTo x y m.
Proof. refine (@M.choose_spec1 _ _ _ _ _). Qed.
Lemma choose_spec2 : choose m = None → Empty m.
Proof. refine (@M.choose_spec2 _ _ _). Qed. (*
Lemma choose_spec3 : choose m = Some kv1 → choose m2 = Some kv2 →
m [=] m2 → Kvp_eq kv1 kv2.
Proof. refine (@M.choose_spec3 _ _ _ _ _ _ _). Qed. *)
Lemma min_elt_spec1 : min_elt m = Some (x,y) → MapsTo x y m.
Proof. refine (@M.min_elt_spec1 _ _ _ _ _). Qed.
Lemma min_elt_spec2 : min_elt m = Some (x,y) → ∀ a, In a m → ¬klt a x.
Proof. refine (@M.min_elt_spec2 _ _ _ _ _). Qed.
Lemma min_elt_spec3 : min_elt m = None → Empty m.
Proof. refine (@M.min_elt_spec3 _ _ _). Qed.
Lemma max_elt_spec1 : max_elt m = Some (x,y) → MapsTo x y m.
Proof. refine (@M.max_elt_spec1 _ _ _ _ _). Qed.
Lemma max_elt_spec2 : max_elt m = Some (x,y) → ∀ a, In a m → ¬klt x a.
Proof. refine (@M.max_elt_spec2 _ _ _ _ _). Qed.
Lemma max_elt_spec3 : max_elt m = None → Empty m.
Proof. refine (@M.max_elt_spec3 _ _ _). Qed.

  End Vals.

End Raw2Maps.


Module KvpRelations (K:OrderedType).
  Include Kvp K.
(*  Notation key := K.t.
  Notation kvp := (prod key val).
*)
  Instance Kvpeq_compat (val:Type) :
  Proper ((Kvpeq val)==>(Kvpeq val)==>iff) (Kvplt val).
  Proof with auto.
    intros (?,?) (?,?) (A,?) (?,?)
    (?,?) (B,?). split; cbv in *;
    rewrite A,B...
  Qed.

  Instance Pkeq_compat (val:Type) :
  Proper ((Pkeq val)==>(Pkeq val)==> iff) (Kvplt val).
  Proof with auto.
  unfold Kvplt. intros (a,w) (b,x) H (c,y) (d,z) H0;
  red in H, H0; simpl in *. rewrite H, H0; split...
  Qed.


  Instance Kvpeq_refl (val:Type) : Reflexive (Kvpeq val).
  Proof with auto. split... reflexivity... Qed.
  Hint Immediate Kvpeq_refl.

  Instance Kvpeq_symm (val:Type) : Symmetric (Kvpeq val).
  Proof. intros x y (H,H0). split; auto.
  symmetry; auto. Qed. Hint Immediate Kvpeq_symm.

  Instance Kvpeq_trans (val:Type) : Transitive (Kvpeq val).
  Proof.
    intros x y z (H,H0) (H1,H2). split;
    [transitivity (fst y) |
     transitivity (snd y) ]; auto.
  Qed. Hint Resolve Kvpeq_trans.
  
  Instance Kvpeq_equiv (val:Type) : Equivalence (Kvpeq val). 
  Proof. split; auto. Qed.


  Instance Pkeq_refl (val:Type) : Reflexive (Pkeq val).
  Proof with auto. intros (x,y). red. reflexivity...
  Qed. Hint Immediate Pkeq_refl.

  Instance Pkeq_symm (val:Type) : Symmetric (Pkeq val).
  Proof. unfold Pkeq. intros x y H. 
  symmetry; auto. Qed. Hint Immediate Pkeq_symm.

  Instance Pkeq_trans (val:Type) : Transitive (Pkeq val).
  Proof.
    unfold Pkeq. intros x y z H H1.
    transitivity (fst y); auto.
  Qed. Hint Resolve Pkeq_trans.
  
  Instance Pkeq_equiv (val:Type) : Equivalence (Pkeq val). 
  Proof. split; auto. Qed.

  Instance Kvplt_irrefl (val:Type) : Irreflexive (Kvplt val).
  Proof with auto.
    intros (x,y) H.
    apply (StrictOrder_Irreflexive x)...
  Qed. Hint Resolve Kvplt_irrefl.

  Instance Kvplt_trans (val:Type) : Transitive (Kvplt val).
  Proof.
    intros (?,?) (x,?) (?,?); cbv.
    transitivity x; auto.
  Qed. Hint Resolve Kvplt_trans.

  Instance Kvplt_strord (val:Type) : StrictOrder (Kvplt val).
  Proof. split; auto. Qed.

Hint Immediate Kvpeq_equiv Pkeq_equiv Kvplt_strord.
(*
  End Vals.

Hint Immediate Kvpeq_refl Kvpeq_symm
Kvpeq_trans Kvpeq_equiv Pkeq_refl
Pkeq_symm Pkeq_trans Pkeq_equiv
Kvplt_irrefl Kvplt_trans Kvplt_strord.
*)
End KvpRelations.

Module MakeListOrdering (O:OrderedType).
 Module MO:=OrderedTypeFacts O.
 Local Notation key := O.t.
 Local Notation keq := O.eq.
 Local Notation klt := O.lt.
 Local Notation t := (list key).
 Local Notation In := (InA keq).


(*
Definition eq m m' := ∀ x:key, In x m ↔ In x m'.
*)
Definition eq := eqlistA keq.
Hint Unfold eq.
Hint Constructors eqlistA.

Instance eq_equiv : Equivalence eq.
Proof with auto.
  split.
  - intros x. reflexivity.
  - intros x y H. symmetry...
  - intros x y z H H'. transitivity y...
Qed.

Inductive lt_list : t → t → Prop :=
  | lt_nil : ∀ x s, lt_list nil (x :: s)
  | lt_cons_lt : ∀ x y s s', klt x y → lt_list (x :: s) (y :: s')
  | lt_cons_eq : ∀ x y s s', keq x y → lt_list s s' →
      lt_list (x :: s) (y :: s').
Hint Constructors lt_list.



Definition lt := lt_list.
Hint Unfold lt.

Instance lt_strorder : StrictOrder lt.
Proof with auto.
  split.
  - assert (∀ s s', s=s' → ¬lt s s').
    { intros x y H. induction 1; inversion H;
      subst... apply (MO.lt_irrefl H0)... }
    intro s. apply H...
  - intros x y z H. revert z. elim H; intros.
    + inversion_clear H0...
    + inversion_clear H1; constructor 2.
      * transitivity y0...
      * rewrite <- H2...
    + inversion_clear H3.
      * constructor 2. rewrite H0...
      * unfold lt in H2. constructor 3...
        rewrite H0...
Qed.

Instance lt_compat' :
  Proper (eq==>eq==>iff) lt.
Proof with auto.
  apply proper_sym_impl_iff_2; auto with *.
  intros a b E1 x y E2 H.
  revert b E1 y E2. induction H; intros;
  inversion_clear E1; inversion_clear E2...
  - constructor 2. MO.order.
  - constructor 3; [|apply IHlt_list]...
    transitivity y; [transitivity x;
   [symmetry|]|]...
Qed.

Lemma eq_cons l1 l2 x y :
 keq x y → eq l1 l2 → eq (x :: l1) (y :: l2).
Proof.
  unfold eq; intros Exy E12.
  constructor 2;[MO.order|auto].
Qed.
Hint Resolve eq_cons.

Lemma cons_CompSpec : forall c x1 x2 l1 l2, keq x1 x2 →
 CompSpec eq lt l1 l2 c → CompSpec eq lt (x1::l1) (x2::l2) c.
Proof.
  destruct c; simpl; inversion_clear 2; auto with relations.
Qed.

End MakeListOrdering.