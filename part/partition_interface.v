Require Import List.

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

Class varsable (A B : Type) : Type := Varsable {
  vars : A -> list B
}.
Implicit Arguments Varsable [A B].

Class EqDec (A : Type) : Type := 
 eq_dec : forall a a' : A, {a = a'} + {a <> a'}.

Definition vars_list {A} {B} `{varsable A B} : (list A) -> (list B) :=
  fold_right (fun a L' => (vars a) ++ L') nil.
Instance varsable_list {A} {B} `{varsable A B} : varsable (list A) B :=
  Varsable vars_list.

Definition var_list_extract {A B: Type} `{varsable A B} (l : list A) :
 list (list B) := map (fun e => vars e) l.

Definition disjoint_pwise {A : Type} (L : list (list A)) : Prop :=
 forall l l' i j, i <> j -> nth_op i L = Some l -> nth_op j L = Some l' -> disjoint l l'.

Fixpoint disjoint_pwise_fun {A : Type} (L : list (list A)) : Prop :=
 match L with
 | nil => True
 | l::L' => (forall l', In l' L' -> disjoint l l') /\ disjoint_pwise_fun L'
 end. 

Delimit Scope part_scope with part_scope.

Open Scope part_scope.

Class evalable (A : Type) (B : Type) : Type := Evalable {
  eval : A -> B -> Prop
}.
Implicit Arguments Evalable [A B].
Notation " rho '|=' obj " := (eval rho obj) (at level 30) : part_scope.

Class overridable (A : Type) (B : Type) : Type := Overridable {
  override : A -> A -> (list B) -> A
}.
Implicit Arguments Overridable [A B].
Notation " [ E '=>' ctx2 ']' ctx1 " := (override ctx1 ctx2 E) (at level 10) : part_scope.

Definition eval_list {A} {B} `{evalable A B} : A -> list B -> Prop := 
    fun a => fold_right (fun e t => t /\ a |= e) True.
Instance evalable_list {A} {B} `{evalable A B} : evalable A (list B):=
  Evalable eval_list.

Module Type PARTITION_INPUT.

  Parameter equation : Type.
  Parameter eqn_eq_dec : EqDec equation.
  Existing Instance eqn_eq_dec.
  Parameter var : Type.
  Parameter var_eq_dec : EqDec var.
  Existing Instance var_eq_dec.
  Parameter varsable_equation: varsable equation var.
  Existing Instance varsable_equation.

  Parameter context : Type.
  Parameter a_context : context.
  Parameter context_override : overridable context var.
  Parameter eval : evalable context equation.
  Existing Instance eval.

  Axiom eval_override_disjoint: forall 
    (l : list var) (ctx ctx' : context) (eqn : equation),
    disjoint l (vars eqn) ->
    (ctx |= eqn <-> ([l => ctx'] ctx) |= eqn).

  Axiom eval_override_sublist: forall
    (l : list var) (ctx ctx' : context) (eqn : equation),
    ctx |= eqn -> sublist (vars eqn) l ->
    ([l => ctx] ctx') |= eqn.

End PARTITION_INPUT.

Module Type PARTITION (Import pi : PARTITION_INPUT).

  Parameter partition : list equation -> list (list equation).

  Axiom partition_sublist : forall (l : list equation),
   forall l', In l' (partition l) -> sublist l' l.

  Axiom partition_exist : forall (l : list equation),
   forall e, In e l -> exists l', In l' (partition l) /\ In e l'.

  Axiom partition_disjoint : forall (l:list equation),
   disjoint_pwise (var_list_extract (partition l)).

  Axiom partition_eval: forall l rho,
   rho |= l <-> (forall l', In l' (partition l) -> rho |= l').

End PARTITION.

Module Type PARTITION_SAT (Import pi : PARTITION_INPUT).
  
  Declare Module Part : PARTITION pi.
  Import Part.

  Definition SAT := fun (l : list equation) => exists rho, rho |= l.

  Definition partition_SAT : list equation -> list (list equation) := partition.

  Axiom partition_SAT_correct1: forall l,
   SAT l -> forall l', In l' (partition_SAT l) -> SAT l'.

  Axiom partition_SAT_correct2 : forall l,
    (forall l', In l' (partition_SAT l) -> SAT l') -> SAT l.

End PARTITION_SAT.

Module Type PARTITION_IMPL (Import pi : PARTITION_INPUT).

  Definition IMPL := fun (l1 l2 : list equation) => forall rho, rho |= l1 -> rho |= l2. 
  Definition IMPL_pair (p : (list equation*list equation)): Prop := IMPL (fst p) (snd p).
  Parameter partition_IMPL : list equation -> list equation -> list (list equation*list equation).
  Parameter SAT : list equation -> Prop.

  Axiom partition_IMPL_sublist1: forall l1 l2 l1' l2',
   In (l1',l2') (partition_IMPL l1 l2) -> sublist l1' l1.

  Axiom partition_IMPL_sublist2: forall l1 l2 l1' l2',
   In (l1',l2') (partition_IMPL l1 l2) -> sublist l2' l2.

  Axiom partition_IMPL_correct1: forall l1 l2,
   (forall pl', In pl' (partition_IMPL l1 l2) -> IMPL_pair pl') ->
   IMPL l1 l2.

  Axiom partition_IMPL_In1: forall l1 l2 eqn,
   In eqn l1 -> exists l1' l2', In eqn l1' /\ In (l1',l2') (partition_IMPL l1 l2).

  Axiom partition_IMPL_In2: forall l1 l2 eqn,
   In eqn l2 -> exists l1' l2', In eqn l2' /\ In (l1',l2') (partition_IMPL l1 l2).

  Axiom partition_IMPL_disjoint: forall l1 l2 l1' l2' l1'' l2'' i j,
   nth_op i (partition_IMPL l1 l2) = Some (l1',l2') ->
   nth_op j (partition_IMPL l1 l2) = Some (l1'',l2'') ->
   i <> j -> disjoint (vars (l1'++l2')) (vars (l1''++l2'')).

  Axiom partition_IMPL_correct2 : forall l1 l2,
   SAT l1 -> IMPL l1 l2 ->
   forall pl', In pl' (partition_IMPL l1 l2) -> IMPL_pair pl'.

End PARTITION_IMPL.

Close Scope part_scope.
   