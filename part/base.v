(* Begin MSL *)

(** This file collects some axioms used throughout the Mechanized Semantic Library development.
  This file was developed in 2010 by Andrew W. Appel and Xavier Leroy, and harmonizes
  the axioms used by MSL and by the CompCert project.
 *)

Require ClassicalFacts.

(** * Extensionality axioms *)

(** The following [Require Export] gives us functional extensionality for dependent function types:
<<
Axiom functional_extensionality_dep : forall {A} {B : A -> Type}, 
  forall (f g : forall x : A, B x), 
  (forall x, f x = g x) -> f = g.
>> 
and, as a corollary, functional extensionality for non-dependent functions:
<<
Lemma functional_extensionality {A B} (f g : A -> B) : 
  (forall x, f x = g x) -> f = g.
>>
*)
Require Export FunctionalExtensionality.

(** For compatibility with earlier developments, [extensionality]
  is an alias for [functional_extensionality]. *)

Lemma extensionality:
  forall (A B: Type) (f g : A -> B),  (forall x, f x = g x) -> f = g.
Proof. intros; apply functional_extensionality. auto. Qed.

Implicit Arguments extensionality.

(** We also assert propositional extensionality. *)

Axiom prop_ext: ClassicalFacts.prop_extensionality.
Implicit Arguments prop_ext.

(** * Proof irrelevance *)

(** We also use proof irrelevance, which is a consequence of propositional
    extensionality. *)

Lemma proof_irr: ClassicalFacts.proof_irrelevance.
Proof.
  exact (ClassicalFacts.ext_prop_dep_proof_irrel_cic prop_ext).
Qed.
Implicit Arguments proof_irr.

Require Import EqdepFacts.

(* From EqdepTh we obtain inj_pair and inj_pairT2 without
   use of excluded middle:
 *)
Module EqdepElim: EqdepElimination.
Lemma eq_rect_eq :
    forall (U:Type) (p:U) (Q:U -> Type) (x:Q p) (h:p = p),
      x = eq_rect p Q x p h.
Proof.
  intros.
  apply Streicher_K__eq_rect_eq.
  apply UIP_refl__Streicher_K.
  unfold UIP_refl_.
  intros.
  apply proof_irr.
Qed.
End EqdepElim.

Module EqdepTh := EqdepTheory EqdepElim.
Export EqdepTh.

(* Generalize the extensionality tactic from the Coq library. *)
Tactic Notation "extensionality" := 
 let x := fresh "x" in extensionality x.

Tactic Notation "extensionality" ident(x) ident(y) := 
    extensionality x; extensionality y.

Tactic Notation "extensionality" ident(x) ident(y) ident(z):= 
    extensionality x; extensionality y z.

Lemma imp_ext: forall (A A' B B' : Prop), (A=A') -> (A -> (B=B')) -> ((A->B)=(A'->B')).
Proof.
intros.
subst A'.
apply prop_ext; split; intros; auto.
rewrite <- H0; auto. rewrite H0; auto.
Qed.

Lemma exists_ext: forall (A: Type) F G, (forall x: A, F x = G x) -> (Logic.ex F = Logic.ex G).
Proof.
intros.
apply prop_ext; split; intro; destruct H0; exists x.
rewrite <- H; auto.
rewrite H; auto.
Qed.


Lemma and_ext: forall A B C D, A=B -> C=D -> (A /\ C) = (B /\ D).
Proof.
intros.
rewrite H; rewrite H0; auto.
Qed.

Lemma and_ext': forall (A: Prop) B C D, A=B -> (A -> (C=D)) -> (A /\ C) = (B /\ D).
Proof.
intros.
subst B.
apply prop_ext.
intuition; subst; auto.
Qed.

Lemma or_ext: forall A B C D, A=B -> C=D -> (A \/ C) = (B \/ D).
Proof.
intros.
rewrite H; rewrite H0; auto.
Qed.

Lemma forall_ext: forall (A: Type) (F: A -> Prop) G, (forall x:A, F x = G x) -> (forall x, F x) = (forall x, G x).
Proof.
intros.
apply prop_ext. split; intros. rewrite <- H; auto. rewrite H; auto.
Qed.

Lemma existT_ext:
  forall (A: Type) (P: A -> Prop) (x y: A) (Hx: P x) (Hy: P y),
     x = y -> existT _ x Hx = existT _ y Hy.
Proof.
intros.
subst.
rewrite (proof_irr Hx Hy); auto.
Qed.

Lemma exist_ext:
  forall (A: Type) (P: A -> Prop) (x y: A) (Hx: P x) (Hy: P y),
     x = y -> exist _ x Hx = exist _ y Hy.
Proof.
intros.
subst.
rewrite (proof_irr Hx Hy); auto.
Qed.

Require Import Omega.

Definition compose (A B C:Type) (g:B -> C) (f:A -> B) := fun x => g (f x).
Implicit Arguments compose [A B C].
Infix "oo" := compose (at level 54, right associativity).

Lemma compose_assoc (A B C D:Type) (h:C->D) (g:B->C) (f:A->B) :
  (h oo g) oo f = h oo g oo f.
Proof.
  intros; apply extensionality; intro x; unfold compose; auto.
Qed.

Definition id (A:Type) := fun x:A => x.

Lemma id_unit1 : forall A B (f:A->B), f oo id A = f.
Proof.
  intros; apply extensionality; intro x; auto.
Qed.

Lemma id_unit2 : forall A B (f:A->B), id B oo f = f.
Proof.
  intros; apply extensionality; intro x; auto.
Qed.

Record bijection (A B:Type) : Type := Bijection {
  bij_f: A -> B;
  bij_g: B -> A;
  bij_fg: forall x, bij_f (bij_g x) = x;
  bij_gf: forall x, bij_g (bij_f x) = x
}.

(** Perform inversion on a hypothesis, removing it from the context, and
    perform substitutions
  *)
Tactic Notation "inv" hyp(H) := inversion H; clear H; subst.

Ltac detach H :=
  match goal with [ H : (?X -> ?Y) |- _ ] =>
    cut Y; [ clear H; intro H | apply H; clear H ]
  end.

(** Specialize a hypothesis with respect to specific terms or proofs. *)
Tactic Notation "spec" hyp(H) :=
  match type of H with ?a -> _ => 
    let H1 := fresh in (assert (H1: a); [|generalize (H H1); clear H H1; intro H]) end.

Tactic Notation "spec" hyp(H) constr(a) :=
  (generalize (H a); clear H; intro H). 

Tactic Notation "spec" hyp(H) constr(a) constr(b) :=
  (generalize (H a b); clear H; intro H).

 Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) :=
  (generalize (H a b c); clear H; intro H).

Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) constr(d) :=
  (generalize (H a b c d); clear H; intro H).

Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) constr(d) constr(e) :=
  (generalize (H a b c d e); clear H; intro H).

(* Some further tactics, from Barrier Project *)

Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) constr(d) constr(e) constr(f) :=
  (generalize (H a b c d e f); clear H; intro H).

Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) constr(d) constr(e) constr(f) constr(g) :=
  (generalize (H a b c d e f g); clear H; intro H).

Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) constr(d) constr(e) constr(f) constr(g) constr(h) :=
  (generalize (H a b c d e f g h); clear H; intro H).

Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) constr(d) constr(e) constr(f) constr(g) constr(h) constr(i) :=
  (generalize (H a b c d e f g h i); clear H; intro H).

Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) constr(d) constr(e) constr(f) constr(g) constr(h) constr(i) constr(j) :=
  (generalize (H a b c d e f g h i j); clear H; intro H).

Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) constr(d) constr(e) constr(f) constr(g) constr(h) constr(i) constr(j) constr(k) :=
  (generalize (H a b c d e f g h i j); clear H; intro H).

Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) constr(d) constr(e) constr(f) constr(g) constr(h) constr(i) constr(j) constr(k) constr(l) :=
  (generalize (H a b c d e f g h i j); clear H; intro H).

Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) constr(d) constr(e) constr(f) constr(g) constr(h) constr(i) constr(j) constr(k) constr(l) constr(m) :=
  (generalize (H a b c d e f g h i j); clear H; intro H).

Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) constr(d) constr(e) constr(f) constr(g) constr(h) constr(i) constr(j) constr(k) constr(l) constr(m) constr(n) :=
  (generalize (H a b c d e f g h i j); clear H; intro H).

Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) constr(d) constr(e) constr(f) constr(g) constr(h) constr(i) constr(j) constr(k) constr(l) constr(m) constr(n) constr(o) :=
  (generalize (H a b c d e f g h i j); clear H; intro H).

Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) constr(d) constr(e) constr(f) constr(g) constr(h) constr(i) constr(j) constr(k) constr(l) constr(m) constr(n) constr(o) constr(p) :=
  (generalize (H a b c d e f g h i j); clear H; intro H).

Tactic Notation "disc" := (try discriminate).

Tactic Notation "contr" := (try contradiction).

Tactic Notation  "icase" constr(v) := (destruct v; disc; contr; auto).

Tactic Notation "omegac" := (elimtype False; omega).

Tactic Notation "copy" hyp(H) := (generalize H; intro).

(* End MSL *)

Definition is_Some {A} (o : option A) : Prop :=
  match o with None => False | _ => True end.

Lemma pred_txe: forall P1 P2,
  (P1 = P2) ->
  (P1 <-> P2).
Proof. intros; subst; tauto. Qed.

Definition set {A : Type} : Type := A -> Prop.
Definition empty_set {A : Type} : set := 
  fun (a : A) => False.
Definition set_singleton {A : Type} (a : A) : set :=
  fun a' => a = a'.
Definition set_union {A} (S1 S2 : set) : set :=
  fun a : A => S1 a \/ S2 a.


