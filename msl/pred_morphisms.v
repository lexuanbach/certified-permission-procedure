(*
 * Copyright (c) 2009-2011, Andrew Appel, Robert Dockins and Aquinas Hobor.
 *
 *
 * Morphisms over the separation logic to provide setoid equivalence without
 * extensionality.
 * For general use: Import pred_morphisms_all.
 *
 * This file was developed by CJ Bell.
 *)

Module predicates_hered.
  Require Import Setoid.
  Require Export Coq.Classes.Morphisms.
  Export SetoidTactics.
  Require Export SetoidClass.

  Require Import msl.ageable.
  Require Import msl.predicates_hered.

  Delimit Scope pred with pred.
  Local Open Scope pred.

  Lemma derives_trans {A:Type} {as_age: ageable A}: forall x y z, x |-- y -> y |-- z -> x |-- z.
    Proof. intros; apply derives_cut with y; auto. Qed.

  Add Parametric Relation (A:Type) (as_age: ageable A): (pred A) (@derives A as_age)
    reflexivity proved by derives_refl
    transitivity proved by derives_trans
    as derives_rel.

  Program Instance PredSetoid : forall {A:Type} {H: ageable A}, Setoid (pred A) :=
      { equiv:= (fun P Q => (P |-- Q) /\ (Q |-- P)) }.
  Solve Obligations using firstorder.

  (* Used for exp and allp *)
  Program Instance FunPredSetoid : forall {A:Type} {H: ageable A} {B:Type}, Setoid (B -> pred A) :=
      { equiv:= (fun P Q => forall (b:B), P b == Q b) }.
  Solve Obligations using firstorder.

  Definition fun_equiv {A:Type} {H: ageable A} {B:Type} := (fun (P Q: B->@pred A H) => (fun (b:B) => P b) == (fun (b:B) => Q b)).


  Add Parametric Morphism A (H: ageable A): (@derives A H)
  with signature equiv ==> equiv ==> equiv
  as derives_m.
    firstorder.
  Qed.

  Add Parametric Morphism A (H: ageable A): (@app_pred A H)
  with signature equiv ==> eq ==> equiv
  as forces_m.
    firstorder.
  Qed.

  Hint Unfold derives andp orp imp prop.


  (* && *)
  Add Parametric Morphism A (as_age : ageable A): (@andp A as_age)
  with signature equiv ==> equiv ==> equiv
  as intersection_m.
    split; repeat intro; destruct H1;
      (split; [apply H; auto | apply H0; auto]).
  Qed.

  (* || *)
  Add Parametric Morphism A (as_age : ageable A): (@orp A as_age)
  with signature equiv ==> equiv ==> equiv
  as union_m.
    intros; destruct H; destruct H0; split; 
      repeat intro; simpl in *; intuition.
  Qed.

  (* --> *)
  Add Parametric Morphism A (as_age : ageable A): (@imp A as_age)
  with signature equiv ==> equiv ==> equiv
  as implies_m.
    split; repeat intro; simpl in *; intuition.
  Qed.

  (* exists *)
  Program Instance exists_m {A : Type} (as_age : ageable A) B :
    Proper (pointwise_relation B equiv ==> equiv)%signature (@exp A as_age B).
  Next Obligation.
    split; repeat intro; simpl in *;
      destruct H0 as [b]; exists b; apply H; auto.
  Qed.

  (* forall *)
  Program Instance forall_m {A : Type} (as_age : ageable A) B :
    Proper (pointwise_relation B equiv ==> equiv)%signature (@allp A as_age B).
  Next Obligation.
    split; repeat intro; simpl in *; apply H; auto.
  Qed.

  (* !! *)
  Add Parametric Morphism A (as_age : ageable A): (@prop A as_age)
  with signature equiv ==> equiv
  as prop_m.
    split; repeat intro; simpl in *; apply H; auto.
  Qed.

  (* [], |>, etc. *)
  Add Parametric Morphism A (as_age : ageable A): (@box A as_age)
  with signature eq ==> equiv ==> equiv
  as box_m.
    split; repeat intro; simpl in *; apply H; auto.
  Qed.

  Add Parametric Morphism A (as_age : ageable A): (@diamond A as_age)
  with signature eq ==> equiv ==> equiv
  as diamond_m.
    split; repeat intro; simpl in *; destruct H0 as [a'[??]]; exists a'; intuition.
  Qed.

  Module Lemmas.
    Lemma derives_equiv: forall {A:Type} {H:ageable A} (P Q: pred A),
      P |-- Q -> Q |-- P -> P == Q.
    Proof. firstorder. Qed.

    Hint Resolve @derives_equiv : seplog_hints.

    Lemma box_refl_trans {A} `{ageable A}: forall (m:modality) p,
      reflexive _ m ->
      transitive _ m ->
      box m (box m p) == box m p.
    Proof.
      split; repeat intro.
      assert (box m p a').
        apply H2; auto.
      apply H4; apply H0.
      apply H2; eapply H1; eauto.
    Qed.

    Lemma box_and {A:Type} {as_age: ageable A}: forall R (P Q:pred A),
      box R (P && Q) == box R P && box R Q.
    Proof.
      split; repeat intro; unfold andp, box in *; simpl in *; firstorder.
    Qed.

    Lemma box_all {A:Type}  {as_age: ageable A} : forall B R (F:B -> pred A),
      box R (allp F) == All x:B, box R (F x).
    Proof.
      split; repeat intro; unfold allp, box in *; simpl in *; firstorder.
    Qed.

    Lemma diamond_or {A:Type}  {as_age: ageable A} : forall R (P Q:pred A),
      diamond R (P || Q) == diamond R P || diamond R Q.
    Proof.
      split; repeat intro; unfold diamond, orp in *; simpl in *; firstorder.
    Qed.

    Lemma diamond_ex {A:Type}  {as_age: ageable A} : forall B R (F:B -> pred A),
      diamond R (exp F) == Ex x:B, diamond R (F x).
    Proof.
      split; repeat intro; unfold diamond, exp in *; simpl in *; firstorder.
    Qed.

    Lemma later_age {A:Type}  {as_age: ageable A} : forall P,
      |>P == box ageM P.
    Proof.
      split; repeat intro.
      simpl in H.
      apply H.
      apply Relation_Operators.t_step; auto.
      revert H; induction H0; intros.
      apply H0; auto.
      apply pred_nec_hereditary with y.
      apply Rt_Rft; auto.
      apply IHclos_trans1; auto.
    Qed.

    Lemma later_commute {A:Type}  {as_age: ageable A} : forall M (P:pred A),
      box M (|>P) == |>(box M P).
    Proof.
      split; repeat intro.
      destruct M as [R HR].
      destruct (valid_rel_commut_later2 R HR _ _ H1 _ H0).
      apply H with x; simpl; auto.
      destruct M as [R HR].
      destruct (valid_rel_commut_later1 R HR _ _ H1 _ H0).
      apply H with x; auto.
    Qed.

    Lemma later_and {A:Type}  {as_age: ageable A} : forall P Q,
      |>(P && Q) == |>P && |> Q.
    Proof. intros; apply box_and. Qed.

    Lemma later_or {A:Type}  {as_age: ageable A} : forall (P Q:pred A),
      |>(P || Q) == |>P || |>Q.
    Proof.
      setoid_rewrite later_age.
      split; repeat intro.
      simpl in H.
      case_eq (age1 a); intros.
      destruct (H a0); auto.
      left; simpl; intros; replace a' with a0; auto; congruence.
      right; simpl; intros; replace a' with a0; auto; congruence.
      left; simpl; unfold age; intros; rewrite H0 in H1; discriminate.
      destruct H.
      left; apply H. auto.
      right; apply H. auto.
    Qed.

    Lemma later_ex {A:Type} {as_age: ageable A} : forall B (F:B->pred A),
      B -> |>(exp F) == Ex x:B, |>(F x).
    Proof.
      intros.
      rewrite later_age.
      split; repeat intro.
      case_eq (age1 a); intros.
      destruct (H a0); auto.
      exists x.
      apply later_age; simpl; intros.
      replace a' with a0; auto; congruence.
      exists X.
      apply later_age.
      hnf; simpl; intros.
      unfold age in H1.
      rewrite H0 in H1; discriminate.
      eapply box_ex; eauto. simpl in *.
      unfold laterR; constructor; auto.
    Qed.

    Lemma later_impl {A:Type} {as_age: ageable A} : forall P Q,
      |>(P --> Q) == |>P --> |>Q.
    Proof.
      intros; repeat rewrite later_age.
      split; intros.
      apply axiomK.
      repeat intro.
      simpl in H.
      destruct valid_rel_nec.
      destruct (H4 _ _ H1 _ H0).
      apply H with x; auto.
      intros; replace a'1 with a'0; auto; congruence.
    Qed.

    Lemma TT_and {A:Type} {as_age: ageable A}: forall P,
      TT && P == P.
    Proof. split; auto with seplog_hints; repeat intro; simpl in *; intuition. Qed.

    Lemma ex_and : forall {A:Type} {as_age: ageable A} B (P:B->pred A) Q,
      (exp P) && Q == Ex x:B, P x && Q.
    Proof.
      split; repeat intro.
      destruct H as [[x]?].
      exists x. split; auto.
      repeat intro.
      destruct H as [b[??]].
      split; auto. exists b; auto.
    Qed.

    Lemma FF_and : forall {A:Type} {as_age: ageable A} (P:pred A),
      FF && P == FF.
    Proof. split; auto with seplog_hints; repeat intro; simpl in *; intuition. Qed.

    Lemma imp_andp_adjoint {A} {as_age: ageable A} : forall (P Q R:pred A),
      ((P && Q) |-- R) == (P |-- (Q --> R)).
    Proof.
      split; repeat intro.
      apply H; split; auto.
      apply pred_nec_hereditary with a; auto.
      destruct H0.
      apply H in H0.
      apply H0; auto.
    Qed.

    Lemma box_diamond {A} `{ageable A} : forall M (P Q:pred A),
      ((diamond M P) |-- Q) == (P |-- (box M Q)).
    Proof.
      unfold derives; split; intuition.
      hnf; intros.
      apply H0.
      hnf; eauto.
      destruct H1 as [a' [? ?]].
      apply H0 with a'; auto.
    Qed.

    Lemma or_dup {A:Type} {age: ageable A}: forall P,
      P || P == P.
    Proof. split; repeat intro; simpl in *; intuition. Qed.

    Lemma and_dup {A:Type} {age: ageable A}: forall P,
      P && P == P.
    Proof. split; repeat intro; simpl in *; intuition. Qed.


  End Lemmas.

  Module Examples.
    Open Scope pred.

    Lemma test_exists_morphism: forall (A:Type) (as_age:ageable A) (B: Type) (C D: B->pred A),
      (forall x, C x == D x) -> (Ex x:B, C x == Ex y:B, D y).
    Proof. intros; setoid_rewrite H; reflexivity. Qed.
    Lemma test_exists_morphism2: forall (A:Type) (as_age:ageable A) (B: Type) (C: B->pred A) (D E:pred A),
      D==E -> (Ex x:B, (C x && D) == Ex y:B, (C y && E)).
    Proof. intros. setoid_rewrite H; reflexivity. Qed.
    Lemma test_forall_morphism: forall (A:Type) (as_age:ageable A) (B: Type) (C D: B->pred A),
      (forall x, C x == D x) -> (All x:B, C x == All y:B, D y).
    Proof. intros. setoid_rewrite H. reflexivity. Qed.
    Lemma test_forall_morphism2: forall (A:Type) (as_age:ageable A) (B: Type) (C: B->pred A) (D E:pred A),
      D==E -> (All x:B, (C x && D) == All y:B, (C y && E)).
    Proof. intros. setoid_rewrite H; reflexivity. Qed.
    Lemma test_later_morphism {T:Type} {age:ageable T}: forall A B,
      A == B -> (|> A == |> B).
    Proof. intros; rewrite  H; reflexivity. Qed.
    Lemma test_prop_morphism {T:Type} {age:ageable T}: forall A B,
      A == B -> (!! A == !! B).
    Proof. intros; rewrite  H; reflexivity. Qed.
    Lemma test_derives_morphism {T:Type} {age:ageable T}: forall A B,
      A == B -> ( A|-- B).
    Proof. intros; rewrite  H; auto. Qed.
    Lemma test_forces_morphism {T:Type} {age:ageable T}: forall (A B: pred T) a,
      A == B -> A a -> B a.
    Proof. intros; rewrite<-  H; auto. Qed.
    Lemma test_and_morphism {T:Type} {age:ageable T}: forall A B C D,
      A == B -> C == D -> (A && C == B && D).
    Proof. intros; rewrite H; rewrite H0; reflexivity. Qed.
    Lemma test_or_morphism {T:Type} {age:ageable T}: forall A B C D,
      A == B -> C == D -> (A || C == B || D).
    Proof. intros; rewrite H; rewrite H0; reflexivity. Qed.
    Lemma test_impl_morphism {T:Type} {age:ageable T}: forall A B C D,
      A == B -> C == D -> (A --> C == B --> D).
    Proof. intros; rewrite H; rewrite H0; reflexivity. Qed.
 
  End Examples.

End predicates_hered.


Module predicates_sl.
  Require Import Setoid.

  Require Import msl.ageable.
  Require Import msl.sepalg.
  Require Import msl.age_sepalg.
  Require Import msl.predicates_sl.

  Import predicates_hered.

  Delimit Scope pred with pred.
  Local Open Scope pred.

  Hint Unfold sepcon wand.
  Hint Resolve @join_com.
  Hint Resolve @join_eq.

  (* * *)
  Add Parametric Morphism A (as_alg : sepalg A) (as_age : ageable A) (H: ASA A): (@sepcon A as_alg as_age H)
  with signature equiv ==> equiv ==> equiv
  as sep_con_m.
    split; repeat intro; destruct H2 as [a1[a2[?[??]]]];
      exists a1; exists a2;
      split; auto;
      (split; [apply H0; auto | apply H1; auto]).
  Qed.

  (* -* *)
  Add Parametric Morphism A (as_alg : sepalg A) (as_age : ageable A) (H: ASA A): (@wand A as_alg as_age H)
  with signature equiv ==> equiv ==> equiv
  as wand_m.
    split; intros; repeat intro.
    setoid_rewrite<- H1.
    apply H2 with x' y1; auto.
    setoid_rewrite H0; auto.
    repeat intro. setoid_rewrite H1.
    apply H2 with x' y1; auto.
    setoid_rewrite<- H0; auto.
  Qed.

  Add Parametric Morphism A (as_alg : sepalg A) (as_age : ageable A) (H: ASA A): (@ewand A as_alg as_age H)
  with signature equiv ==> equiv ==> equiv
  as ewand_m.
    split; intros; repeat intro; simpl; simpl in H2.
    setoid_rewrite<- H1.
    setoid_rewrite<- H0.
    apply H2.
    setoid_rewrite H1.
    setoid_rewrite H0.
    apply H2.
  Qed.

  Module Lemmas.
    Import msl.predicates_hered.
    Require Import msl.cross_split.

    Lemma wand_sepcon_adjoint {A} `{ASA A} : forall (P Q R:pred A),
      ((P * Q) |-- R) == (P |-- (Q -* R)).
    Proof.
      split; intros.
      hnf; intros; simpl; intros.
      apply H0.
      exists x'; exists y.
      intuition.
      apply pred_nec_hereditary with a; auto.
      hnf; intros.
      hnf in H0.
      unfold wand in H0; simpl in H0.
      destruct H1 as [w [v [? [? ?]]]].
      eapply H0; eauto.
    Qed.

    Lemma sepcon_assoc {A} `{ASA A} : forall (P Q R:pred A),
      (P * Q) * R == P * (Q * R).
    Proof.
      split; intros; hnf; intros.
      destruct H0 as [x [y [? [? ?]]]].
      destruct H1 as [z [w [? [? ?]]]].
      destruct (join_assoc H1 H0) as [q [? ?]].
      exists z; exists q; intuition.
      exists w; exists y; intuition.
      destruct H0 as [x [y [? [? ?]]]].
      destruct H2 as [z [w [? [? ?]]]].
      apply join_com in H0.
      apply join_com in H2.
      destruct (join_assoc H2 H0) as [q [? ?]].
      exists q; exists w; intuition.
      exists x; exists z; intuition.
    Qed.

    Lemma sepcon_comm {A} `{ASA A} : forall (P Q:pred A),
      P * Q == Q * P.
    Proof.
      split; repeat intro;
        destruct H0 as [a1[a2[?[??]]]]; exists a2; exists a1; intuition.
    Qed.

    Lemma emp_sepcon {A} `{ASA A} : forall (P:pred A),
      emp * P == P.
    Proof.
      split; repeat intro.
      repeat intro. destruct H0 as [a1[a2[?[??]]]].
      replace a with a2; auto.
      destruct (join_ex_units a) as [unit H1].
      exists unit; exists a; intuition.
      simpl; apply unit_identity with a; auto.
    Qed.

    Lemma sepcon_emp {A} `{ASA A} : forall (P:pred A),
      P * emp == P.
    Proof.
      intros.
      setoid_rewrite sepcon_comm.
      apply emp_sepcon.
    Qed.

(*
    Lemma emp_sepcon : forall {A} `{ASA A} (P:pred A),
      emp * P == P. 
    Proof. exact @emp_sepcon. Qed.
    Lemma sepcon_emp : forall {A} `{ASA A} (P:pred A),
      P * emp == P.
    Proof. exact @sepcon_emp. Qed.
*)
    Lemma later_wand {A} `{ASA A} : forall P Q,
      |>(P -* Q) == |>P -* |>Q.
    Proof.
      split; repeat rewrite later_age; repeat intro.
      simpl in *.
      case_eq (age1 a); intros. 
      specialize (H0 a0 H5).
      apply nec_refl_or_later in H1.
      destruct H1; subst.
      destruct (age1_join2 _ H2 H4) as [w [v [? [? ?]]]].
      eapply H0; eauto.
      replace a0 with w; auto.
      congruence.
      assert (necR a0 x').
      eapply age_later_nec; eauto.
      destruct (age1_join2 _ H2 H4) as [w [v [? [? ?]]]].
      apply H0 with w v; auto.
      apply Relation_Operators.rt_trans with x'; auto.
      apply Relation_Operators.rt_step; auto.
      apply nec_refl_or_later in H1; destruct H1; subst.
      destruct (age1_join2 _  H2 H4) as [w [v [? [? ?]]]].
      hnf in H6.
      rewrite H5 in H6; discriminate.
      clear -H1 H5.
      elimtype False.
      revert H5; induction H1; auto.
      intros.
      unfold age in H.
      rewrite H in H5; discriminate.

      simpl in H0.
      destruct (valid_rel_nec).
      destruct (H6 _ _ H2 _ H1).
      destruct (unage_join _ H3 H7) as [w [v [? [? ?]]]].
      apply H0 with x w v; auto.
      intros.
      replace a'0 with y; auto.
      congruence.
    Qed.

    Lemma later_sepcon {A} `{ASA A} : forall P Q,
      |>(P * Q) == |>P * |>Q.
    Proof.
      split; intros; repeat rewrite later_age; repeat intro.
      hnf; intros.
      simpl in H0.
      case_eq (age1 a); intros.
      destruct (H0 a0) as [w [v [? [? ?]]]]; auto.
      destruct (unage_join2 _ H2 H1) as [w' [v' [? [? ?]]]].
      exists w'; exists v'; intuition.
      simpl; intros.
      replace a' with w; auto.
      unfold age in *; congruence.
      simpl; intros.
      replace a' with v; auto.
      unfold age in *; congruence.
      destruct (join_ex_units a).
      exists x; exists a.
      intuition.
      hnf; intros.
      red in u.
      simpl in H2.
      destruct (age1_join _ u H2) as [s [t [? [? ?]]]].
      unfold age in H5.
      rewrite H1 in H5; discriminate.
      hnf; intros.
      simpl in H2.
      unfold age in H2.
      rewrite H1 in H2; discriminate.
  
      destruct H0 as [w [v [? [? ?]]]].
      hnf; intros.
      simpl in H3.
      destruct (age1_join2 _ H0 H1) as [w' [v' [? [? ?]]]].
      exists w'; exists v'; intuition.
    Qed.

    Lemma FF_sepcon : forall {A} `{ASA A} (P:pred A),
      FF * P == FF.
    Proof.
      split; repeat intro.
      destruct H0 as [? [? [? [? ?]]]].
      elim H1.
      elim H0.
    Qed.

    Lemma exists_sepcon1 {A} `{ASA A}: forall T (P: T ->  pred A) Q,
      exp P * Q == exp (fun x => P x * Q).
    Proof.
      split; intros ? ?.
      destruct H0 as [w1 [w2 [? [[x ?] ?]]]].
      exists x; exists w1; exists w2; split; auto.
      destruct H0 as [x [w1 [w2 [? [? ?]]]]].
      exists w1; exists w2; split; auto.
      split; auto.
      exists x; auto.
    Qed.

    Lemma extend_later {A} `{asaA : ASA A} : forall P,
      %|>P == |>%P.
    Proof. split; intros; rewrite later_commute; auto. Qed.

    Lemma age_sepcon {A} `{H : ASA A} : forall P Q,
      box ageM (P * Q) == box ageM P * box ageM Q.
    Proof.
      split; repeat intro.
      case_eq (age1 a); intros.
      destruct (H0 a0) as [u [v [? [? ?]]]]; auto.
      red.
      destruct (unage_join2 _ H2 H1) as [x [y [? [? ?]]]].
      exists x; exists y.
      intuition.
      hnf; intros.
      replace a' with u; auto.
      unfold age in *; congruence.
      hnf; intros.
      replace a' with v; auto.
      unfold age in *; congruence.
      destruct (join_ex_units a).
      exists x; exists a.
      intuition.
      hnf; intros.
      red in u.
      destruct (age1_join _ u H2)
        as [p [q [? [? ?]]]]; auto.
      unfold age in *.
      rewrite H1 in H4; discriminate.
      hnf; intros.
      simpl in *.
      unfold age in *.
      rewrite H1 in H2; discriminate.

      destruct H0 as [u [v [? [? ?]]]].
      destruct (age1_join2 _ H0 H1)
        as [p [q [? [? ?]]]]; auto.
      exists p; exists q; intuition.
    Qed.

    Lemma sepcon_andp_prop {A} `{HA: ASA A}: forall P Q R,
      P * (!!Q && R) == !!Q && (P * R).
    Proof.
      split; intros w ?.
      destruct H as [w1 [w2 [? [? [? ?]]]]].
      split. apply H1.
      exists w1; exists w2; split; [|split]; auto.
      destruct H.
      destruct H0 as [w1 [w2 [? [? ?]]]].
      exists w1; exists w2; repeat split; auto.
    Qed.

    Lemma TT_sepcon_TT {A} `{ASA A}:
      TT * TT == TT.
    Proof.
      split; intros w ?; auto.
      destruct (join_ex_units w).
      exists x; exists w; split; auto.
    Qed.
 
    Lemma join_exactly {A} `{ASA A}: forall w1 w2 w3,
      join w1 w2 w3 -> exactly w1 * exactly w2 == exactly w3.
    Proof.
      intros.
      unfold exactly.
      split; intros w ?; simpl in *.
      destruct H1 as [? [? [? [? ?]]]].
      destruct (nec_join H0 H2) as [a [b [? [? ?]]]].
      assert (x0=a).
        eapply necR_linear'; eauto. 
        transitivity (level x).
        symmetry; apply comparable_fashionR. eapply join_comparable2; eauto.
        apply comparable_fashionR. eapply join_comparable2; eauto.
      subst x0.
      generalize (join_eq H4 H1); clear H4; intro; subst.
      auto.
      eapply nec_join2; eauto.
    Qed.

    Lemma exists_expand_sepcon {A} `{saA : ASA A}: forall B (p: B -> pred A) q,
      exp p * q == exp (fun x => p x * q).
    Proof.
      split; intros w ?.
      destruct H as [? [? [? [? ?]]]].
      destruct H0.
      exists x1; exists x; exists x0; split; auto.
      destruct H as [? [? [? [? [? ?]]]]].
      exists x0; exists x1; split; auto.
      split; auto.
      exists x; auto.
    Qed.

    Lemma exists_expand_sepcon' {A} `{saA : ASA A}: forall B p (q: B -> pred A),
      p * exp q == exp (fun x => p * q x).
    Proof.
      split; intros w ?.
      destruct H as [? [? [? [? ?]]]].
      destruct H1.
      exists x1; exists x; exists x0; split; auto.
      destruct H as [? [? [? [? [? ?]]]]].
      exists x0; exists x1; split; auto.
      split; auto.
      exists x; auto.
    Qed.

    Lemma precise_equiv {A} `{saA : ASA A}: forall (P: pred A),
      precise P == forall Q R, P * (Q && R) == (P * Q) && (P * R).
    Proof.
      unfold precise.
      split; intros.
      split; repeat intro; rename a into w.
      destruct H0 as [phi1 [phi2 [? [? [? ?]]]]].
      split; exists phi1; exists phi2; auto.
      destruct H0 as [[phi1a [phi2a [? [? ?]]]] [phi1b [phi2b [? [? ?]]]]].
      specialize (H w _ _ H1 H4).
      replace phi1b with phi1a in *;
        [| apply H; eexists; eauto].
      generalize (join_canc (join_com H0) (join_com H3)).
      intro; subst phi2b.
      exists phi1a; exists phi2a; intuition.
      split; auto.
      rename w1 into w1a.
      rename w2 into w1b.
      destruct H2 as [w2a ?].
      destruct H3 as [w2b ?].
      assert (((P * exactly w2a) && (P * exactly w2b)) w).
      split; do 2 econstructor; repeat split; 
      try solve [simpl; apply necR_refl].
      eassumption. auto. eassumption. auto.
      rewrite <- H in H4.
      destruct H4 as [w1 [w2 [? [? [? ?]]]]].
      simpl in H6,H7.
      rewrite (necR_comparable _ _ H6) in H2.
      rewrite (necR_comparable _ _ H7) in H3.
      eapply join_canc; eauto.
      apply comparable_trans with w.
      apply join_comparable with w1b; auto.
      apply comparable_sym; apply join_comparable with w1; auto.
      apply comparable_trans with w.
      apply join_comparable with w1a; auto.
      apply comparable_sym; apply join_comparable with w1; auto.
    Qed.

    Lemma emp_ewand {A} `{ASA A}:  forall P,
      ewand emp P == P.
    Proof.
      split; intros w ?.
      destruct H0 as [w1 [w2 [? [? ?]]]].
      replace w with w2; auto.
      eapply join_eq; eauto.
      eapply identity_unit; eauto.
      destruct (join_ex_units w) as [e ?].
      exists e; exists w.
      split; auto. split; auto.
      simpl; eapply unit_identity; eauto.
    Qed.

    Lemma pry_apart {A} `{ASA A}: forall G P Q,
      cross_split -> superprecise G -> P == ewand G (G * P) ->
      (P * Q) && (G * TT) |-- (P * G * (ewand G Q)).
    Proof.
      intros until Q. intro CS; intros.
      intros w [? ?].
      destruct H2 as [w2 [w3 [? [? Hq]]]].
      destruct H3 as [w4 [w5 [? [? _]]]].
      rewrite H1 in H4.
      destruct H4 as [wa [wb [? [? ?]]]].
      assert (wa = w4). apply H0; auto.
      apply comparable_trans with w2. apply join_comparable2 with wb; auto.
      apply comparable_trans with w. apply join_comparable with w3; auto.
      apply comparable_sym. apply join_comparable with w5; auto.
      subst wa; clear H6.
      destruct H7 as [w4' [w2' [? [? ?]]]].
      assert (w4' = w4).
        apply H0; auto.
        apply comparable_trans with wb. eapply join_comparable; eauto.
        apply comparable_sym.  eapply join_comparable; eauto.
      subst w4'; clear H7.
      assert (w2' = w2).
        eapply join_canc; try apply join_com; eauto.
      subst w2'; clear H6.
      destruct (CS _ _ _ _ _ H2 H3) as [[[[w24 w25] w34] w35] [? [? [? ?]]]].
      assert (identity w24).
        destruct (join_assoc (join_com H9) H4) as [f [? ?]].
        destruct (join_assoc (join_com H6) (join_com H11)) as [g [? ?]].
        generalize (saf_self_join (@facts _ as_alg) _ _ H13); intro.
        subst g.
        generalize (join_canc H14 (join_com H11)); intro.
        subst w25.
        eapply unit_identity; eauto.
      assert (w34=w4). eapply join_eq; [eapply identity_unit; eauto | auto ].
      subst w34.
      assert (w25 = w2). eapply join_eq; [eapply identity_unit; eauto | auto ].
      subst w25.
      clear H11 H9 H6 w24.
      destruct (join_assoc (join_com H10) (join_com H3)) as [h [? ?]].
      generalize (join_eq H6 (join_com H4)); clear H6; intro; subst h.
      destruct (join_assoc (join_com H4) (join_com H9)) as [h [? ?]].
      generalize (join_eq H6 H7); clear H6; intro; subst h.
      clear H11.
      exists wb; exists w35.
      split. apply join_com; auto.
      split; auto.
      exists w2; exists w4; split; auto.
      unfold ewand.
      exists w4; exists w3; split; auto. 
    Qed.

    Lemma wk_pry_apart {A} `{ASA A}: forall G P Q,
      wk_split -> superprecise G -> P == ewand G (G * P) ->
      (P * Q) && (G * TT) |-- (P * G * (ewand G Q)).
    Proof.
      intros until Q. intro WS; intros. 
      intros w [? ?]. unfold ewand.
      destruct H2 as [w2 [w3 [? [? Hq]]]].
      destruct H3 as [w4 [w5 [? [? _]]]].
      rewrite H1 in H4.
      destruct H4 as [wa [wb [? [? ?]]]].
      assert (wa = w4). apply H0; auto.
      apply comparable_trans with w2. eapply join_comparable2; eauto.
      apply comparable_trans with w. eapply join_comparable; eauto.
      apply comparable_sym.  eapply join_comparable; eauto.
      subst wa; clear H6. 
      destruct H7 as [w4' [w2' [? [? ?]]]].
      assert (w4' = w4). apply H0; auto.
      apply comparable_trans with wb. eapply join_comparable; eauto.
      apply comparable_sym.  eapply join_comparable; eauto.
      subst w4'; clear H7.
      assert (w2' = w2). eapply join_canc; try apply join_com; eauto.
      subst w2'; clear H6.
      assert (exists y, join w2 y w5).
        destruct (WS _ _ _ _ _ H2 H3 (join_joins (join_com H4))).
        destruct (join_assoc H6 (join_com H2)) as [y [myH1 myH2]].
        assert (y=w5) by apply (join_canc  (join_com myH2) (join_com H3)). subst y.
        exists x. apply (join_com myH1). 
      exists wb.
      destruct H6 as [y w2_y_w5].
      destruct (join_assoc w2_y_w5 (join_com H3)) as [x [myH1 myH2]]. 
      destruct (join_assoc  (join_com myH1) (join_com myH2)) as [z [myH3 myH4]].
      assert (w5=z) by apply  (join_canc (join_com H3) (join_com myH4)). subst w5.
      assert (w3=x) by apply (join_canc (join_com H2) (join_com myH2)).  subst w3.
      destruct (join_assoc myH3 (join_com myH4)) as [u [myH5 myH6]].
      assert (wb=u) by apply (join_eq H4 (join_com myH5)). subst wb.
      exists y. split. apply (join_com myH6).
      split. exists w2. exists w4. split. apply (join_com H4). split; assumption.
      exists w4. exists x; split. apply (join_com myH1). split; assumption.
    Qed.

    Lemma ewand_sepcon {A} `{HA: ASA A}: forall P Q R,
      ewand (P * Q) R == ewand P (ewand Q R).
    Proof.
      split; intros w ?.
      destruct H as [w1 [w2 [? [? ?]]]].
      destruct H0 as [w3 [w4 [? [? ?]]]].
      exists w3.
      destruct (join_assoc (join_com H0) H) as [wf [? ?]].
      exists wf.
      split; [|split]; auto.
      exists w4. exists w2. split; auto. 
      destruct H as [w1 [w2 [? [? ?]]]].
      destruct H1 as [w3 [w4 [? [? ?]]]].
      destruct (join_assoc (join_com H) (join_com H1)) as [wf [? ?]].
      exists wf. exists w4. split; [|split]; auto.
      exists w1; exists w3; split; auto.
    Qed.

    Lemma ewand_sepcon2 {A} `{HA: ASA A}: forall (CS: cross_split) R (SP: superprecise R) P (H: P == ewand R (R * P)) Q,
      ewand P (Q * R) |-- ewand P Q * R.
    Proof.
      intros.
      intros w ?.
      destruct H0 as [w1 [w34 [? [? [w3 [w4 [? [? ?]]]]]]]].
      generalize (crosssplit_wkSplit CS  _ _ _ _ _ H0 (join_com H2)); unfold wk_split; intro.
      assert (H5': joins w1 w4).
      rewrite H in H1.
      destruct H1 as [wa [wb [? [? ?]]]].
      generalize (SP _ _ H6 H4); clear H4; intro.
      assert (H4': comparable wa w4).
      apply comparable_trans with w34. apply comparable_trans with w1.
      eapply join_comparable2; eauto. eapply join_comparable; eauto.
      apply comparable_sym; eapply join_comparable; eauto.
      specialize (H4 H4').
      subst wa.
      destruct H7 as [wx [wy [? [? ?]]]].
      generalize (SP _ _ H7 H6); clear H7; intro.
      assert (H7': comparable wx w4).
      apply comparable_trans with wb.  eapply join_comparable; eauto.
      apply comparable_sym; eapply join_comparable; eauto.
      specialize (H7 H7').
      subst wx.
      generalize (join_canc (join_com H1) (join_com H4)); clear H4; intro.
      subst wy.
      econstructor; eauto.
      specialize (H5 H5').
      destruct H5 as [w5 ?].
      exists w5; exists w4; split; [|split]; auto.
      exists w1; exists w3; split; [|split]; auto.
      destruct (join_assoc H5 (join_com H0)) as [wf [? ?]].
      generalize (join_canc (join_com H7) H2); clear H7; intro.
      subst wf.
      auto.
    Qed.

    Lemma and_com {A:Type} {as_age: ageable A}: forall (x y: pred A),
      x && y == y && x.
    Proof. split; repeat intro; simpl in *; intuition. Qed.

    Lemma andp_assoc {A:Type} {as_age: ageable A}: forall (x y z: pred A),
      x && (y && z) == ((x && y) && z).
    Proof. split; repeat intro; simpl in *; intuition. Qed.

    Lemma or_com {A:Type} {as_age: ageable A}: forall (x y: pred A),
      x || y == y || x.
    Proof. split; repeat intro; simpl in *; intuition. Qed.

    Lemma or_assoc {A:Type} {as_age: ageable A}: forall (x y z: pred A),
      x || (y || z) == ((x || y) || z).
    Proof. split; repeat intro; simpl in *; intuition. Qed.


  End Lemmas.

  Module Examples.
    Open Scope pred.
    Lemma test_extend_morphism {T:Type} `{H_ASA: ASA T}: forall A B,
      A == B -> (% A == % B).
    Proof. intros; rewrite  H; reflexivity. Qed.
    Lemma test_star_morphism {T:Type} `{H_ASA: ASA T}: forall A B C D,
      A == B -> C == D -> (A * C == B * D).
    Proof. intros; rewrite H; rewrite H0; reflexivity. Qed.
    Lemma test_wand_morphism {T:Type} `{H_ASA: ASA T}: forall A B C D,
      A == B -> C == D -> (A -* C == B -* D).
    Proof. intros; rewrite H; rewrite H0; reflexivity. Qed.
  End Examples.

End predicates_sl.

Module subtypes.
  Require Import Setoid.

  Require Import msl.ageable.
  Require Import msl.subtypes.

  Import predicates_hered.

  Delimit Scope pred with pred.
  Local Open Scope pred.

  (* # *)
  Add Parametric Morphism A (as_age : ageable A): (@fash A as_age)
  with signature equiv ==> equiv
  as fash_m.
    split; repeat intro.
    rewrite<- H; apply H0; auto.
    rewrite-> H; apply H0; auto.
  Qed.

  (* ! *)
  Add Parametric Morphism A (as_age : ageable A): (@fash' A as_age)
  with signature equiv ==> equiv
  as fash'_m.
    split; repeat intro; simpl; simpl in H0.
    setoid_rewrite<- H; apply H0; auto.
    setoid_rewrite-> H; apply H0; auto.
  Qed.

  Module Lemmas.
    Require Import msl.predicates_rec.
    Import msl.predicates_hered.

    Lemma fash_fash {A} `{NA: ageable A}: forall P: pred A,
      # # P == # P.
    Proof.
      split; repeat intro; simpl in *.
      apply H with a; auto.
      unfold natLevel in H0.
      apply H; auto.
      omega.
    Qed.

    Lemma fash_and {A} `{H : ageable A}: forall (P Q:pred A),
      # (P && Q) == # P && # Q.
    Proof.
      split; repeat intro; simpl in *.
      split; intros.
      destruct (H0 y H1); auto.
      apply H0; auto.
      intuition.
    Qed.

    Lemma later_fash {A} `{NA : natty A}: 
      forall P, |> # P == # |> P.
    Proof.
      split; intros.
      apply later_fash1.
      (** backward direction **) 
      intros w ? w' ?.
      simpl in *.
      intros.
      destruct (NA y).
      apply (H x).
      apply later_nat in H0.
      apply age_level in H2. 
      omega.
      constructor 1; auto.
    Qed.

    Lemma sub_later {A} `{natty A} : forall P Q,
       |>(P >=> Q) == |>P >=> |>Q.
    Proof.
      intros.
      rewrite later_fash.
      rewrite later_impl.
      reflexivity.
    Qed.

    Lemma later_fash' {A} `{H : ageable A}: forall P,
      |> (fash' P: pred A) == fash' ( |> P).
    Proof.
      unfold fash'; intros.
      split; intros w ?; hnf in *.
      intros n' ?.
      simpl in H1. destruct (level_later H1) as [w' [? ?]].
      subst. apply H0. auto.
      intros ? ?. simpl in H1. apply H0. simpl.
      apply laterR_level in H1. rewrite laterR_nat; auto.
    Qed.

    Lemma fash_allp {A} {agA:ageable A}: forall (B: Type) (F: B -> pred A), 
      # (allp F) == allp (fun z: B => # F z).
    Proof.
      split; intros w ?.
      intro z.
      intros ? ?.
      eapply H; eauto.
      intros ? ? ?.
      eapply H; auto.
    Qed.

  End Lemmas.

  Module Examples.
    Open Scope pred.

    Lemma test_sub_morphism {T:Type} {age:ageable T}: forall A B C D,
      A == B -> C == D -> (A >=> C == B >=> D).
    Proof. intros; rewrite H; rewrite H0; reflexivity. Qed.
    Lemma test_sub_equ_morphism {T:Type} {age:ageable T}: forall A B C D,
      A == B -> C == D -> (A <=> C == B <=> D).
    Proof. intros; rewrite  H; rewrite H0; reflexivity. Qed.
  End Examples.

End subtypes.

Module pred_morphisms_all.
  Export predicates_hered.
  Export predicates_sl.
  Export subtypes.
  Export predicates_hered.Lemmas.
  Export predicates_sl.Lemmas.
End pred_morphisms_all.


