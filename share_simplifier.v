Require Import msl.msl_standard.
Require Import share_dec_base.
Require Import base_properties.
Require Import share_equation_system.
Require Import share_dec_interface.

Module Share_Simpl_Spec <: SIMPL_DOM_SPEC with Module dom := Share_Domain.
 
  Module dom := Share_Domain.
  Import Share dom.

  Definition top := top.
  Lemma bot_join : forall t, join bot t t.
  Proof with try tauto.
   intros.
   generalize (bot_correct' t0);intro.
   destruct H as [t1 H].
   generalize (bot_identity _ _ H);intro.
   subst...
  Qed.

  Lemma join_top : forall (t1 t2 : share), join top t1 t2 -> t1 = bot /\ t2 = top.
  Proof with try tauto.
   intros.
   destruct H.
   rewrite glb_commute in H.
   rewrite glb_top in H.
   rewrite lub_commute in H0.
   rewrite lub_top in H0.
   subst...
  Qed.

  Lemma join_comm: forall {a b c : share}, join a b c -> join b a c.
  Proof. intros. apply join_comm. trivial. Qed.

  Definition unit_for := fun e a => join e a a.
  Definition add := add.
  Definition sub := sub.

  Definition identity := fun (e : share) => 
   forall a b, join e a b -> a = b. 
  Lemma unit_identity: forall e b, unit_for e b -> identity e.
  Proof. intros. eapply unit_identity;eauto. Qed.
  Lemma identity_share_bot : forall s, identity s -> s = bot.
  Proof. intros. eapply identity_share_bot;eauto. Qed.
  Lemma join_canc : forall {a1 a2 b c : share}, join a1 b c -> join a2 b c -> a1 = a2.
  Proof. intros. eapply join_canc;eauto. Qed.
  Lemma sub_join : forall t1 t2 t3, sub t1 t2 = Some t3 <-> join t2 t3 t1.
  Proof. intros. eapply sub_join;eauto. Qed.
  Lemma add_join : forall t1 t2 t3, add t1 t2 = Some t3 <-> join t1 t2 t3.
  Proof. intros. eapply add_join;eauto. Qed.
  Lemma join_eq : forall x y z z', join x y z -> join x y z' -> z = z'.
  Proof. intros. eapply join_eq;eauto. Qed.
  Lemma split_identity : forall a b {c}, join a b c -> identity c -> identity a.
  Proof. intros. eapply split_identity;eauto. Qed.
  Lemma bot_identity: identity bot.
  Proof. intros. eapply bot_identity;eauto. Qed.
  Lemma join_self: forall {a b : share}, join a a b -> a = b.
  Proof. intros. eapply join_self;eauto. Qed.
  Lemma nontrivial: top <> bot.
  Proof. intros. eapply nontrivial;eauto. Qed.

End Share_Simpl_Spec.

Module Bool_Simpl_Spec <: SIMPL_DOM_SPEC with Module dom := Bool_Domain.
  Module dom := Bool_Domain.
  Import dom.
 
  Definition top := true.
  Lemma bot_join : forall t, join bot t t.
  Proof with try tauto. intros. icase t;compute... Qed.
  Lemma join_top : forall t1 t2, join top t1 t2 -> t1 = bot /\ t2 = top.
  Proof with try tauto. intros. icase t1;icase t2;compute in *;firstorder. Qed.
  Lemma join_comm: forall {a b c}, join a b c -> join b a c.
  Proof with try tauto. intros. icase a;icase b;icase c;compute in *;firstorder. Qed.
  Definition unit_for := fun e a => join e a a.
  Definition add : e -> e -> option e := fun (b1 b2 : bool) =>
   if b1 then if b2 then None else Some true else Some b2.
  Definition sub : e -> e -> option e := fun (b1 b2 : bool) =>
   if b2 then if b1 then Some false else None else Some b1.

  Definition identity := fun (e : e) => 
   forall a b, join e a b -> a = b. 
  Lemma unit_identity: forall e b, unit_for e b -> identity e.
  Proof. repeat intro. icase a;icase e0;icase b;icase b0;inv H;inv H0;firstorder. Qed. 
  Lemma identity_share_bot : forall s, identity s -> s = bot.
  Proof. intros. spec H bot top. icase s;firstorder. Qed. 
  Lemma join_canc : forall {a1 a2 b c}, join a1 b c -> join a2 b c -> a1 = a2.
  Proof. intros. icase a1;icase a2;icase b;icase c; firstorder. Qed.
  Lemma sub_join : forall t1 t2 t3, sub t1 t2 = Some t3 <-> join t2 t3 t1.
  Proof. 
   intros. icase t1;icase t2;icase t3; 
   compute in *; split;intro;disc;try inv H;disc;tauto. 
  Qed.
  Lemma add_join : forall t1 t2 t3, add t1 t2 = Some t3 <-> join t1 t2 t3.
  Proof.
   intros. icase t1;icase t2;icase t3;
   compute in *; split;intro;disc;try inv H;disc;tauto.
  Qed.
  Lemma join_eq : forall x y z z', join x y z -> join x y z' -> z = z'.
  Proof. intros. icase x;icase y;icase z;icase z';firstorder. Qed.
  Lemma split_identity : forall a b {c}, join a b c -> identity c -> identity a.
  Proof with try tauto.
   intros. icase a;icase b;inv H...
   repeat intro. icase a;icase b;inv H...
  Qed.
  Lemma bot_identity: identity bot.
  Proof with try tauto.
   repeat intro. icase a;icase b;inv H...
  Qed.
  Lemma join_self: forall {a b : e}, join a a b -> a = b.
  Proof with try tauto.
   intros. icase a;icase b; inv H...
  Qed.
  Lemma nontrivial: top <> bot.
  Proof. intro. inv H. Qed.

End Bool_Simpl_Spec.

Module Simplifier (sv : SV) (Import dom' : DOMAIN)
                  (Import es : EQUATION_SYSTEM sv with Module dom := dom') 
                  (Import spec : SIMPL_DOM_SPEC with Module dom := dom') <:
                   SIMPLIFIER sv dom' es spec.

  Module sys_features := System_Features sv es.
  Import sys_features.
  Definition valid {A B} `{evalable A B} := fun (b : B) =>
   forall (rho : A), rho |= b.
  Definition equiv_eval {A B B'} `{evalable A B} `{evalable A B'} := 
   fun (b : B) (b' : B') => forall rho, rho |= b <-> rho |= b'.
  Lemma equiv_refl {A B} `{evalable A B}: forall (b : B),
    equiv_eval b b.
  Proof.
    repeat intro. tauto.
  Qed.

  Definition substitution : Type :=
    {p : (var * object)%type | snd p <> Vobject (fst p)}.
  Definition sbst_var (sbst : substitution) : var := fst (projT1 sbst).
  Definition sbst_object (sbst : substitution) : object := snd (projT1 sbst).
  Program Definition mkCsubstitution (x : var) (sh : s) : substitution :=
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
  Qed.

  Definition eval_substitution (ctx : context) (subst : substitution) : Prop :=
    match subst with exist (x, fp) pf => ctx x = get ctx fp end.
  Instance evalable_substitution : evalable context substitution :=
    Evalable eval_substitution.
  Definition vars_subst (subst : substitution) : list var :=
   (sbst_var subst) :: (vars (sbst_object subst)).
  Instance varsable_subst : varsable substitution var :=
   Varsable vars_subst.

  Class substable (A : Type) (B : Type) : Type := Substable 
   {subst: substitution -> A -> B}.
  Implicit Arguments Substable [A B].

  Definition subst_object (sbst : substitution) (fp' : object) : object :=
    match sbst, fp' with
     | _, Cobject c => Cobject c
     | exist (x, fp) _, Vobject v => if eq_dec x v then fp else Vobject v
    end.
  Instance substable_object : substable object object :=
   Substable subst_object.

  Lemma subst_object_id: forall sbst,
    subst sbst (sbst_object sbst) = (sbst_object sbst).
  Proof.
    destruct sbst; auto. simpl. destruct x. unfold sbst_object. simpl. 
    destruct o; auto. case (eq_dec v v0); auto.
  Qed.

  Definition upd_subst (ctx : context) (sbst : substitution) : context :=
    upd ctx (sbst_var sbst) (get ctx (sbst_object sbst)).
   
  Lemma subst_object_upd: forall sbst fp' ctx,
    get ctx (subst sbst fp') = get (upd_subst ctx sbst) fp'.
  Proof with try tauto.
    intros. destruct sbst. simpl. destruct x. destruct fp'; auto.
    unfold upd_subst, upd, sbst_var. simpl. case (eq_dec v v0); simpl...
  Qed.

  Lemma subst_object_vars: forall sbst fp' fp'',
    (sbst_object sbst <> Vobject (sbst_var sbst)) ->
    subst sbst fp' = fp'' ->
    (forall x', In x' (vars fp'') -> 
       In x' ((vars sbst) ++ (vars fp'))) /\
       ~In (sbst_var sbst) (vars fp'').
  Proof.
    repeat intro. destruct sbst. destruct x.
    icase fp'; icase fp''; unfold fst,snd in n; simpl in *.
    Focus 2.  split. intros. contradiction H1. auto.
    Focus 2. split. intros. contradiction H1. auto.
    split. intros. destruct H1. Focus 2. contradiction H1.
    subst. destruct (eq_dec v v0);subst. right. simpl. left;trivial.
    injection H0; intro;subst. right. apply in_app_iff;right. apply in_eq.
    destruct (eq_dec v v0). 
    subst. unfold sbst_object,sbst_var in *. simpl in *.
    apply neg_false. split. intros. destruct H0;trivial.
    Focus 2. auto. subst. Focus 2.
    injection H0; intro;subst.
    revert H. unfold sbst_object,sbst_var. simpl. intro.
    apply neg_false. split;auto. intro. destruct H1;subst. 
    auto. trivial.
    contradiction H. trivial.
  Qed.

(* HERE Have to do subst_subst... *)

  Definition subst_substitution (sbst sbst' : substitution) : result substitution unit :=
    match sbst, sbst' with
      exist (x, o) _, exist (x', o') _ =>
        if eq_dec x x' then
          match o, o' with
           | Cobject c1, Cobject c2 => if eq_dec c1 c2 then Simpler tt else Absurd
           | Cobject c1, Vobject v2 => Same (mkCsubstitution v2 c1)
           | Vobject v1, Cobject c2 => Same (mkCsubstitution v1 c2)
           | Vobject v1, Vobject v2 =>
             match eq_dec v1 v2 with
              | left _ => Simpler tt
              | right pf => Same (mkVsubstitution v1 v2 pf)
             end
          end
        else match subst sbst o' with
          | Cobject c2' => Same (mkCsubstitution x' c2')
          | Vobject v2' => 
            match eq_dec x' v2' with
             | left _ => Simpler tt
             | right pf => Same (mkVsubstitution x' v2' pf)
            end
        end
    end.
 Instance substable_substitution : substable substitution (result substitution unit) :=
  Substable subst_substitution.

  Lemma subst_substitution_equiv: forall sbst sbst' sbst'',
    subst sbst sbst' = Same sbst'' ->
      (forall ctx, eval ctx sbst'' <-> eval (upd_subst ctx sbst) sbst') /\
      (forall x, In x (vars sbst'') -> In x ((vars (sbst_object sbst)) ++ (vars sbst'))) /\
      ~In (sbst_var sbst) (vars sbst'').
  Proof with try tauto.
    intros.
    icase sbst. icase sbst'. icase sbst''. icase x. icase x0. icase x1. unfold upd_subst, sbst_var in *. simpl in *.
    revert H.
    case (eq_dec v v0); simpl. destruct o; destruct o0; simpl.
    case (eq_dec v2 v3); disc; intros. inv H. simpl. split; intros.
    rewrite upd_eq. split; intros.
    rewrite H. rewrite upd_eq'. trivial.
    rewrite upd_neq in H; auto.
    intro. apply n0. rewrite H0. trivial.
    split; intros. tauto.
    intro. icase H. apply n. inv H...
    icase H. congr.
    intros. inv H. simpl.
    split; intros. rewrite upd_eq. split; trivial.
    split; intros. icase H.
    intro. icase H. unfold sbst_var in *;simpl in *. congr.
    intros. inv H. simpl.
    split; intros. rewrite upd_eq.
    split; intro. rewrite <- H. rewrite upd_eq'. trivial.
    rewrite H. rewrite upd_neq; trivial. congr.
    split; intros. icase H. intro. icase H. unfold sbst_var in *;simpl in *. congr.
    case (eq_dec s0 s1); disc.
    icase o0. case (eq_dec v v2).
    icase o. case (eq_dec v0 v3); disc. simpl. intros.
    inv H. split; intros.
    rewrite upd_eq.
    rewrite upd_neq; auto. tauto.
    split; intros. icase H. simpl in H. icase H. simpl.
    intro. icase H; congr. icase H; congr.
    simpl. intros. inv H.
    split; intros. rewrite upd_eq. rewrite upd_neq; auto. tauto.
    split; intros. icase H. intro. icase H.
    case (eq_dec v0 v2); disc. simpl. intros.
    inv H. unfold sbst_object. simpl.
    split; intros. rewrite upd_neq; auto. rewrite upd_neq; auto. tauto.
    split; intros. icase o. simpl. tauto.
    intro. icase H. icase H.
    unfold sbst_object. simpl.
    split; intros. inv H. rewrite upd_neq; auto. tauto.
    inv H. simpl. split; intros. icase o. icase H. simpl. tauto.
    intro. icase H.
  Qed.

  Lemma subst_substitution_valid: forall sbst sbst',
    subst sbst sbst' = Simpler tt ->
    forall ctx, (upd_subst ctx sbst) |= sbst'.
  Proof.
    intros.
    icase sbst. icase sbst'. icase x. icase x0. unfold subst_substitution, upd_subst, sbst_var in *. simpl in *.
    revert H. case (eq_dec v v0); disc. icase o. icase o0. case (eq_dec v1 v2); disc. simpl. intros. subst.
    rewrite upd_eq. rewrite upd_eq'. trivial.
    icase o0. case (eq_dec s0 s1); disc. simpl. intros. subst. rewrite upd_eq. trivial.
    icase o0. case (eq_dec v v1). icase o. case (eq_dec v0 v2); disc. simpl. intros. subst. rewrite upd_eq, upd_eq'. trivial.
    case (eq_dec v0 v1); disc. simpl. intros. subst. unfold sbst_object. simpl. trivial.
  Qed.

  Lemma subst_substitution_unsat: forall sbst sbst',
    subst_substitution sbst sbst' = Absurd ->
    forall ctx, ~eval (upd_subst ctx sbst) sbst'.
  Proof.
    intros.
    icase sbst. icase sbst'. icase x. icase x0. unfold subst_substitution, upd_subst, sbst_var in *. simpl in *.
    revert H. case (eq_dec v v0); disc. icase o. icase o0. case (eq_dec v1 v2); disc.
    icase o0. case (eq_dec s0 s1); disc. intros. subst. unfold sbst_object. simpl. rewrite upd_eq. congr.
    icase o0. case (eq_dec v v1). icase o. case (eq_dec v0 v2); disc.
    case (eq_dec v0 v1); disc.
  Qed.

  (* removes annoying _ *)
  Implicit Arguments inl [A B].
  Implicit Arguments inr [A B].

  Definition simpl_equation (eqn : equation) : 
    result equation (unit + (substitution + (substitution * substitution))) :=
    match eqn with 
      (* 3 constants *)
      | (Cobject c1, Cobject c2, Cobject c3) => 
         match add c1 c2 with 
          | None => Absurd 
          | Some c3' => if eq_dec c3 c3' then Simpler (inl tt) else Absurd
(* A bug! | Some c3' => if eq_dec c3 c3' then Absurd else Simpler (inl tt) *)
         end
      (* 2 constants, 3 cases, can always simplify *)
      | (Cobject c1, Cobject c2, Vobject v3) =>
         match add c1 c2 with
          | None => Absurd
          | Some c3 => Simpler (inr (inl (mkCsubstitution v3 c3)))
         end
      | (Cobject c1, Vobject v2, Cobject c3) =>
         match 
 sub c3 c1 with
          | None => Absurd
          | Some c2 => Simpler (inr (inl (mkCsubstitution v2 c2)))
         end
      | (Vobject v1, Cobject c2, Cobject c3) =>
         match sub c3 c2 with
          | None => Absurd
          | Some c1 => Simpler (inr (inl (mkCsubstitution v1 c1)))
         end
      (* 1 constant, can simplify in a few special cases *)
      | (Cobject c1, Vobject v2, Vobject v3) =>
         if eq_dec c1 bot then 
           match eq_dec v2 v3 with
            | left _ => Simpler (inl tt)
            | right pf => Simpler (inr (inl (mkVsubstitution v2 v3 pf)))
           end
(*           if eq_dec v2 v3 then Simpler (inl tt) else Simpler (inr (inl (v2, Vobject v3))) *)
         else if eq_dec c1 top then
           Simpler (inr (inr ((mkCsubstitution v2 bot), (mkCsubstitution v3 top))))
         else Same eqn
      | (Vobject v1, Cobject c2, Vobject v3) =>
         if eq_dec c2 bot then 
           match eq_dec v1 v3 with
            | left _ => Simpler (inl tt)
            | right pf => Simpler (inr (inl (mkVsubstitution v1 v3 pf)))
           end
(*           if eq_dec v1 v3 then Simpler (inl tt) else Simpler (inr (inl (v1, Vobject v3))) *)
         else if eq_dec c2 top then
           Simpler (inr (inr ((mkCsubstitution v1 bot), (mkCsubstitution v3 top))))
         else Same eqn
      | (Vobject v1, Vobject v2, Cobject c3) =>
         if eq_dec c3 bot then
           if eq_dec v1 v2 then Simpler (inr (inl (mkCsubstitution v1 bot)))
           else Simpler (inr (inr ((mkCsubstitution v1 bot), (mkCsubstitution v2 bot))))
         else if eq_dec v1 v2 then
           Absurd (* v1 = v2 but c3 <> bot *)
         else Same eqn
      (* no constants, can simplify in a few special cases *)
      | (Vobject v1, Vobject v2, Vobject v3) =>
        if eq_dec v1 v3 then
          Simpler (inr (inl (mkCsubstitution v2 bot)))
        else if eq_dec v2 v3 then
          Simpler (inr (inl (mkCsubstitution v1 bot)))
        else if eq_dec v1 v2 then
          Simpler (inr (inr ((mkCsubstitution v1 bot), (mkCsubstitution v3 bot))))
        else
          Same eqn
  end.

  Lemma simpl_equation_equiv: forall eqn eqn',
    simpl_equation eqn = Same eqn' -> 
    equiv_eval eqn eqn' /\
    forall x, In x (vars eqn') -> In x (vars eqn).
  Proof with try (split; try apply equiv_refl; auto).
    intros [[fp1 fp2] fp3] [[fp4 fp5] fp6] ?.
    icase fp1; icase fp2; icase fp3; simpl in H; revert H.
    case (eq_dec v v1). intros; disc.
    case (eq_dec v0 v1). intros; disc.
    case (eq_dec v v0); intros; disc.
    inv H...
    case (eq_dec s0 bot).
    case (eq_dec v v0); disc.
    case (eq_dec v v0); intros; disc.
    inv H... 
    case (eq_dec s0 bot). case (eq_dec v v0); intros; disc.
    case (eq_dec s0 top); intros; disc.
    inv H...
    case (sub s1 s0); intros; disc.
    case (eq_dec s0 bot). case (eq_dec v v0); intros; disc.
    case (eq_dec s0 top); intros; disc.
    inv H...
    case (sub s1 s0); intros; disc.
    case (add s0 s1); intros; disc.
    case (add s0 s1); intro; disc.
    case (eq_dec s2 e0); intros; disc.
  Qed.

  Lemma simpl_equation_reduce1: forall eqn eq,
    simpl_equation eqn = Simpler (inr (inl eq)) ->
      (forall ctx, eval ctx eqn <-> eval ctx eq) /\
      (forall x, In x (vars eq) -> In x (vars eqn)).
  Proof with try tauto.
    intros [[fp1 fp2] fp3] [fp4 fp5] ?.
    icase fp1; icase fp2; icase fp3; simpl in H; revert H.
    case (eq_dec v v1). intros.
    inv H. simpl. split.
    split; intro.
    apply join_comm in H. apply unit_identity in H.
    apply identity_share_bot in H. trivial.
    rewrite H. apply join_comm. apply bot_join.
    intros. destruct H; contr; auto.
    case (eq_dec v0 v1). intros.
    inv H. simpl. split.
    split; intro.
    apply unit_identity in H. apply identity_share_bot in H. trivial.
    rewrite H. apply bot_join.
    intros. destruct H; contr; auto.
    case (eq_dec v v0); disc.
    case (eq_dec s0 bot); disc.
    case (eq_dec v v0); disc.
    intros. inv H. simpl. split.
    split; intro.
    generalize (split_identity _ _ H bot_identity); intro.
    apply identity_share_bot in H0. trivial.
    rewrite H. apply bot_join.
    intros. destruct H; contr; auto.
    case (eq_dec s0 bot).
    case (eq_dec v v0); disc; intros.
    case (eq_dec v v0); disc; intros.
    case (eq_dec s0 bot).
    case (eq_dec v v0); disc; intros.
    inv H. simpl. split.
    split; intro.
    apply (bot_identity _ _ (join_comm H)).
    rewrite H. apply join_comm. apply bot_join.
    intros. destruct H; contr; auto.
    case (eq_dec s0 top); disc.
    case_eq (sub s1 s0); disc; intros.
    inv H0. simpl. split; auto.
    apply sub_join in H.
    split; intro.
    generalize (join_canc (join_comm H) H0). auto.
    subst e0. apply join_comm...
    case (eq_dec s0 bot). case (eq_dec v v0); disc; intros.
    inv H. simpl. split.
    split; intro.
    apply (bot_identity _ _ H).
    rewrite H. apply bot_join.
    intros. destruct H; auto.
    case (eq_dec s0 top); disc.
    case_eq (sub s1 s0); disc; intros.
    inv H0. simpl. split; auto.
    apply sub_join in H.
    split; intro. 
    apply (@join_canc (ctx v) e0 s0 s1). 
    apply join_comm;trivial.
    apply join_comm;trivial.
    subst; auto.
    case_eq (add s0 s1); disc; intros.
    inv H0. simpl. split; auto.
    apply add_join in H.
    split; intro.
    eapply join_eq; eauto.
    subst; eauto.
    case_eq (add s0 s1); disc; intro.
    case (eq_dec s2 e0); disc.
  Qed.

  Lemma simpl_equation_reduce2: forall eqn eq1 eq2,
    simpl_equation eqn = Simpler (inr (inr (eq1, eq2))) ->
      (forall ctx, eval ctx eqn <-> eval ctx eq1 /\ eval ctx eq2) /\
      (forall x, In x ((vars eq1) ++ (vars eq2)) -> In x (vars eqn)).
  Proof.
    intros [[fp1 fp2] fp3] [fp4 fp5] [fp6 fp7] ?.
    icase fp1; icase fp2; icase fp3; simpl in H; revert H.
    case (eq_dec v v1); disc.
    case (eq_dec v0 v1); disc.
    case (eq_dec v v0); disc.
    intros. subst v0. inv H. simpl. split; [| firstorder].
    split; intro.
    generalize (join_self H); intro.
    rewrite <- H0 in *.
    apply unit_identity in H. apply identity_share_bot in H. tauto.
    destruct H. rewrite H, H0. apply bot_join.
    case (eq_dec s0 bot); disc.
    case (eq_dec v v0); disc.
    intros.
    inv H. simpl. split; [| firstorder].
    split; intro.
    generalize (split_identity _ _ H bot_identity); intro.
    generalize (split_identity _ _ (join_comm H) bot_identity); intro.
    split; apply identity_share_bot; trivial.
    destruct H. rewrite H, H0. apply bot_join.
    case (eq_dec v v0); disc.
    case (eq_dec v v0); disc.
    case (eq_dec s0 bot); disc.
    case (eq_dec s0 top); disc; intros.
    inv H; simpl. split; [| firstorder].
    split; intro.
    apply join_comm, join_top in H. trivial.
    destruct H.
    rewrite H0 in H. apply nontrivial in H; contr.
    case (eq_dec s0 bot); disc.
    case (eq_dec s0 top); disc; intros.
    inv H. simpl. split; [| firstorder].
    split; intro.
    apply join_comm, join_top in H; trivial.
    destruct H.
    rewrite H, H0. apply bot_join.
    case (sub s1 s0); disc.
    case (eq_dec s0 bot). case (eq_dec v v0); disc. case (eq_dec s0 top); disc; intros.
    inv H. simpl. split; [| firstorder].
    split; intro.
    apply join_top in H; trivial.
    destruct H; rewrite H, H0. apply join_comm. apply bot_join.
    case (sub s1 s0); disc.
    case (add s0 s1); disc.
    case (add s0 s1); disc; intro.
    case (eq_dec s2 e0); disc.
  Qed.

  Lemma simpl_equation_valid: forall eqn,
    simpl_equation eqn = Simpler (inl tt) ->
    valid eqn.
  Proof.
    intros [[fp1 fp2] fp3] ?.
    icase fp1; icase fp2; icase fp3; simpl in H; revert H.
    case (eq_dec v v1); disc. case (eq_dec v0 v1); disc. case (eq_dec v v0); disc.
    case (eq_dec s0 bot); disc. case (eq_dec v v0); disc. case (eq_dec v v0); disc.
    case (eq_dec s0 bot).
    case (eq_dec v v0); disc; intros.
    subst. simpl. intro. apply join_comm. apply bot_join.
    case (eq_dec s0 top); disc.
    case (sub s1 s0); disc.
    case (eq_dec s0 bot).
    case (eq_dec v v0); disc; intros.
    subst. simpl. intro. apply bot_join.
    case (eq_dec s0 top); disc.
    case (sub s1 s0); disc.
    case (add s0 s1); disc.
    case_eq (add s0 s1); disc; intro.
    case (eq_dec s2 e0); disc ; intros.
    subst s2.
    apply add_join in H. simpl. intro. trivial.
  Qed.

  Lemma simpl_equation_unsat: forall eqn,
    simpl_equation eqn = Absurd ->
    ~(exists rho, rho|= eqn).
  Proof.
    intros [[fp1 fp2] fp3] ?.
    icase fp1; icase fp2; icase fp3; simpl in H; revert H.
    case (eq_dec v v1); disc. case (eq_dec v0 v1); disc. case (eq_dec v v0); disc.
    case (eq_dec s0 bot); disc. case (eq_dec v v0); disc.
    case (eq_dec v v0); disc; intros.
    intro. destruct H0. subst v0. simpl in H0.
    generalize (join_self H0). intro. rewrite H1 in H0.
    apply unit_identity in H0. apply identity_share_bot in H0. contr.
    case (eq_dec s0 bot).
    case (eq_dec v v0); disc.
    case_eq (eq_dec s0 top); disc.
    case_eq (sub s1 s0); disc; intros.
    intro. destruct H1. simpl in H1.
    apply join_comm in H1.
    apply sub_join in H1. rewrite H in H1; disc.
    case (eq_dec s0 bot). case (eq_dec v v0); disc. case (eq_dec s0 top); disc.
    case_eq (sub s1 s0); disc; intros.
    intros [? ?]. simpl in H1.
    rewrite <- sub_join in H1. rewrite H in H1; disc.
    case_eq (add s0 s1); disc; intros.
    intros [? ?]. simpl in H1.
    rewrite <- add_join in H1. rewrite H in H1; disc.
    case_eq (add s0 s1); intro.
    case (eq_dec s2 e0); disc; intros.
    intros [? ?]. simpl in H1.
    rewrite <- add_join in H1. rewrite H in H1. inv H1. apply n; trivial.
    intros ? [? ?]. simpl in H1.
    rewrite <- add_join in H1. rewrite H in H1. inv H1.
  Qed.

  Definition subst_equation (sbst : substitution) (eqn : equation) :
    result equation (unit + (substitution + (substitution * substitution))) :=
    match eqn with (fp1, fp2, fp3) => 
     simpl_equation (subst sbst fp1, subst sbst fp2, subst sbst fp3) 
    end.
  Instance substable_equation : substable equation (result equation (unit + (substitution + (substitution * substitution)))):=
   Substable subst_equation.

  Lemma subst_equation_equiv: forall sbst eqn eqn',
    subst sbst eqn = Same eqn' ->
      (forall ctx, eval ctx eqn' <-> eval (upd_subst ctx sbst) eqn) /\
      (forall x', In x' (vars eqn') -> In x' ((vars (sbst_object sbst)) ++ (vars eqn))) /\
      ~In (sbst_var sbst) (vars eqn').
  Proof.
    intros.
    change subst with subst_equation in *.
    unfold subst_equation in H.
    change subst with subst_object in *. 
    destruct eqn as [[? ?] ].
    destruct sbst. destruct x.
    apply simpl_equation_equiv in H.
    destruct H. split.
    intro ctx. spec H ctx.
    rewrite <- H. unfold eval,eval_equation.
    do 3 rewrite <- subst_object_upd. tauto.
    remember (subst_object (exist _ (v, o2) n) o). symmetry in Heqo3.
    apply subst_object_vars in Heqo3. destruct Heqo3.
    remember (subst_object (exist _ (v, o2) n) o0). symmetry in Heqo4.
    apply subst_object_vars in Heqo4. destruct Heqo4.
    remember (subst_object (exist _ (v, o2) n) o1). symmetry in Heqo5.
    apply subst_object_vars in Heqo5. destruct Heqo5.
    unfold sbst_var in *. simpl in *.
    split.
    intros. spec H0 x' H7.
    apply in_app_or in H0. destruct H0.
    spec H1 x' H0. rewrite app_assoc.
    apply in_or_app. icase H1. subst x'. contr.
    apply in_app_or in H0. destruct H0.
    spec H3 x' H0.
    apply in_or_app. destruct H3. subst x'. contr.
    apply in_app_or in H3. destruct H3; auto. right. apply in_or_app. 
    right. apply in_or_app; auto.
    spec H5 x' H0. destruct H5. subst x'. contr.
    apply in_or_app. apply in_app_or in H5. destruct H5; auto.
    right.
    apply in_or_app. right. apply in_or_app; auto.
    intro.
    spec H0 v H7.
    apply in_app_or in H0. icase H0.
    apply in_app_or in H0. icase H0.
    trivial. trivial. trivial.
  Qed.

  Lemma subst_equation_reduce1: forall sbst eqn eq1,
    subst sbst eqn = Simpler (inr (inl eq1)) ->
      (forall ctx, eval ctx eq1 <-> eval (upd_subst ctx sbst) eqn) /\
      (forall x', In x' (vars eq1) -> In x' ((vars (sbst_object sbst)) ++ (vars eqn))) /\
      ~In (sbst_var sbst) (vars eq1).
  Proof.
    intros.
    change subst with subst_equation in *.
    unfold subst_equation in H.
    change subst with subst_object in *. 
    destruct sbst as [[? ?] ?]. destruct eqn as [[? ?] ?].
    apply simpl_equation_reduce1 in H. destruct H. split.
    intro ctx. spec H ctx.
    rewrite <- H. unfold eval,eval_equation.
    do 3 rewrite <- subst_object_upd. tauto.
    remember (subst_object (exist _ (v, o) n) o0). symmetry in Heqo3.
    apply subst_object_vars in Heqo3. destruct Heqo3.
    remember (subst_object (exist _ (v, o) n) o1). symmetry in Heqo4.
    apply subst_object_vars in Heqo4. destruct Heqo4.
    remember (subst_object (exist _ (v, o) n) o2). symmetry in Heqo5.
    apply subst_object_vars in Heqo5. destruct Heqo5.
    unfold sbst_var in *. simpl in *.
    split. intros.
    spec H0 x' H7.
    apply in_app_or in H0. destruct H0.
    spec H1 x' H0. destruct H1. subst x'. contr.
    rewrite app_assoc. apply in_or_app; auto.
    apply in_app_or in H0. destruct H0.
    spec H3 x' H0. destruct H3. subst x'. contr.
    apply in_app_or in H3. apply in_or_app; destruct H3; auto.
    right. apply in_or_app. right. apply in_or_app; auto.
    spec H5 x' H0. destruct H5. subst x'. contr.
    apply in_app_or in H5. apply in_or_app; destruct H5; auto.
    right. apply in_or_app. right. apply in_or_app; auto.
    intro.
    spec H0 v H7.
    apply in_app_or in H0. destruct H0. contr.
    apply in_app_or in H0; firstorder. 
    trivial. trivial. trivial.
  Qed.

  Lemma subst_equation_reduce2: forall sbst eqn sbst' sbst'',
    subst sbst eqn = Simpler (inr (inr (sbst', sbst''))) ->
      (forall ctx, eval ctx sbst' /\ eval ctx sbst'' <-> 
                   eval (upd_subst ctx sbst) eqn) /\
      (forall x', In x' ((vars sbst') ++ (vars sbst'')) -> 
                  In x' ((vars (sbst_object sbst)) ++ (vars eqn))) /\
      ~In (sbst_var sbst) ((vars sbst') ++ (vars sbst'')).
  Proof.
    intros.
    change subst with subst_equation in *.
    unfold subst_equation in H.
    change subst with subst_object in *. 
    destruct sbst as [[? ?] ?]. destruct eqn as [[? ?] ?].
    apply simpl_equation_reduce2 in H. destruct H. split.
    intro ctx. spec H ctx.
    rewrite <- H. unfold eval,eval_equation.
    do 3 rewrite <- subst_object_upd. tauto.
    remember (subst_object (exist _ (v, o) n) o0). symmetry in Heqo3.
    apply subst_object_vars in Heqo3. destruct Heqo3.
    remember (subst_object (exist _ (v, o) n) o1). symmetry in Heqo4.
    apply subst_object_vars in Heqo4. destruct Heqo4.
    remember (subst_object (exist _ (v, o) n) o2). symmetry in Heqo5.
    apply subst_object_vars in Heqo5. destruct Heqo5.
    unfold sbst_var in *. simpl in *.
    split. intros.
    spec H0 x' H7.
    apply in_app_or in H0. destruct H0.
    spec H1 x' H0. destruct H1. subst x'; contr.
    rewrite app_assoc. apply in_or_app; auto.
    apply in_app_or in H0. destruct H0.
    spec H3 x' H0. destruct H3. subst x'; contr.
    apply in_app_or in H3. apply in_or_app.
    destruct H3; auto. right. apply in_or_app. right. apply in_or_app; auto.
    spec H5 x' H0. destruct H5. subst x'. contr.
    apply in_app_or in H5. apply in_or_app.
    destruct H5; auto. right. apply in_or_app. right. apply in_or_app; auto.
    intro.
    spec H0 v H7.
    apply in_app_or in H0. destruct H0; contr.
    apply in_app_or in H0. destruct H0; contr.
    trivial. trivial. trivial.
  Qed.

  Lemma subst_equation_valid: forall sbst eqn,
    subst sbst eqn = Simpler (inl tt) ->
    forall ctx, (upd_subst ctx sbst) |= eqn.
  Proof.
    intros.
    change subst with subst_equation in *.
    unfold subst_equation in H.
    change subst with subst_object in *. 
    destruct eqn as [[? ?] ].
    apply simpl_equation_valid in H. spec H ctx.
    unfold eval,eval_equation in *. do 3 rewrite <- subst_object_upd. trivial. 
  Qed.

  Lemma subst_equation_unsat: forall sbst eqn,
    subst sbst eqn = Absurd ->
    forall ctx, ~ (upd_subst ctx sbst) |= eqn.
  Proof.
    intros.
    change subst with subst_equation in *.
    unfold subst_equation in H.
    change subst with subst_object in *. 
    destruct eqn as [[? ?] ?].
    apply simpl_equation_unsat in H.
    intro. apply H. exists ctx.
    unfold eval,eval_equation in *. do 3 rewrite <- subst_object_upd in H0. trivial.
  Qed.
  
  Fixpoint subst_substitution_list (sbst : substitution) (sbst_list : list substitution) : option (list substitution) :=
    match sbst_list with
     | nil => Some nil
     | sbst1::sbst_list' => 
       match subst sbst sbst1 with
        | Absurd => None
        | Simpler tt => subst_substitution_list sbst sbst_list'
        | Same sbst1' => 
          match subst_substitution_list sbst sbst_list' with
           | None => None
           | Some sbst_list'' => Some (sbst1'::sbst_list'')
          end
       end
    end.
  Instance substab_substitution_list : substable (list substitution) (option (list substitution))  :=
    Substable subst_substitution_list.

  Lemma subst_substitution_list_Some: forall sbst sbst_list sbst_list',
    subst sbst sbst_list = Some sbst_list' ->
    (forall ctx, 
      eval (upd_subst ctx sbst) sbst_list <->  
      eval ctx sbst_list') /\
    (forall x', In x' (vars sbst_list') -> 
      In x' ((vars (sbst_object sbst)) ++ (vars sbst_list))) /\
    ~In (sbst_var sbst) (vars sbst_list').
  Proof with try tauto.
    induction sbst_list; repeat intro; simpl in *.
    inv H. simpl. split. intro. tauto. tauto. (* rewrite <- subst_object_upd. rewrite subst_object_id. rewrite upd_context_eq. tauto. tauto. *)
    revert H. case_eq (subst_substitution sbst a); intros; disc.
    destruct u. spec IHsbst_list sbst_list' H0. destruct IHsbst_list. split. intro ctx. spec H1 ctx.
    rewrite <- H1. firstorder; eapply subst_substitution_valid; eauto.
    destruct H2. split; auto. intros. spec H2 x' H4.
    apply in_app_or in H2. apply in_or_app. destruct H2; auto. right. simpl. rewrite in_app_iff; auto.
    revert H0. case_eq (subst_substitution_list sbst sbst_list); disc; intros.
    apply subst_substitution_equiv in H. destruct H. 
    inv H1. simpl. spec IHsbst_list l H0. destruct IHsbst_list.
    split. intro ctx. rewrite H. rewrite <- H1. firstorder.
    destruct H3. split. intros. 
    assert (In x' ((vars s0)++(vars l))) by (simpl;tauto).
    rewrite in_app_iff in H6. destruct H6.
    destruct H2. spec H2 x' H6. simpl. simpl in *. repeat rewrite in_app_iff in *.
    simpl in *. rewrite in_app_iff...
    spec H3 x' H6. simpl in *. repeat rewrite in_app_iff in *.
    simpl in *. rewrite in_app_iff...
    destruct H2. intro. simpl in *. rewrite in_app_iff in *...
  Qed.

  Lemma subst_substitution_list_None: forall sbst sbst_list,
    subst sbst sbst_list = None ->
    forall ctx, ~eval (upd_subst ctx sbst) sbst_list.
  Proof.
    induction sbst_list. intros. inv H.
    simpl. case_eq (subst_substitution sbst a); disc; intro.
    repeat intro.
    apply subst_substitution_unsat with (ctx := ctx) in H. tauto.
    destruct u. repeat intro. destruct H1.
    eapply IHsbst_list; eauto.
    case_eq (subst_substitution sbst a); disc.
    case_eq (subst_substitution_list sbst sbst_list); disc.
    repeat intro. inv H1. destruct H3.
    eapply IHsbst_list; eauto.
  Qed.

  Lemma subst_substitution_list_length: forall sbst sbst_list sbst_list',
    subst sbst sbst_list = Some sbst_list' -> length sbst_list >= length sbst_list'.
  Proof.
    induction sbst_list; simpl; intros. 
    inv H; auto.
    revert H; case_eq (subst_substitution sbst a); disc; intro.
    destruct u; intros.
    spec IHsbst_list sbst_list' H0. omega.
    case_eq (subst_substitution_list sbst sbst_list); disc; intros.
    inv H1.
    spec IHsbst_list l H. simpl. omega.
  Qed.
   
(* simpl is just subst with x => x, but that adds extra eq_dec comparisons, and actually
      makes some of the proofs harder... so we write another, which is unfortunately a bit
      too close to subst_equation_list, but that's life... *)
  Fixpoint simpl_equation_list (eqn_list : list equation) : option (list substitution * list equation) :=
    match eqn_list with 
     | nil => Some (nil, nil)
     | eqn :: eqn_list' => 
       match simpl_equation eqn with
        | Absurd => None
        | Same eqn' => 
          match simpl_equation_list eqn_list' with
           | None => None
           | Some (eql, eqnl) => Some (eql, eqn' :: eqnl)
          end
        | Simpler (inl tt) => simpl_equation_list eqn_list'
        | Simpler (inr (inl eq1)) => 
          match simpl_equation_list eqn_list' with
           | None => None
           | Some (eql, eqnl) => Some (eq1 :: eql, eqnl)
          end
        | Simpler (inr (inr (eq1, eq2))) => 
          match simpl_equation_list eqn_list' with
           | None => None
           | Some (eql, eqnl) => Some (eq1 :: eq2 :: eql, eqnl)
          end
       end
    end.

  Lemma simpl_equation_list_Some: forall eqnL sbstL' eqnL',
    simpl_equation_list eqnL = Some (sbstL', eqnL') ->
    (forall ctx, eval ctx eqnL <->  eval ctx sbstL' /\ eval ctx eqnL') /\
    (forall x, In x ((vars sbstL') ++ (vars eqnL')) ->  In x (vars eqnL)).
  Proof with try tauto.
    induction eqnL; simpl; intros.
    inv H. compute...
    revert H. simpl in IHeqnL. case_eq (simpl_equation_list eqnL); intros.
    2: icase (simpl_equation a); icase s0; [icase u | icase s0]; icase p.
    destruct p. generalize (IHeqnL _ _ H); clear IHeqnL H; intros [IH1 IH2].
    revert H0. case_eq (simpl_equation a); disc; intros.
    destruct s0. destruct u.
    inv H0. apply simpl_equation_valid in H. split; intros.
    rewrite <- IH1. firstorder. apply in_or_app. auto.
    destruct s0. inv H0. apply simpl_equation_reduce1 in H. destruct H.
    simpl. split; intros.
    rewrite IH1. firstorder.
    icase a;icase p.
    assert (In x ((vars s0)++((vars l)++(vars eqnL')))). simpl;repeat rewrite in_app_iff in *...
    rewrite in_app_iff.
    rewrite in_app_iff in H2. destruct H2. apply H0 in H2;simpl in *...
    apply IH2 in H2...
    destruct p. inv H0. simpl. apply simpl_equation_reduce2 in H. destruct H.
    split; intros.
    rewrite IH1. firstorder.
    icase a;icase p.
    assert (In x (((vars s0)++(vars s1))++((vars l)++(vars eqnL')))). simpl;repeat rewrite in_app_iff in *...
    simpl in *;repeat rewrite in_app_iff in *...
    rewrite in_app_iff in H2.
    rewrite in_app_iff.
    destruct H2. apply H0 in H2;simpl in *...
    apply IH2 in H2...
    inv H0. apply simpl_equation_equiv in H. destruct H. simpl.
    split; intros. rewrite IH1. spec H ctx. rewrite H. tauto.
    apply in_or_app. apply in_app_or in H1. destruct H1.
    right. apply IH2. apply in_or_app; auto.
    apply in_app_or in H1. destruct H1; auto. right. apply IH2. apply in_or_app; auto.
  Qed.

  Lemma simpl_equation_list_None: forall eqnL,
    simpl_equation_list eqnL = None -> ~(exists rho, rho |= eqnL).
  Proof.
    induction eqnL; repeat intro.
    simpl in H. disc.
    destruct H0. simpl in *.
    revert H. case_eq (simpl_equation a); intros.
    destruct H0.
    apply simpl_equation_unsat in H. apply H. exists x. trivial.
    destruct s0. destruct u. destruct H0.
    apply IHeqnL; auto. exists x. trivial.
    destruct s0. revert H1. case_eq (simpl_equation_list eqnL); intros. icase p.
    apply IHeqnL; auto. exists x. tauto.
    icase p. revert H1. case_eq (simpl_equation_list eqnL); intros. icase p.
    apply IHeqnL; auto. exists x. tauto.
    revert H1. case_eq (simpl_equation_list eqnL); intros. icase p.
    apply IHeqnL; auto. exists x. tauto.
  Qed.

  Lemma simpl_equation_list_length: forall eqn_list eq_list eqn_list',
    simpl_equation_list eqn_list = Some (eq_list, eqn_list') ->
    2 * length eqn_list >= length eq_list + 2 * length eqn_list'.
  Proof.
    induction eqn_list; simpl; intros. 
    inv H; simpl; auto.
    revert H; case_eq (simpl_equation a); disc; intro.
    destruct s0. destruct u. intros.
    spec IHeqn_list eq_list eqn_list' H0. omega.
    destruct s0. case_eq (simpl_equation_list eqn_list); disc; intros.
    icase p. inv H1. simpl.
    spec IHeqn_list l eqn_list' H. omega.
    icase p. case_eq (simpl_equation_list eqn_list); disc; intros.
    icase p. inv H1.
    spec IHeqn_list l eqn_list' H. simpl. omega.
    case_eq (simpl_equation_list eqn_list); disc; intros.
    icase p. inv H1.
    spec IHeqn_list eq_list l0 H. simpl. omega.
  Qed.

  Fixpoint subst_equation_list (sbst : substitution) (eqn_list : list equation) : option (list substitution * list equation) :=
    match eqn_list with
     | nil => Some (nil, nil)
     | eqn :: eqn_list' =>
       match subst sbst eqn with
        | Absurd => None
        | Simpler (inl tt) => subst_equation_list sbst eqn_list'
        | Simpler (inr (inl eq1)) => 
          match subst_equation_list sbst eqn_list' with
           | None => None
           | Some (eq_list, eqn_list'') => Some (eq1 :: eq_list, eqn_list'')
          end
        | Simpler (inr (inr (eq1, eq2))) =>
          match subst_equation_list sbst eqn_list' with
           | None => None
           | Some (eq_list, eqn_list'') => Some (eq1 :: eq2 :: eq_list, eqn_list'')
          end
        | Same eqn' =>
          match subst_equation_list sbst eqn_list' with
           | None => None
           | Some (eq_list, eqn_list'') => Some (eq_list, eqn' :: eqn_list'')
          end
       end
     end.
  Instance substable_eq_list : substable (list equation) (option (list substitution * list equation)) :=
   Substable subst_equation_list.

  Lemma subst_equation_list_Some: forall sbst eqnL sbstL' eqnL',
    subst sbst eqnL = Some (sbstL', eqnL') ->
   (forall ctx, eval (upd_subst ctx sbst) eqnL <-> eval ctx sbstL' /\ eval ctx eqnL') /\
   (forall x', In x' (vars sbstL' ++ vars eqnL') -> 
   In x' ((vars (sbst_object sbst)) ++ (vars eqnL))) /\
   ~In (sbst_var sbst) (vars sbstL' ++ vars eqnL').
  Proof with try tauto.
    induction eqnL; simpl; intros.
    inv H. compute...
    revert H.  simpl in IHeqnL. case_eq (subst_equation_list sbst eqnL); intros.
    2: icase (subst_equation sbst a); icase s0; [icase u | icase s0]; icase p.
    destruct p. spec IHeqnL l l0 H. destruct IHeqnL as [? [? ?]].
    revert H0. case_eq (subst_equation sbst a); disc; intros.
    destruct s0. destruct u. inv H4.
    split. intro. spec H1 ctx. rewrite H1.
    firstorder. eapply subst_equation_valid; eauto.
    split; auto.
    intros. spec H2 x' H4. apply in_or_app. apply in_app_or in H2. destruct H2; auto. right. apply in_or_app; auto.
    destruct s0. inv H4. simpl.
    destruct (subst_equation_reduce1 _ _ _ H0). split. intro. rewrite H1. firstorder.
    split. intros.
    assert (In x' ((vars s0)++(vars l)++(vars eqnL'))).
    repeat rewrite in_app_iff in *;simpl in *...
    rewrite in_app_iff in H7. destruct H7.
    destruct H5. spec H5 x' H7.  rewrite app_assoc. apply in_or_app; auto.
    spec H2 x' H7. repeat rewrite in_app_iff in *...
    destruct H5. intro.
    assert (In (sbst_var sbst) ((vars s0)++(vars l)++(vars eqnL'))).
    repeat rewrite in_app_iff in *;simpl in *...
    apply in_app_or in H8. destruct H8; contr.
    destruct p. inv H4. simpl.
    destruct (subst_equation_reduce2 _ _ _ _ H0).
    split. intro. simpl in H4. rewrite <- H4. rewrite H1. tauto.
    destruct H5. split. intros.
    assert (In x' (((vars s0)++(vars s1))++((vars l)++(vars eqnL')))).
    repeat rewrite in_app_iff in *;simpl in *;repeat rewrite in_app_iff in *...
    rewrite in_app_iff in H8. destruct H8.
    spec H5 x' H8. rewrite app_assoc. apply in_or_app; auto.
    spec H2 x' H8. apply in_or_app. apply in_app_or in H2. destruct H2; auto. right. apply in_or_app; auto.
    intro.
    assert (In (sbst_var sbst) (((vars s0)++(vars s1))++((vars l)++(vars eqnL')))).
    repeat rewrite in_app_iff in *;simpl in *;repeat rewrite in_app_iff in *... 
    rewrite in_app_iff in H8. destruct H8;contr.
    inv H4. simpl.
    destruct (subst_equation_equiv _ _ _ H0). split. intro. rewrite H1. firstorder.
    destruct H5. split. intros.
    apply in_app_or in H7. destruct H7. spec H2 x'. spec H2. apply in_or_app; auto.
    apply in_app_or in H2. apply in_or_app; destruct H2; auto. right. apply in_or_app; auto.
    apply in_app_or in H7. destruct H7. spec H5 x' H7. rewrite app_assoc. apply in_or_app; auto.
    spec H2 x'. spec H2. apply in_or_app; auto.
    apply in_app_or in H2. apply in_or_app; destruct H2; auto. right. apply in_or_app; auto.
    intro.
    apply in_app_or in H7. destruct H7. apply H3. apply in_or_app; auto.
    apply in_app_or in H7. destruct H7; contr. apply H3. apply in_or_app; auto.
  Qed.

  Lemma subst_equation_list_None: forall sbst (eqnL: list equation),
    subst sbst eqnL = None -> forall ctx, ~eval (upd_subst ctx sbst) eqnL.
  Proof.
    induction eqnL; simpl; repeat intro. disc.
    simpl in IHeqnL.
    destruct H0.
    revert H. case_eq (subst_equation sbst a); intros.
    apply subst_equation_unsat with (ctx := ctx) in H. apply H. trivial.
    simpl in H.
    destruct s0. destruct u.
    eapply IHeqnL; eauto.
    destruct a. revert H2. case_eq (subst_equation_list sbst eqnL); intros. icase p.
    eapply IHeqnL; eauto.
    destruct p0.
    icase s0. destruct p. disc.
    revert H2. case_eq (subst_equation_list sbst eqnL); intros. icase p.
    eapply IHeqnL; eauto.
    revert H2. case_eq (subst_equation_list sbst eqnL); intros. icase p.
    eapply IHeqnL; eauto.
  Qed.

  Lemma subst_equation_list_length: forall sbst eqn_list sbst_list eqn_list',
    subst sbst eqn_list = Some (sbst_list, eqn_list') ->
    2 * length eqn_list >= length sbst_list + 2 * length eqn_list'.
  Proof.
    induction eqn_list; simpl; intros. 
    inv H; simpl; auto.
    revert H; case_eq (subst_equation sbst a); disc; intro.
    destruct s0. destruct u. intros.
    spec IHeqn_list sbst_list eqn_list' H0. omega.
    destruct s0. case_eq (subst_equation_list sbst eqn_list); disc; intros.
    icase p. inv H1. simpl.
    spec IHeqn_list l eqn_list' H. omega.
    icase p. case_eq (subst_equation_list sbst eqn_list); disc; intros.
    icase p. inv H1.
    spec IHeqn_list l eqn_list' H. simpl. omega.
    case_eq (subst_equation_list sbst eqn_list); disc; intros.
    icase p. inv H1.
    spec IHeqn_list sbst_list l0 H. simpl. omega.
  Qed.

  Definition subst_nzvar (sbst : substitution) (v : var) :=
  match (eq_dec (sbst_var sbst) v) with
  |left _ => match sbst_object sbst with
             |Cobject c => if (eq_dec c bot) then Absurd else Simpler tt
             |Vobject v' => Same v'
             end 
  |right _ => Same v 
  end.

 Instance substable_nzvar : substable var (result var unit) :=
  Substable subst_nzvar.

  Fixpoint subst_nzvar_list (sbst : substitution) (l : list var) : option (list var) :=
   match l with
   |nil => Some nil
   |v::l' => match subst_nzvar sbst v with
             |Absurd => None
             |Simpler tt => subst_nzvar_list sbst l'
             |Same v' => match subst_nzvar_list sbst l' with
                         |Some l'' => Some (v'::l'')
                         |None => None
                         end
             end
   end.
 
  Instance substable_nz_list : substable (list var) (option (list var)) :=
   Substable subst_nzvar_list.

  Record equation_system : Type := Equation_system {
    eqs_nzvars        : list var;
    eqs_substitutions : list substitution;
    eqs_equations     : list equation
  }.

  Definition eval_equation_system (ctx : context) (eqs : equation_system) : Prop :=
    ctx |= (eqs_nzvars eqs) /\ ctx |= (eqs_substitutions eqs) /\ ctx |= (eqs_equations eqs).
  Instance evalable_equation_system : evalable context equation_system :=
    Evalable eval_equation_system.

  (* This should not be moved to base because it's just a custom termination measure for the next function. *) 
  Definition size_equation_system (eqs : equation_system) : nat :=
    length (eqs_substitutions eqs) + (3 * length (eqs_equations eqs)).

  (* This is much shorter & simpler than before the equality -> substitution & dt change *)
  Function simpl_equation_system (eqs : equation_system) 
  {measure size_equation_system eqs} :  option equation_system :=
    match eqs_substitutions(eqs), eqs_equations(eqs) with 
     | nil, eqn_list =>
        match simpl_equation_list eqn_list with
         | Some (nil, eqn_list') => Some (Equation_system (eqs_nzvars eqs) nil eqn_list')
         | Some (eq_list', eqn_list') => simpl_equation_system (Equation_system (eqs_nzvars eqs) eq_list' eqn_list')
         | None => None
        end
     | sbst1 :: sbst_list, eqn_list => 
           match subst sbst1 sbst_list with
            | Some sbst_list' =>
              match subst sbst1 eqn_list with
                | Some (sbst_list'', eqn_list') => 
                  match subst sbst1 (eqs_nzvars eqs) with
                   | Some nz_list' =>
                     match simpl_equation_system (Equation_system nz_list' (sbst_list' ++ sbst_list'') eqn_list') with
                      | None => None
                      | Some s => 
                         Some (Equation_system (eqs_nzvars s) (sbst1 :: (eqs_substitutions s)) (eqs_equations s))
                     end
                   | None => None
                  end
                | None => None
              end
            | None => None
           end
    end.
  Proof.
    (* 1 *)
    intros. destruct eqs. subst. unfold size_equation_system, eqs_substitutions, eqs_equations in *. subst. 
    apply simpl_equation_list_length in teq0. simpl in *. omega.
    (* 2 *)
    intros. destruct eqs. subst. unfold size_equation_system, eqs_substitutions, eqs_equations in *. simpl.
    rewrite teq in *.
    apply subst_substitution_list_length in teq0.
    apply subst_equation_list_length in teq1.
    simpl in *. rewrite app_length. omega.
  Defined. (* Seems to be faster than Defined, and also I am not sure if Defined will mess up the extraction vs. Qed. *)

  Lemma eval_substitution_refl : forall ctx s, eval_substitution (upd_subst ctx s) s.
  Proof with try tauto.
   destruct s0 as [[? ?] ?].
   compute. destruct (sv.t_eq_dec v v)...
   icase o; try rewrite upd_eq; auto.
   symmetry. simpl in *.
   destruct (sv.t_eq_dec v v0)...
  Qed.

  Definition upd_subst_list (ctx : context) (subst_list : list substitution) : context :=
    fold_right (fun vfp ctx' => upd_subst ctx' vfp) ctx subst_list.
  Lemma upd_subst_equiv: forall ctx sbst,
    ctx (sbst_var sbst) = get ctx (sbst_object sbst) ->
    upd_subst ctx sbst = ctx.
  Proof.
    unfold upd_subst, upd. intros.
    extensionality a'.
    case (eq_dec (sbst_var sbst) a'); intros. subst a'. rewrite H; trivial.
    trivial.
  Qed.

  Lemma upd_subst_list_equiv: forall ctx (subst_list : list substitution),
    eval_list ctx subst_list ->
    upd_subst_list ctx subst_list = ctx. 
  Proof.
    induction subst_list; simpl. trivial.
    destruct a. simpl. intros. destruct H.
    rewrite IHsubst_list; auto. destruct x.
    apply upd_subst_equiv; auto.
  Qed.

  Lemma subst_nzvar_Absurd: forall sbst (v : var),
   subst sbst v = Absurd -> forall rho,~(upd_subst rho sbst) |= v.
  Proof with try tauto.
   intros.
   destruct sbst as [[? ?] ?].
   icase o; compute in H.
   destruct (sv.t_eq_dec v0 v);inv H.
   intro. compute in H0.
   destruct (sv.t_eq_dec v0 v);subst;
   destruct (e_eq_dec s0 bot);subst;inv H...
  Qed.

  Lemma subst_nzvar_Simpler: forall sbst (v : var),
   subst sbst v = Simpler tt -> forall rho, (upd_subst rho sbst) |= v.
  Proof with try tauto.
   intros.
   destruct sbst as [[? ?] ?].
   icase o; compute in H.
   destruct (sv.t_eq_dec v0 v);inv H.
   intro. compute in H0.
   destruct (sv.t_eq_dec v0 v);
   destruct (e_eq_dec s0 bot);subst;inv H...
  Qed.

  Lemma subst_nzvar_Same: forall sbst (v v': var),
   subst sbst v = Same v' -> 
   (forall rho, rho |= v' <-> (upd_subst rho sbst) |= v) /\
   (In v' (v::(vars (sbst_object sbst)))) /\ (sbst_var sbst <> v').
  Proof with try tauto.
   intros.
   destruct sbst as [[? ?] ?].
   icase o; compute in *.
   destruct (sv.t_eq_dec v0 v);inv H...
   split;intros... split;intros;subst...
   destruct (sv.t_eq_dec v0 v);
   destruct (e_eq_dec s0 bot);subst;inv H...
  Qed.

  Lemma subst_nzvars_list_None: forall sbst (nl : list var),
   subst sbst nl = None -> forall rho, ~(upd_subst rho sbst)|= nl.
  Proof with try tauto.
   induction nl;repeat intro. inv H.
   simpl in *.
   remember (subst_nzvar sbst a).
   remember (subst_nzvar_list sbst nl).
   symmetry in Heqr,Heqo.
   icase r. 
   apply subst_nzvar_Absurd with (rho:=rho)in Heqr...
   icase u. subst. apply IHnl with (rho:=rho) in H.
   apply H...
   icase o. spec IHnl...
   apply IHnl with (rho:=rho)...
  Qed.

  Lemma subst_nzvars_list_Some: forall (sbst : substitution)
   (nl nl' : list var),
   subst sbst nl = Some nl' ->
   (forall ctx : context,
   upd_subst ctx sbst |= nl <-> ctx |= nl') /\
   (forall x' : var,
   In x' nl' ->
   In x' (vars (sbst_object sbst) ++ nl)) /\
   ~ In (sbst_var sbst) nl'.
  Proof with try tauto.
   induction nl;intros. inv H.
   split;simpl;intros...
   simpl in H.
   remember (subst_nzvar sbst a).
   remember (subst_nzvar_list sbst nl).
   symmetry in Heqr,Heqo.
   icase r. icase u;subst.
   spec IHnl nl' H.
   destruct IHnl as [? [? ?]].
   split;intros.
   split;intros;simpl in *. apply H0...
   split. apply H0... apply subst_nzvar_Simpler with (rho:=ctx) in Heqr...
   split;intros...
   spec H1 x' H3. rewrite in_app_iff in *;simpl...
   icase o;inv H.
   spec IHnl l Heqo.
   destruct IHnl as [? [? ?]].
   apply subst_nzvar_Same in Heqr.
   destruct Heqr as [? [? ?]].
   split;intros. spec H ctx. spec H2 ctx. simpl in *...
   split;intros. destruct H5. subst.
   destruct H3;subst;rewrite in_app_iff;simpl...
   spec H0 x' H5.
   rewrite in_app_iff in *. simpl in *...
   intro. apply H1. destruct H5;subst...
  Qed.

  Lemma eval_subst_correct: forall (sbst : substitution) ctx,
   ctx |= sbst ->
   ctx (sbst_var sbst) = get ctx (sbst_object sbst).
  Proof.
   intros.
   destruct sbst as [[? ?] ?]. icase o.
  Qed.

  Lemma simpl_equation_system_Some: forall eqs eqs',
    simpl_equation_system eqs = Some eqs' ->
    (forall ctx, ctx |= eqs <-> ctx |= eqs') /\
    (forall ctx, (upd_subst_list ctx (eqs_substitutions eqs')) |= eqs <->
      ctx |= (eqs_nzvars eqs') /\ ctx |= (eqs_equations eqs')).
  Proof with try tauto.
    (* Try induction on the measure. *)
    intro eqs.
    remember (size_equation_system eqs).
    assert (n >= size_equation_system eqs) by omega. clear Heqn.
    revert eqs H. induction n; intros.
    (* base case *)
    destruct eqs as [l' l l0]. unfold size_equation_system in H. simpl in H.
    assert (length l = 0) by omega. assert (length l0 = 0) by omega.
    icase l; icase l0. clear H H1 H2.
    rewrite simpl_equation_system_equation in H0. simpl in H0. inv H0.
    simpl. unfold eval_equation_system;simpl. firstorder.
    (* inductive case *)
    rewrite simpl_equation_system_equation in H0. destruct eqs as [ln l l0]. destruct eqs' as [ln' ll' l0'].
    unfold eqs_nzvars,eqs_substitutions, eqs_equations in *. simpl in *. destruct l. 
    (* case 1: no recursive call, we are done *)
    revert H0.
    case_eq (simpl_equation_list l0); disc. simpl. destruct p.
    destruct l; intros.
    inv H1. unfold eval_equation_system. simpl.
    apply simpl_equation_list_Some in H0. destruct H0. simpl in H0.
    split; intro; rewrite H0; tauto.
    (* case 2: recursive call, but no subst *)
    spec IHn (Equation_system ln (s0 :: l) l1).
    spec IHn.
    apply simpl_equation_list_length in H0. 
    unfold size_equation_system in *. simpl in *. omega.
    spec IHn (Equation_system ln' ll' l0') H1. destruct IHn.
    apply simpl_equation_list_Some in H0. destruct H0.
    unfold eval_equation_system in *. simpl in *.
    split; intros. rewrite <- H2. rewrite <- H0. tauto.
    rewrite <- H3. rewrite <- H0. tauto.
    (* case 3: recursive call inside a subst *)
    revert H0. unfold size_equation_system in H. simpl in H.
    case_eq (subst_substitution_list s0 l); disc.
    case_eq (subst_equation_list s0 l0); disc. intros [? ?] ? ? ?.
    case_eq (subst_nzvar_list s0 ln); disc. intros ? ?.
    case_eq (simpl_equation_system (Equation_system l4 (l3 ++ l1) l2));intros.
    2 : inv H4. inv H4.
    spec IHn (Equation_system l4 (l3 ++ l1) l2). spec IHn.
    unfold size_equation_system. simpl in *. rewrite app_length.
    apply subst_equation_list_length in H0. apply subst_substitution_list_length in H1. omega.
    spec IHn e0. spec IHn;auto. destruct IHn as [H4 H5].
    destruct e0 as [l5 l6 l7];simpl in *.
    unfold eval_equation_system in *;simpl in *.
    apply subst_equation_list_Some in H0.
    apply subst_substitution_list_Some in H1.
    apply subst_nzvars_list_Some in H2.
    destruct H0 as [H0 _]. destruct H1 as [H1 _].
    destruct H2 as [H2 _].
    split;intro rho;split;intros.
    spec H0 rho;spec H1 rho;spec H2 rho;spec H4 rho;spec H5 rho.
    rewrite upd_subst_equiv in H0,H1,H2;try apply eval_subst_correct...
    change (eval_list rho (l3++l1)) with (rho |= (l3++l1)) in H4.
    rewrite eval_list_app in H4...
    spec H0 rho;spec H1 rho;spec H2 rho;spec H4 rho;spec H5 rho.
    rewrite upd_subst_equiv in H0,H1,H2;try apply eval_subst_correct...
    change (eval_list rho (l3++l1)) with (rho |= (l3++l1)) in H4.
    rewrite eval_list_app in H4.
    rewrite upd_subst_list_equiv in H5...
    spec H2 (upd_subst_list rho l6).
    spec H1 (upd_subst_list rho l6).
    spec H0 (upd_subst_list rho l6).
    spec H5 rho.
    change (eval_list (upd_subst_list rho l6) (l3 ++ l1)) with ((upd_subst_list rho l6) |= (l3 ++ l1)) in H5.
    rewrite eval_list_app in H5...
    spec H2 (upd_subst_list rho l6).
    spec H1 (upd_subst_list rho l6).
    spec H0 (upd_subst_list rho l6).
    spec H5 rho.
    change (eval_list (upd_subst_list rho l6) (l3 ++ l1)) with ((upd_subst_list rho l6) |= (l3 ++ l1)) in H5.
    rewrite eval_list_app in H5.
    split... split... split... apply eval_substitution_refl.
  Qed.

  Lemma simpl_equation_system_None: forall eqs,
    simpl_equation_system eqs = None ->
    ~(exists rho, rho |= eqs).
  Proof with try tauto.
    intro. remember (size_equation_system eqs).
    assert (n >= size_equation_system eqs) by omega. clear Heqn.
    revert eqs H.
    induction n; destruct eqs as [ln l l0]; intros.
    (* base *)
    unfold size_equation_system in H. simpl in H.
    assert (length l = 0) by omega. assert (length l0 = 0) by omega. icase l. icase l0.
    (* inductive *)
    rewrite simpl_equation_system_equation in H0. simpl in H0.
    destruct l; revert H0.
    unfold size_equation_system,eqs_substitutions, eqs_equations in H. simpl in H.
    simpl.
    unfold eval_equation_system,eqs_substitutions, eqs_equations. simpl.
    (* case 1 *)
    case_eq (simpl_equation_list l0); disc. destruct p. icase l. intros.
    apply IHn in H1. intro.
    apply simpl_equation_list_Some in H0. destruct H0.
    destruct H2 as [ctx [? ?]]. 
    unfold eval, eval_equation_system in *. 
    simpl in *.  unfold eval_equation_system,eqs_equations  in *.
    contradiction H1. exists ctx. unfold eqs_substitutions in *. simpl.
    spec H0 ctx. destruct H0. tauto.
    unfold size_equation_system in *; simpl in *.
    apply simpl_equation_list_length in H0. simpl in *. omega.
    (* case 2 *)
    repeat intro. destruct H2 as [ctx [? ?]].
    apply simpl_equation_list_None in H0. apply H0.
    exists ctx. tauto.
    (* case 3 *)
    case_eq (subst_substitution_list s0 l).
    case_eq (subst_equation_list s0 l0). destruct p.
    case_eq (subst_nzvar_list s0 ln).
    intros ? ? ? ? ?. case_eq (simpl_equation_system (Equation_system l3 (l4 ++ l1) l2)).
    destruct e0; disc. intros.
    apply IHn in H3. intro. apply H3. clear H3.
    simpl in *. 
    unfold eval_equation_system in *. simpl in *.
    apply subst_nzvars_list_Some in H0. destruct H0 as [? [? ?]].
    apply subst_equation_list_Some in H1. destruct H1 as [? [? ?]].
    apply subst_substitution_list_Some in H2. destruct H2 as [? [? ?]].
    destruct H5 as [ctx [? [[? ?] ?]]].
    rewrite <- upd_subst_equiv with (ctx := ctx) (sbst := s0) in H5.
    2: destruct s0 as [[? ?] ?]; compute; icase o.
    rewrite <- upd_subst_equiv with (ctx := ctx) (sbst := s0) in H11.
    2: destruct s0 as [[? ?] ?]; compute; icase o...
    rewrite <- upd_subst_equiv with (ctx := ctx) (sbst := s0) in H13.
    2: destruct s0 as [[? ?] ?]; compute; icase o...
    exists ctx.
    simpl in H0;rewrite H0 in H5.
    simpl in H2;rewrite H2 in H11.
    simpl in H1;rewrite H1 in H13.
    change (eval_list ctx (l4++l1)) with (ctx |= (l4++l1)).
    rewrite eval_list_app. tauto.
    unfold size_equation_system in *; apply subst_equation_list_length in H1.
    unfold eqs_substitutions,eqs_equations,eqs_nzvars in *.
    apply subst_substitution_list_length in H2. simpl in *. rewrite app_length. omega.
    (* case 4 *)
    intros. intros [ctx ?].
    apply subst_nzvars_list_None with (rho:=ctx) in H0. apply H0.
    simpl in H4. 
    unfold eval_equation_system in H4;simpl in H4...
    rewrite upd_subst_equiv;try apply eval_subst_correct...
    (* case 5 *)
    intros. intros [ctx ?].
    apply subst_equation_list_None with (ctx:=ctx)in H0. apply H0.
    simpl in H3;unfold eval_equation_system in H3;simpl in H3.  
    rewrite upd_subst_equiv; try apply eval_subst_correct...
    (* case 6*)
    intros. intros [ctx ?].
    apply subst_substitution_list_None with (ctx:=ctx)in H0. apply H0.
    simpl in H2;unfold eval_equation_system in H2;simpl in H2.  
    rewrite upd_subst_equiv;try apply eval_subst_correct...
  Qed.

  Lemma simpl_equation_system_sat_sound: forall eqs nzvars sbst eqn,
    simpl_equation_system eqs = Some (Equation_system nzvars sbst eqn) ->
    forall ctx, ctx |= nzvars /\ ctx |= eqn <-> eval (upd_subst_list ctx sbst) eqs.
  Proof.
    intros. apply simpl_equation_system_Some in H. destruct H. rewrite H0. tauto.
  Qed.

  Lemma simpl_equation_system_sat_complete: forall ctx eqs,
   ctx |= eqs ->  exists nzvars, exists sbst, exists eqn,
      simpl_equation_system eqs = Some (Equation_system nzvars sbst eqn) /\  ctx |= nzvars /\ ctx |= eqn.
  Proof.
    intros. 
    case_eq (simpl_equation_system eqs); intros.
    icase e0. exists eqs_nzvars0. 
    exists  eqs_substitutions0. exists eqs_equations0. split;trivial.
    apply simpl_equation_system_Some in H0. destruct H0. spec H0 ctx. simpl in *.
    rewrite H0 in H. destruct H; tauto.
    apply simpl_equation_system_None in H0. destruct H0. exists ctx; auto.
  Qed.
 
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
   valid eql.
  Proof with try tauto.
   repeat intro.
   destruct eql as [obj1 obj2].
   icase obj1;icase obj2.
   compute in H.
   destruct (sv.t_eq_dec v0 v);subst;simpl...
   inv H. simpl in H.
   destruct (eq_dec s0 s1);subst;simpl;inv H...
  Qed.

  Lemma eql2subst_Absurd: forall eql,
   eql2subst eql = Absurd ->
   forall rho, ~rho|=eql.
  Proof with try tauto.
   repeat intro.
   destruct eql as [obj1 obj2].
   icase obj1;icase obj2;compute in H.
   destruct (sv.t_eq_dec v0 v);subst;simpl;inv H...
   destruct (e_eq_dec s0 s1);inv H.
   compute in H0...
  Qed.

  Lemma eql2subst_Same: forall eql subst,
    eql2subst eql = Same subst ->
    equiv_eval eql subst.
  Proof with try tauto.
   repeat intro.
   destruct eql as [obj1 obj2].
   icase obj1;icase obj2;compute in H;
   try destruct (sv.t_eq_dec v0 v);subst;simpl;inv H...
   compute. split;intros;subst...
   destruct (e_eq_dec s0 s1);inv H1.
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
   eql2subst_list l = Some l' -> equiv_eval l l'.
  Proof with try tauto.
   induction l;repeat intro;inv H.
   simpl...
   remember (eql2subst a). symmetry in Heqr.
   destruct r;inv H1. icase u.
   apply eql2subst_Simpler in Heqr...
   spec Heqr rho. spec IHl l' H0 rho. simpl in *...
   remember (eql2subst_list l).
   symmetry in Heqo. icase o.
   inv H0. spec IHl l0. spec IHl...
   apply eql2subst_Same in Heqr.
   spec IHl rho. spec Heqr rho. simpl in *...
  Qed.

  Definition subst2eql (subst : substitution) : equality :=
   let (v,obj) := projT1 subst in (Vobject v,obj).
  Definition subst2eql_list := fun l =>
   fold_right (fun sbst l' => (subst2eql sbst)::l') nil l.

  Lemma subst2eql_eval: forall sbst,
   equiv_eval sbst (subst2eql sbst).
  Proof with try tauto.
   repeat intro.
   destruct sbst as [[? ?] ?].
   icase o;compute...
  Qed.
  Lemma subst2eql_list_eval: forall l,
   equiv_eval l (subst2eql_list l).
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
   wrapped_ses ses = Some ses' -> equiv_eval ses ses'.
  Proof with try tauto.
   intros.
   destruct ses as [l1 l2 l3].
   unfold wrapped_ses in H. simpl in H.
   remember (eql2subst_list l2).
   symmetry in Heqo. icase o;inv H.
   apply eql2subst_list_Some in Heqo.
   repeat intro; simpl in *;spec Heqo rho;
   unfold eval_sat_equation_system,eval_equation_system in *;simpl in *...
  Qed.

  Lemma unwrapped_ses_eval: forall ses,
   equiv_eval ses (unwrapped_ses ses).
  Proof with try tauto.
   repeat intro.
   destruct ses as [l1 l2 l3].
   generalize (subst2eql_list_eval l2 rho);simpl;intro.
   unfold eval_equation_system,eval_sat_equation_system...
  Qed.

  Definition SATsimplifier := fun (ses : sat_equation_system) =>
   match wrapped_ses ses with
   |None => None
   |Some ses' => match simpl_equation_system ses' with
                 |None => None
                 |Some ses'' => Some (unwrapped_ses ses'')
                 end
   end.

  Lemma SATsimplifier_None: forall ses,
   SATsimplifier ses = None -> forall rho,~rho |= ses.
  Proof with try tauto.
   repeat intro.
   unfold SATsimplifier in H.
   remember (wrapped_ses ses).
   symmetry in Heqo;icase o.
   generalize (wrapped_ses_Some _ _ Heqo);intro.
   remember (simpl_equation_system e0). symmetry in Heqo0.
   icase o. apply simpl_equation_system_None in Heqo0.
   apply Heqo0. exists rho. apply H1...
   apply wrapped_ses_None with (rho:=rho) in Heqo...
  Qed.

  Lemma SATsimplifier_Some: forall ses ses',
   SATsimplifier ses = Some ses' -> 
   forall rho, rho |= ses <-> rho |= ses'.
  Proof with try tauto.
   repeat intro.
   unfold SATsimplifier in H.
   remember (wrapped_ses ses).
   symmetry in Heqo;icase o.
   generalize (wrapped_ses_Some _ _ Heqo);intro.
   remember (simpl_equation_system e0). symmetry in Heqo0.
   icase o. apply simpl_equation_system_Some in Heqo0.
   destruct Heqo0 as [? _]. spec H1 rho.
   spec H0 rho. inv H. rewrite H0. rewrite H1.
   apply unwrapped_ses_eval.
  Qed.

  Definition ies_simplifier := fun (ies : impl_equation_system) =>
   match SATsimplifier (ies2ses ies) with
   |None => None
   |Some ses => Some (Impl_equation_system (impl_exvars ies) (sat_nzvars ses) 
                (sat_equalities ses) (sat_equations ses))
   end.

  Lemma ies_simplifier_None: forall ies,
   ies_simplifier ies = None -> forall rho, ~rho |= ies.
  Proof with try tauto.
   repeat intro.
   unfold ies_simplifier in H.
   remember (SATsimplifier (ies2ses ies)).
   symmetry in Heqo. icase o.
   destruct H0 as [rho' H0].
   apply SATsimplifier_None with (rho:=[impl_exvars ies => rho']rho) in Heqo.
   apply Heqo...
  Qed.

  Lemma ies_simplifier_Some: forall ies ies',
   ies_simplifier ies = Some ies' -> forall rho, rho|= ies <-> rho |= ies'.
  Proof with try tauto.
   repeat intro.
   unfold ies_simplifier in H.
   remember (SATsimplifier (ies2ses ies)).
   symmetry in Heqo. icase o. inv H.
   generalize (SATsimplifier_Some _ _ Heqo);intro.
   split;intro. destruct H0 as [rho' H0].
   exists rho'. rewrite H in H0.
   simpl in *. unfold ies2ses;simpl...
   destruct H0 as [rho' H0].
   exists rho'. apply H...
  Qed.

  Fixpoint subst_list {A} `{substable A (option A)} (l : list substitution) (a : A) : option A:=
   match l with
   |nil => Some a
   |sbst::l' => match subst sbst a with
                |None => None
                |Some a' => subst_list l' a'
                end
   end.

  Lemma subst_list_subst_None:
   forall l (l' : list substitution) , subst_list l l' = None ->
   forall rho, rho |= l -> rho |= l' -> False.
  Proof with try tauto.
   induction l;intros.
   inv H. destruct H0.
   inv H. 
   revert H4. case_eq (subst_substitution_list a l');intros.
   apply subst_substitution_list_Some in H.
   destruct H as [? _]. apply IHl with (rho:=rho) in H4...
   apply H... rewrite list_eval_rewrite.
   repeat intro. rewrite list_eval_rewrite in H1.
   spec H1 e0 H3.
   rewrite upd_subst_equiv... apply eval_subst_correct...
   apply subst_substitution_list_None with (ctx:=rho) in H.
   apply H.
   rewrite list_eval_rewrite. intros.
   rewrite list_eval_rewrite in H1. spec H1 e0 H3.
   rewrite upd_subst_equiv... apply eval_subst_correct...   
  Qed.

  Lemma subst_list_subst_Some:
   forall l (l' l'': list substitution) , subst_list l l' = Some l'' ->
   forall rho, rho |= l -> (rho |= l' <-> rho |= l'').
  Proof with try tauto.
   induction l;intros. inv H...
   destruct H0. inv H.
   revert H3. case_eq (subst_substitution_list a l');intros.
   apply subst_substitution_list_Some in H.
   destruct H as [? _].
   spec H rho. apply IHl with (rho:=rho) in H3...
   rewrite<- H3. rewrite<- H.
   repeat rewrite list_eval_rewrite.
   split;intros H4 e H5;spec H4 e H5.
   rewrite upd_subst_equiv... apply eval_subst_correct...
   rewrite upd_subst_equiv in H4... apply eval_subst_correct...
   inv H3.
  Qed.
 
  Lemma subst_list_nzvars_None:
   forall l (l' : list var) , subst_list l l' = None ->
   forall rho, rho |= l -> rho |= l' -> False.
  Proof with try tauto.
   induction l;intros.
   inv H. destruct H0.
   inv H. 
   revert H4. case_eq (subst_nzvar_list a l');intros.
   apply subst_nzvars_list_Some in H.
   destruct H as [? _]. apply IHl with (rho:=rho) in H4...
   apply H... rewrite list_eval_rewrite.
   intros. rewrite list_eval_rewrite in H1.
   spec H1 e0 H3.
   rewrite upd_subst_equiv... apply eval_subst_correct...
   apply subst_nzvars_list_None with (rho:=rho) in H.
   apply H.
   rewrite list_eval_rewrite. intros.
   rewrite list_eval_rewrite in H1. spec H1 e0 H3.
   rewrite upd_subst_equiv... apply eval_subst_correct...
  Qed.   

  Lemma subst_list_nzvars_Some: 
   forall l (l' l'': list var) , subst_list l l' = Some l'' ->
   forall rho, rho |= l -> (rho |= l' <-> rho |= l'').   
  Proof with try tauto.
   induction l;intros. inv H...
   destruct H0. inv H.
   revert H3. case_eq (subst_nzvar_list a l');intros.
   apply subst_nzvars_list_Some in H.
   destruct H as [? _].
   spec H rho. apply IHl with (rho:=rho) in H3...
   rewrite<- H3. rewrite<- H.
   repeat rewrite list_eval_rewrite.
   split;intros H4 e H5;spec H4 e H5.
   rewrite upd_subst_equiv... apply eval_subst_correct...
   rewrite upd_subst_equiv in H4... apply eval_subst_correct...
   inv H3.
  Qed.

  Fixpoint subst_list_eqn (l : list substitution) (leqn : list equation) :=
  match l with
  |nil => Some (nil,leqn)
  |sbst::l' => match subst sbst leqn with
               |None => None
               |Some (l1,l2) => match (subst_list l' l1, subst_list_eqn l' l2) with
                                |(Some l1',Some (l2',l3')) => Some (l1'++l2',l3')
                                |_ => None
                                end
               end
  end.

  Lemma subst_list_eqn_None:
   forall l (l' : list equation) , subst_list_eqn l l' = None ->
   forall rho, rho |= l -> rho |= l' -> False.
  Proof with try tauto.
   induction l;intros. inv H.
   destruct H0. inv H.
   revert H4. case_eq (subst_equation_list a l');intros ? ?.
   destruct p as [l1 l2]. case_eq (subst_list l l1);intros ? ?.
   case_eq (subst_list_eqn l l2);intros. destruct p. inv H5.
   apply IHl with (rho:=rho) in H4...
   apply subst_equation_list_Some in H. destruct H as [? _].
   apply H. rewrite list_eval_rewrite;intros e H6.
   rewrite list_eval_rewrite in H1;spec H1 e H6.
   rewrite upd_subst_equiv;try apply eval_subst_correct...

   apply subst_list_subst_None with (rho:=rho) in H3...
   apply subst_equation_list_Some in H. apply H...
   rewrite list_eval_rewrite;intros e H6.
   rewrite list_eval_rewrite in H1;spec H1 e H6.
   rewrite upd_subst_equiv;try apply eval_subst_correct...
   
   apply subst_equation_list_None with (ctx:=rho) in H. apply H.
   rewrite list_eval_rewrite;intros e H6.
   rewrite list_eval_rewrite in H1;spec H1 e H6.
   rewrite upd_subst_equiv;try apply eval_subst_correct...
  Qed.   

  Lemma subst_list_eqn_Some: 
   forall l (l': list equation) l1 l2, subst_list_eqn l l' = Some (l1,l2) ->
   forall rho, rho |= l -> (rho |= l' <-> rho |= l1 /\ rho |= l2).
  Proof with try tauto.
   induction l;intros. inv H. simpl...
   destruct H0.
   inv H. revert H3. case_eq (subst_equation_list a l');intros ? ?.
   destruct p as [l3 l4]. case_eq (subst_list l l3);intros ? ?.
   case_eq (subst_list_eqn l l4);intros. destruct p. inv H4.
   rewrite eval_list_app.
   apply IHl with (rho:=rho) in H3...
   apply subst_equation_list_Some in H.
   destruct H as [H _]. spec H rho.
   apply subst_list_subst_Some with (rho:=rho) in H2...
   rewrite upd_subst_equiv in H;try apply eval_subst_correct...
   inv H4. inv H3. inv H3.
  Qed.

  Definition subst_list_eqs:= fun l (eqs : equation_system) =>
   let l1 := eqs_nzvars eqs in
   let l2 := eqs_substitutions eqs in
   let l3 := eqs_equations eqs in
   match (subst_list l l1,subst_list l l2,subst_list_eqn l l3) with
   |(Some l1',Some l2',Some pl) => Some (Equation_system l1' ((fst pl)++l2') (snd pl))
   | _ => None
   end.

  Lemma subst_list_eqs_Some:
   forall l eqs eqs', subst_list_eqs l eqs = Some eqs' ->
   forall rho, rho |= l -> (rho |= eqs <-> rho |= eqs').
  Proof with try tauto.
   intros.
   destruct eqs as [l1 l2 l3]. 
   unfold subst_list_eqs in H. simpl in H.
   revert H. 
   case_eq (subst_list l l1);
   case_eq (subst_list l l2);
   case_eq (subst_list_eqn l l3);intros;inv H3.
   destruct p as [l5 l6].
   apply subst_list_eqn_Some with (rho:=rho) in H...
   apply subst_list_subst_Some with (rho:=rho) in H1...
   apply subst_list_nzvars_Some with (rho:=rho) in H2...
   simpl. unfold eval_equation_system;simpl.
   change (eval_list rho (l5++l0)) with (rho |= (l5++l0)).
   rewrite eval_list_app...
  Qed.

  Lemma subst_list_eqs_None:
   forall l eqs, subst_list_eqs l eqs = None ->
   forall rho, rho |= l -> rho |= eqs -> False.
  Proof with try tauto.
   intros.
   destruct eqs as [l1 l2 l3]. 
   unfold subst_list_eqs in H. simpl in H.
   assert (rho |= l1 /\ rho |= l2 /\ rho |= l3) by tauto.
   clear H1.
   revert H.
   case_eq (subst_list l l1);
   case_eq (subst_list l l2);
   case_eq (subst_list_eqn l l3);intros;disc;
   try apply subst_list_eqn_None with (rho:=rho) in H;
   try apply subst_list_subst_None with (rho:=rho) in H1;
   try apply subst_list_nzvars_None with (rho:=rho) in H3...
  Qed.

  Definition exclusive {A} `{H : EqDec A} (l1: list A) := fun l2 =>
   fold_right (fun a b => if in_dec H a l1 then false else b) true l2.

  Lemma exclusive_true {A} `{H : EqDec A}: forall (l1 l2 : list A),
   exclusive l1 l2 = true <-> disjoint l1 l2.
  Proof with try tauto.
   induction l2;repeat intro. split;intros;simpl...
   intros rho H1. destruct H1...
   simpl. destruct (in_dec H a l1).
   split;repeat intro. inv H0.
   spec H0 a. elimtype False. apply H0;simpl...
   rewrite IHl2. split;intros H2 v;spec H2 v;simpl in *...
   intro. apply H2. split... destruct H0. destruct H1;subst...
  Qed.

  Lemma exclusive_false {A} `{H : EqDec A}: forall (l1 l2 : list A),
   exclusive l1 l2 = false <-> exists a, In a l1 /\ In a l2.
  Proof with try tauto.
   induction l2;intros. simpl;split;intros.
   inv H0. destruct H0...
   simpl. destruct (in_dec H a l1).
   split;intros... exists a...
   rewrite IHl2.
   split;intro H1;destruct H1 as [a' [H1 H2]];exists a'...
   destruct H2;subst...
  Qed.

  Lemma exclusive_comm {A} `{H : EqDec A}: forall (l1 l2 : list A),
   exclusive l1 l2 = exclusive l2 l1.
  Proof with try tauto.
   intros.
   case_eq (exclusive l1 l2);case_eq (exclusive l2 l1);intros;subst...
   rewrite exclusive_true in H1.
   rewrite exclusive_false in H0.
   destruct H0 as [a H0]. spec H1 a...
   rewrite exclusive_false in H1.
   rewrite exclusive_true in H0.
   destruct H1 as [a H1]. spec H0 a...
  Qed.

  Definition vars_filter {A B} `{varsable A B}`{EqDec B} (l1 : list A)(l2 : list B) :=
   filter (fun a => exclusive (vars a) l2) l1. 

  Lemma vars_filter_in{A B} `{varsable A B}`{EqDec B}: 
   forall (l1 : list A) (l2 : list B) v,
   In v (vars_filter l1 l2) <-> In v l1 /\ disjoint (vars v) l2.
  Proof with try tauto.
   intros.
   unfold vars_filter.
   rewrite filter_In.
   rewrite exclusive_true...
  Qed.

  Definition ses2ies (l : list var) (ses : sat_equation_system) :=
   Impl_equation_system l (sat_nzvars ses) (sat_equalities ses) (sat_equations ses).
  Definition is_empty_eqs := fun (eqs : equation_system) =>
   match (eqs_nzvars eqs,eqs_substitutions eqs,eqs_equations eqs) with
   |(nil,nil,nil) => true
   |_ => false
   end.
  Definition IMPLsimplifier (is : impl_system): result impl_system unit:=
   let (ies1,ies2) := is in
   let (ses1,ses2) := (ies2ses ies1,ies2ses ies2) in
   match (wrapped_ses ses1,wrapped_ses ses2) with
   |(Some eqs1,Some eqs2) =>
     match simpl_equation_system eqs1 with
     |None => Simpler tt
     |Some eqs1' => 
      let l1    := impl_exvars ies1 in
      let l2    := impl_exvars ies2 in
      let lsbst := eqs_substitutions eqs1' in
      let l := vars_filter lsbst (l1++l2) in
      match subst_list_eqs l eqs2 with
      |Some eqs2' => match simpl_equation_system eqs2' with
                     |Some eqs2'' => if is_empty_eqs eqs2'' then Simpler tt else 
                                     Same (ses2ies l1 (unwrapped_ses eqs1'),ses2ies l2 (unwrapped_ses eqs2''))
                     |None => Absurd
                     end
      |None => Absurd
      end
     end
    |_ => Absurd
   end.

  Lemma obj_disjoint_eval: forall (obj:object) rho rho' l,
   disjoint (vars obj) l ->
   (get ([l => rho']rho) obj = get rho obj).
  Proof with try tauto.
   intros. icase obj...
   simpl. rewrite override_not_in...
   intro. spec H v. apply H;simpl...
  Qed.

  Lemma substitutions_disjoint_eval: forall (sbst : substitution) rho rho' l,
   disjoint (vars sbst) l ->
   ([l => rho']rho |= sbst <-> rho |= sbst).
  Proof with try tauto.
   intros.
   destruct sbst as [[? ?] ?]. 
   assert (disjoint (v::nil) l /\ disjoint (vars o) l).
    split;intro v'; spec H v'; intro; apply H;
    simpl; unfold sbst_var,sbst_object;simpl in *...
   destruct H0.
   generalize (obj_disjoint_eval (Vobject v) rho rho' l H0);intro.
   generalize (obj_disjoint_eval o rho rho' l H1);intro.
   simpl in *. rewrite H2,H3...
  Qed.

  Lemma vars_filter_subst_list: forall (lsubst : list substitution) l l' rho rho',
   sublist l l' ->
   ([l => rho']rho |= vars_filter lsubst l' <-> rho |= vars_filter lsubst l').
  Proof with try tauto.
   intros.
   repeat rewrite list_eval_rewrite.
   split;intros H1 e H2;spec H1 e H2;apply vars_filter_in in H2;
   destruct H2 as [H3 H4];
   try apply substitutions_disjoint_eval in H1;
   try apply substitutions_disjoint_eval;
   try apply disjoint_comm; try 
   apply sublist_disjoint with (l2:= l');
   try apply disjoint_comm...
  Qed.

  Lemma vars_filter_sublist {A B} `{varsable A B}`{EqDec B}:
   forall (l : list A) (l' : list B),
   sublist (vars_filter l l') l.
  Proof with try tauto.
   repeat intro.
   apply vars_filter_in in H1...
  Qed.

  Lemma IMPLsimplifier_Absurd: forall is,
   SAT (ies2ses (fst is)) ->
   IMPLsimplifier is = Absurd ->
   ~IMPL is.
  Proof with try tauto.
   repeat intro.
   destruct H as [rho H].
   generalize (H1 rho);intro.
   simpl in H2. unfold eval_impl_system in H2.
   spec H2. exists rho. rewrite context_override_idem...
   destruct H2 as [rho' H2].
   revert H0.
   unfold IMPLsimplifier.
   destruct is as [ies1 ies2].
   case_eq (wrapped_ses (ies2ses ies1));disc.
   case_eq (wrapped_ses (ies2ses ies2));disc. intros ? ? ? ?.
   case_eq (simpl_equation_system e1);disc. intros ? ?.
   case_eq (subst_list_eqs
            (vars_filter (eqs_substitutions e2)
            (impl_exvars ies1 ++ impl_exvars ies2)) e0);disc. intros ? ?.
   case_eq (simpl_equation_system e3);disc. intros ? ?.
   case_eq (is_empty_eqs e4);intros. inv H8. inv H8.
   repeat intro.
   apply wrapped_ses_Some in H0.  apply H0 in H2.
   apply simpl_equation_system_None in H6. apply H6.
   eapply subst_list_eqs_Some in H5. apply H5 in H2.
   exists ([impl_exvars ies2 => rho']rho)...
   rewrite vars_filter_subst_list.
   eapply sublist_eval. apply vars_filter_sublist.
   apply wrapped_ses_Some in H3.
   apply simpl_equation_system_Some in H4.
   destruct H4 as [H4 _].
   apply H3 in H. apply H4 in H.
   destruct e1 as [l1 l2 l3];simpl in *;
   unfold eval_equation_system in *...
   repeat intro. rewrite in_app_iff...
   repeat intro.
   apply wrapped_ses_Some in H0.
   apply H0 in H2.
   apply subst_list_eqs_None with (rho:= [impl_exvars ies2 => rho']rho)in H5...
   apply vars_filter_subst_list. repeat intro;rewrite in_app_iff...
   apply wrapped_ses_Some in H3. apply H3 in H.
   apply simpl_equation_system_Some in H4.
   destruct H4 as [H4 _]. apply H4 in H.
   eapply sublist_eval. apply vars_filter_sublist.
   destruct e1 as [l1 l2 l3];simpl in *;
   unfold eval_equation_system in *...
   intros;apply wrapped_ses_None with (rho:=[impl_exvars (snd (ies1, ies2)) => rho']rho) in H2...
   intros;apply wrapped_ses_None with (rho:=rho) in H0...
  Qed.

  Lemma is_empty_eqs_valid: forall eqs,
   is_empty_eqs eqs = true -> forall rho, rho|= eqs.
  Proof with try tauto.
   intros. destruct eqs as [l1 l2 l3].
   compute in H. icase l1;icase l2;icase l3.
   compute...
  Qed.

  Lemma IMPLsimplifier_Simpler: forall is,
   IMPLsimplifier is = Simpler tt ->
   forall rho,rho |= is.
  Proof with try tauto.
   intros is H rho H1.
   revert H. unfold IMPLsimplifier.
   destruct is as [ies1 ies2].
   case_eq (wrapped_ses (ies2ses ies1));disc.
   case_eq (wrapped_ses (ies2ses ies2));disc.
   intros ? ? ? ?.
   case_eq (simpl_equation_system e1);disc. intros ? ?.
   case_eq (  subst_list_eqs
    (vars_filter (eqs_substitutions e2)
       (impl_exvars ies1 ++ impl_exvars ies2)) e0);disc. intros ? ?.
   case_eq (simpl_equation_system e3);disc. intros ? ?.
   case_eq (is_empty_eqs e4);intros;disc.
   exists rho. rewrite context_override_idem.
   apply is_empty_eqs_valid with (rho:=rho) in H5.
   apply simpl_equation_system_Some in H4. destruct H4 as [H4 ?].
   apply H4 in H5. 
   apply subst_list_eqs_Some with (rho:=rho) in H3.
   apply H3 in H5.
   apply wrapped_ses_Some in H.
   apply H in H5...
   apply wrapped_ses_Some in H0. 
   destruct H1 as [rho' H1].
   apply H0 in H1.
   apply simpl_equation_system_Some in H2. destruct H2 as [H2 ?].
   apply H2 in H1.
   rewrite <- vars_filter_subst_list with (l:=impl_exvars ies1) (rho':=rho').
   apply sublist_eval with (l':=eqs_substitutions e2).
   apply vars_filter_sublist.
   destruct e2 as [l1 l2 l3];simpl in *;
   unfold eval_equation_system in *...
   repeat intro;rewrite in_app_iff...
   
   intros. apply simpl_equation_system_None in H2.
   elimtype False. apply H2.
   apply wrapped_ses_Some in H0. 
   destruct H1 as [rho' H1]. apply H0 in H1.
   exists ([impl_exvars ies1 => rho']rho)...
  Qed.

  Lemma ses2ies_rewrite: forall l ses,
   ies2ses (ses2ies l ses) = ses.
  Proof with try tauto.
   intros. destruct ses as [l1 l2 l3]...
  Qed.

  Lemma ses2ies_exvars: forall l ses,
   impl_exvars (ses2ies l ses) = l.
  Proof with try tauto.
   intros...
  Qed.

  Lemma IMPLsimplifier_Same: forall is is',
   IMPLsimplifier is = Same is' ->
   forall rho, (rho |= fst is <-> rho |= fst is') /\ (rho |= is <-> rho |= is').
  Proof with try tauto.
   intros.
   revert H. unfold IMPLsimplifier.
   destruct is as [ies1 ies2].
   case_eq (wrapped_ses (ies2ses ies1));disc.
   case_eq (wrapped_ses (ies2ses ies2));disc.
   intros ? ? ? ?.
   case_eq (simpl_equation_system e1);disc. intros ? ?.
   case_eq (  subst_list_eqs
    (vars_filter (eqs_substitutions e2)
       (impl_exvars ies1 ++ impl_exvars ies2)) e0);disc. intros ? ?.
   case_eq (simpl_equation_system e3);disc. intros ? ?.
   case_eq (is_empty_eqs e4);intros;disc.
   inv H5.
   apply wrapped_ses_Some in H.
   apply wrapped_ses_Some in H0.
   apply simpl_equation_system_Some in H1.
   destruct H1 as [H1 _].
   apply simpl_equation_system_Some in H3.
   destruct H3 as [H3 _].
   split;repeat intro;unfold fst,snd in *.
   split;intros. destruct H5 as [rho' H5].
   apply H0 in H5. apply H1 in H5.
   exists rho'. rewrite ses2ies_exvars,ses2ies_rewrite.
   apply unwrapped_ses_eval...
   destruct H5 as [rho' H5].
   rewrite ses2ies_exvars,ses2ies_rewrite in H5.
   apply unwrapped_ses_eval in H5. apply H1 in H5. apply H0 in H5.
   exists rho'...

   split;repeat intro;unfold fst,snd in *.
   destruct H6 as [rho' H6].
   rewrite ses2ies_rewrite in H6.
   rewrite ses2ies_exvars in H6.
   apply unwrapped_ses_eval in H6.
   apply H1 in H6. apply H0 in H6.
   simpl in H5. unfold eval_impl_system in H5.
   spec H5. exists rho'...
   destruct H5 as [rho'' H5].
   exists rho''.
   rewrite ses2ies_rewrite,ses2ies_exvars.
   apply unwrapped_ses_eval.
   apply H3. 
   apply subst_list_eqs_Some with (rho:= [impl_exvars ies2 => rho'']rho)in H2...
   apply H2. apply H...
   apply vars_filter_subst_list.
   repeat intro;rewrite in_app_iff...
   rewrite<- vars_filter_subst_list with (rho':=rho') (l:= impl_exvars ies1).
   2:repeat intro;rewrite in_app_iff...
   apply sublist_eval with (l':=eqs_substitutions e2).
   apply vars_filter_sublist. apply H0 in H6. apply H1 in H6.
   destruct e1 as [l1 l2 l3];simpl in *;
   unfold eval_equation_system in *...
  
   destruct H6 as [rho' H6].
   apply H0 in H6. apply H1 in H6.
   simpl in H5. unfold eval_impl_system in H5.
   unfold fst,snd in *. spec H5.
   exists rho'. rewrite ses2ies_exvars,ses2ies_rewrite.
   apply unwrapped_ses_eval...
   destruct H5 as [rho'' H5].
   rewrite ses2ies_exvars,ses2ies_rewrite in H5.
   apply unwrapped_ses_eval in H5.
   apply H3 in H5. 
   apply subst_list_eqs_Some with (rho:=[impl_exvars ies2 => rho'']rho) in H2.
   apply H2 in H5. apply H in H5.
   exists rho''...
   apply vars_filter_subst_list. repeat intro;rewrite in_app_iff...
   rewrite <-vars_filter_subst_list with (rho':=rho') (l:=impl_exvars ies1).
   2:repeat intro;rewrite in_app_iff...
   apply sublist_eval with (l':=eqs_substitutions e2).
   apply vars_filter_sublist.
   destruct e2 as [l1 l2 l3];simpl in *;
   unfold eval_equation_system in *...   
 Qed.

End Simplifier.
   
   
    

  

(*
  Definition IMPLsimplifier (is : impl_system): result impl_system unit:=
   let (ies1,ies2) := is in
   match ies_simplifier ies1 with
   |None => Simpler tt
   |Some ies1' => match ies_simplifier ies2 with
                  |None => Absurd
                  |Some ies2' => Same (ies1',ies2')
                  end
   end.

  Lemma IMPLsimplifier_Absurd: forall is,
   SAT (ies2ses (fst is)) ->
   IMPLsimplifier is = Absurd ->
   ~IMPL is.
  Proof with try tauto.
   repeat intro.
   destruct H as [rho H].
   spec H1 rho.
   unfold IMPLsimplifier in H0.
   destruct is as [ies1 ies2].
   remember (ies_simplifier ies1).
   remember (ies_simplifier ies2).
   symmetry in Heqo,Heqo0.
   icase o;icase o0.
   apply ies_simplifier_None with (rho:=rho) in Heqo0.
   apply Heqo0. apply H1.
   exists rho. rewrite context_override_idem...
  Qed.

  Lemma IMPLsimplifier_Simpler: forall is,
   IMPLsimplifier is = Simpler tt ->
   IMPL is.
  Proof with try tauto.
   repeat intro.
   unfold IMPLsimplifier in H.
   destruct is as [ies1 ies2].
   remember (ies_simplifier ies1).
   remember (ies_simplifier ies2).
   symmetry in Heqo,Heqo0.
   icase o;icase o0.
   apply ies_simplifier_None with (rho:=a) in Heqo...
   apply ies_simplifier_None with (rho:=a) in Heqo...
  Qed.

  Lemma IMPLsimplifier_Same: forall is is',
   IMPLsimplifier is = Same is' ->
   forall rho, (rho |= fst is <-> rho |= fst is') /\ (rho |= snd is <-> rho |= snd is').
  Proof with try tauto.
   repeat intro.
   unfold IMPLsimplifier in H.
   destruct is as [ies1 ies2].
   remember (ies_simplifier ies1).
   remember (ies_simplifier ies2).
   symmetry in Heqo,Heqo0.
   icase o;icase o0. inv H.
   generalize (ies_simplifier_Some _ _ Heqo rho);intro.
   generalize (ies_simplifier_Some _ _ Heqo0 rho);intro.
   simpl in *...
  Qed.
*)
(*
  Lemma simpl_equation_system_impl_sound: forall eqs sbst eqnl eqs2 eqs2',
    simpl_equation_system eqs = Some (Equation_system sbst eqnl) ->
    simpl_equation_system eqs2 = Some eqs2' ->
    (forall ctx, eval ctx eqnl -> eval ctx eqs2') ->
    forall ctx, eval ctx eqs -> eval ctx eqs2.
  Proof.
    intros. 
    apply simpl_equation_system_Some in H. 
    apply simpl_equation_system_Some in H0. destruct H. destruct H0.
    apply H in H2. destruct H2. simpl in *.
    apply H1 in H5. rewrite <- H0 in H5. trivial.
  Qed.

  Lemma simpl_equation_system_impl_complete: forall eqs eqs',
    (impl eqs eqs') ->
    (exists ctx, eval_equation_system ctx eqs) -> (* needs to be checked by machine *)
    forall sbst eqnl,
      simpl_equation_system eqs = Some (Equation_system sbst eqnl) ->
      exists sbst', exists eqnl',
        simpl_equation_system eqs' = Some (Equation_system sbst' eqnl') /\
        (forall ctx, (eval ctx eqnl  /\ eval ctx sbst) -> 
                     eval ctx eqnl').
  Proof.
    intros. destruct H0 as [ctx ?].
    apply simpl_equation_system_Some in H1. destruct H1.
    case_eq (simpl_equation_system eqs'); intro. destruct e as [sbst' eqnl']. exists sbst'. exists eqnl'. split; auto.
    2: apply simpl_equation_system_None in H3; destruct H3; exists ctx; apply H; auto.
    clear H0 ctx.
    intros. apply simpl_equation_system_Some in H3. destruct H3.
    rewrite <- H2 in H0. destruct H0.
    rewrite upd_subst_list_equiv in H0; trivial.
    apply H in H0.
    apply H3. trivial.
  Qed.

*)
































(*
 Definition subst_instance := (var*object)%type.
 Instance subst_eval : evalable context subst_instance.
 Proof with try tauto.
  constructor. intros rho subst.
  apply (rho (fst subst) = get rho (snd subst)).
 Defined.

 Inductive result (A : Type) : Type :=
 |valid_res : result A
 |invalid_res : result A
 |normal_res : A -> result A.
 Implicit Arguments valid_res [A].
 Implicit Arguments invalid_res [A].
 Implicit Arguments normal_res [A].
 
 Definition eql2subst (eql : equality) : result (subst_instance) :=
  match eql with
  |(Vobject v, obj)
  |(obj, Vobject v)=> normal_res (v,obj)
  |(Cobject c1, Cobject c2) => match eq_dec c1 c2 with
                               |left _ => valid_res
                               |right _ => invalid_res
                               end
  end.

 Definition valid {A B} `{evalable A B} := fun (b : B) =>
  forall (rho : A), rho |= b.
 Definition invalid {A B} `{evalable A B} := fun (b : B) =>
  forall (rho : A), ~rho |= b.
 Definition equiv_eval {A B B'} `{evalable A B} `{evalable A B'} := 
  fun (b : B) (b' : B')=> forall rho, rho |= b <-> rho |= b'.
  
 Fixpoint eql2subst_list (l : list equality) : option (list (subst_instance)) :=
  match l with
  |nil => Some nil
  |eql::l' => match eql2subst eql with
              |normal_res subst' => match eql2subst_list l' with 
                                    |Some l'' => Some (subst'::l'')
                                    |None => None
                                    end
              |valid_res => eql2subst_list l'
              |invalid_res => None
              end
  end.

  Lemma eql2subst_valid: forall eql,
   eql2subst eql = valid_res ->
   valid eql.
  Proof with try tauto.
   repeat intro.
   destruct eql as [obj1 obj2].
   icase obj1;icase obj2;inv H.
   destruct (eq_dec s0 s1)...
   inv H1.
  Qed.

  Lemma eql2subst_invalid: forall eql,
   eql2subst eql = invalid_res ->
   invalid eql.
  Proof with try tauto.
   repeat intro.
   destruct eql as [obj1 obj2].
   icase obj1;icase obj2;inv H.
   destruct (eq_dec s0 s1)...
   inv H2.
  Qed.
   
  Lemma eql2subst_normal: forall eql subst,
   eql2subst eql = normal_res subst ->
   equiv_eval eql subst.
  Proof with try tauto.
   repeat intro.
   destruct eql as [obj1 obj2].
   icase obj1;icase obj2;inv H;simpl...
   split;intros;subst...
   destruct (eq_dec s0 s1);inv H1...
  Qed.

  Lemma eql2subst_list_None: forall l,
   eql2subst_list l = None -> invalid l.
  Proof with try tauto.
   induction l;repeat intro;inv H.
   destruct H0.
   remember (eql2subst a). symmetry in Heqr.
   destruct r;inv H2.
   spec IHl H3 rho. apply IHl...
   apply eql2subst_invalid in Heqr.
   spec Heqr rho. apply Heqr...
   icase (eql2subst_list l);inv H3.
   detach IHl... spec IHl rho. apply IHl...
  Qed.

  Lemma eql2subst_list_Some: forall l l',
   eql2subst_list l = Some l' -> equiv_eval l l'.
  
*)   
    
  
