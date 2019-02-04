Require Import msl.msl_standard.
Require Import share_dec_base.
Require Import share_equation_system.
Require Import base_properties.

  Inductive result (A B : Type) : Type := 
    | Absurd (* reach contradiction *)
    | Simpler : B -> result A B
    | Same : A -> result A B.
  Implicit Arguments Absurd [A B].
  Implicit Arguments Simpler [A B].
  Implicit Arguments Same [A B].

Module Type SHARE_TO_BOOL (sv : SV)
                          (ses : EQUATION_SYSTEM sv with Module dom := Share_Domain)
                          (sesf : SYSTEM_FEATURES sv ses)
                          (bes : EQUATION_SYSTEM sv with Module dom := Bool_Domain)
                          (besf : SYSTEM_FEATURES sv bes).

 Class S2B (A B : Type):= Transformation {
  transform : A -> B
 }.

 Implicit Arguments Transformation [A B].

 Parameter Sses2bses : @S2B ses.sat_equation_system bes.sat_equation_system.
 Parameter Sis2bis : @S2B ses.impl_system bes.impl_system.

 Axiom nSAT_transform_correct: forall (ses : ses.sat_equation_system),
  |ses| = 0 ->
  (sesf.nSAT ses <-> besf.nSAT (transform ses)).
 Axiom sSAT_transform_correct: forall (ses : ses.sat_equation_system) v,
  |ses| = 0 ->
  (sesf.sSAT ses v <-> besf.sSAT (transform ses) v).
 Axiom nIMPL_transform_correct: forall is,
  |is| = 0 ->
  (sesf.nIMPL is <-> besf.nIMPL (transform is)).
 Axiom zIMPL_transform_correct: forall is x,
  |is| = 0 ->
  (sesf.zIMPL is x <-> besf.zIMPL (transform is) x).
 Axiom sIMPL_transform_correct: forall is x y,
  |is| = 0 ->
  sesf.nIMPL is ->
  (sesf.sIMPL is x y <-> besf.sIMPL (transform is) x y).

End SHARE_TO_BOOL.

Module Type SIMPL_DOM_SPEC.

  Declare Module dom : DOMAIN.
  Import dom.
 
  Parameter top : e.
  Axiom bot_join : forall t, join bot t t.
  Axiom join_top : forall t1 t2, join top t1 t2 -> t1 = bot /\ t2 = top.
  Axiom join_comm: forall {a b c}, join a b c -> join b a c.
  Definition unit_for := fun e a => join e a a.
  Parameter add : e -> e -> option e.
  Parameter sub : e -> e -> option e.


  Definition identity := fun (e : e) => 
   forall a b, join e a b -> a = b. 
  Axiom unit_identity: forall e b, unit_for e b -> identity e.
  Axiom identity_share_bot : forall s, identity s -> s = bot.
  Axiom join_canc : forall {a1 a2 b c}, join a1 b c -> join a2 b c -> a1 = a2.
  Axiom sub_join : forall t1 t2 t3, sub t1 t2 = Some t3 <-> join t2 t3 t1.
  Axiom add_join : forall t1 t2 t3, add t1 t2 = Some t3 <-> join t1 t2 t3.
  Axiom join_eq : forall x y z z', join x y z -> join x y z' -> z = z'.
  Axiom split_identity : forall a b {c}, join a b c -> identity c -> identity a.
  Axiom bot_identity: identity bot.
  Axiom join_self: forall {a b : e}, join a a b -> a = b.
  Axiom nontrivial: top <> bot.

End SIMPL_DOM_SPEC.

Module Type SIMPLIFIER (sv : SV)(dom' : DOMAIN)
                       (Import es : EQUATION_SYSTEM sv with Module dom := dom')
                       (Import spec : SIMPL_DOM_SPEC with Module dom := dom').

 Parameter SATsimplifier : sat_equation_system -> option sat_equation_system.
 Parameter IMPLsimplifier : impl_system -> result impl_system unit.

 Axiom SATsimplifier_None: forall ses,
  SATsimplifier ses = None -> forall rho,~rho |= ses.
 Axiom SATsimplifier_Some: forall ses ses',
  SATsimplifier ses = Some ses' -> 
  forall rho, rho|= ses <-> rho |= ses'.
 Axiom IMPLsimplifier_Absurd: forall is,
   SAT (ies2ses (fst is)) ->
   IMPLsimplifier is = Absurd ->
   ~IMPL is.
 Axiom IMPLsimplifier_Simpler: forall is,
   IMPLsimplifier is = Simpler tt ->
   forall rho, rho |= is.
 Axiom IMPLsimplifier_Same: forall is is',
   IMPLsimplifier is = Same is' ->
   forall rho, (rho |= fst is <-> rho |= fst is') /\
  (rho |= is <-> rho |= is').

 (*Other sanity checks?*)
End SIMPLIFIER.

Module Type BOUNDER (sv : SV)
                    (Import es : EQUATION_SYSTEM sv with Module dom := Share_Domain).

 Parameter SATbounder : sat_equation_system -> option sat_equation_system.
 Parameter IMPLbounder : impl_system -> result impl_system unit.

 Axiom SATbounder_None: forall ses,
  SATbounder ses = None -> forall rho,~rho |= ses.
 Axiom SATbounder_Some: forall ses ses',
  SATbounder ses = Some ses' -> 
  forall rho, rho|= ses <-> rho |= ses'.
 Axiom IMPLbounder_Absurd: forall is,
   SAT (ies2ses (fst is)) ->
   IMPLbounder is = Absurd ->
   ~IMPL is.
 Axiom IMPLbounder_Simpler: forall is,
   IMPLbounder is = Simpler tt ->
   forall rho, rho |= is.
 Axiom IMPLbounder_Same: forall is is',
   IMPLbounder is = Same is' ->
   forall rho, (rho |= fst is <-> rho |= fst is') /\
  (rho |= snd is <-> rho |= snd is').

End BOUNDER.

Module Type SAT_DECOMPOSE (sv : SV)
                          (Import es : EQUATION_SYSTEM sv with Module dom := Share_Domain)
                          (Import esf : SYSTEM_FEATURES sv es).


 Parameter SATdecompose : sat_equation_system -> list sat_equation_system.

 Axiom nSAT_decompose_eval: forall ses,
  nSAT ses <-> (forall ses', In ses' (SATdecompose ses) -> nSAT ses').
 Axiom sSAT_decompose_eval: forall ses x,
  nSAT ses ->
  (sSAT ses x <-> (exists ses', In ses' (SATdecompose ses) /\ sSAT ses' x)).
 Axiom SAT_decompose_height: forall ses ses',
  In ses' (SATdecompose ses) -> |ses'| = 0 .
 Axiom SAT_decompose_not_nil: forall ses,
  SATdecompose ses <> nil.

End SAT_DECOMPOSE.

Module Type IMPL_DECOMPOSE (sv : SV)
                           (Import es : EQUATION_SYSTEM sv with Module dom := Share_Domain)
                           (Import esf : SYSTEM_FEATURES sv es).

 Parameter IMPLdecompose : impl_system -> list impl_system.

 Axiom nIMPL_decompose_eval: forall (is:impl_system),
  nSAT (ies2ses (fst is)) ->
  (nIMPL is <-> forall (is':impl_system), In is' (IMPLdecompose is) -> nIMPL is').
 Axiom zIMPL_decompose_eval: forall (is:impl_system) y,   
  nSAT (ies2ses (fst is)) ->
  nIMPL is  ->
  (zIMPL is y <-> exists (is':impl_system), In is' (IMPLdecompose is) /\ zIMPL is' y).
 Axiom sIMPL_decompose_eval: forall (is:impl_system) x y,
  nSAT (ies2ses (fst is)) ->
  nIMPL is ->
  ~zIMPL is y ->
  (sIMPL is x y <-> forall (is':impl_system), In is' (IMPLdecompose is) -> sIMPL is' x y).
 Axiom IMPL_decompose_height : forall (is is':impl_system),
  In is' (IMPLdecompose is) -> 
  |is'| = 0.
 Axiom IMPL_decompose_not_nil: forall is,
  IMPLdecompose is <> nil.

End IMPL_DECOMPOSE. 

Module Type SAT_CORRECTNESS (sv : SV)
                            (Import es : EQUATION_SYSTEM sv with Module dom := Share_Domain)
                            (Import esf : SYSTEM_FEATURES sv es).
 
 Axiom SAT_nSAT: forall ses,
  SAT ses -> nSAT ses.
 Axiom SAT_nzvars_separate: forall ses,
  nSAT ses ->
  (SAT ses <-> forall x, In x (sat_nzvars ses) -> sSAT ses x).

End SAT_CORRECTNESS.

Module Type IMPL_CORRECTNESS (sv : SV)
                             (Import es : EQUATION_SYSTEM sv with Module dom := Share_Domain)
                             (Import esf : SYSTEM_FEATURES sv es).

 Definition sIMPL_Cond (is : impl_system): Prop :=
  forall y, In y (impl_nzvars (snd is)) ->
  exists x, In x (impl_nzvars (fst is)) /\ sIMPL is x y.
 Definition zIMPL_Cond (is : impl_system) : Prop :=
  forall y, In y (impl_nzvars (snd is)) -> zIMPL is y.

 Axiom IMPL_trivial: forall is,
  ~SAT (ies2ses (fst is)) ->
  IMPL is.
 Axiom IMPL_nIMPL: forall is,
  SAT (ies2ses (fst is)) ->
  IMPL is ->
  nIMPL is.
 Axiom zIMPL_sIMPL: forall is x y,
  zIMPL is y -> sIMPL is x y.
 Axiom IMPL_case1: forall is,
  impl_nzvars (fst is) <> nil ->
  impl_nzvars (snd is) <> nil ->
  (IMPL is <-> sIMPL_Cond is).
 Axiom IMPL_case2: forall is,
  impl_nzvars (snd is) <> nil ->
  impl_nzvars (fst is) = nil ->
  (IMPL is <-> zIMPL_Cond is).
 Axiom IMPL_case3: forall is,
  impl_nzvars (snd is) = nil -> 
  SAT (ies2ses (fst is)) ->
  (IMPL is <-> nIMPL is).

End IMPL_CORRECTNESS.

Module Type BOOL_FORMULA (sv : SV).

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

 Parameter bF_eq_dec: EqDec bF.

 Axiom bF_valid_rewrite: forall (f : bF),
  valid f <-> forall rho, beval rho f = true.
 Axiom bF_unsat_rewrite: forall (f : bF),
  unsat f <-> forall rho, beval rho f = false.
 Axiom bsize_bsubst : forall v b f,
  bsize (bsubst f v b) = bsize f.
 Axiom beval_bsubst: forall f rho v b,
  beval rho (bsubst f v b) = beval (upd rho v b) f.
 Axiom bsubst_id: forall f v b,
  ~In v (vars f) ->
  bsubst f v b = f.
 Axiom bsubst_reduce: forall v b b' f,
  bsubst (bsubst f v b) v b' = bsubst f v b.
 Axiom bsubst_comm: forall v v' b b' f,
  v <> v' ->
  bsubst (bsubst f v b) v' b' = bsubst (bsubst f v' b') v b.
 Axiom bsubst_sublist: forall v b f,
  sublist (vars (bsubst f v b)) (vars f).
 Axiom bsubst_in: forall f v v' b,
  v' <> v ->
  In v' (vars f) ->
  In v' (vars (bsubst f v b)).
 Axiom bsubst_not_free_id: forall v b f,
  not_free v (bsubst f v b).
 Axiom bsubst_not_free_diff: forall v v' b f,
  v <> v' ->
  (not_free v (bsubst f v' b) <-> not_free v f).
 Axiom bsubst_upd_reduce: forall f rho v b b',
  beval (upd rho v b) (bsubst f v b') = beval rho (bsubst f v b').
 Axiom beval_upd_not_in: forall f v b rho,
  ~In v (vars f) ->
  beval (upd rho v b) f = beval rho f.
 Axiom not_free_upd: forall f v rho,
   not_free v f -> forall b, beval (upd rho v b) f = beval rho f.
 Axiom not_free_trivial: forall bf v,
  ~In v (vars bf) -> not_free v bf.
 Axiom full_quan_andF: forall f1 f2,
  full_quan (andF f1 f2) <-> full_quan f1 /\ full_quan f2.
 Axiom full_quan_orF: forall f1 f2,
  full_quan (orF f1 f2) <-> full_quan f1 /\ full_quan f2.
 Axiom full_quan_implF: forall f1 f2,
  full_quan (implF f1 f2) <-> full_quan f1 /\ full_quan f2.
 Axiom full_quan_negF: forall f,
  full_quan (negF f) <-> full_quan f.
 Axiom full_quan_exF: forall f v b,
  full_quan (exF v f) <-> full_quan (bsubst f v b).
 Axiom full_quan_allF: forall f v b,
  full_quan (allF v f) <-> full_quan (bsubst f v b).
 Axiom full_quan_case: forall f,
  full_quan f ->
  (valid f \/ unsat f).

End BOOL_FORMULA.

Module Type BF_SOLVER (sv : SV) (Import bf : BOOL_FORMULA sv).

  Parameter bsolver : bF -> option bool.

  Axiom bsolver_Some: forall f,
   full_quan f ->
   exists b, bsolver f = Some b. 
  Axiom bsolver_unsat: forall f,
   full_quan f ->
   (bsolver f = Some false <-> unsat f).
  Axiom bsolver_valid: forall f,
  full_quan f ->
  (bsolver f = Some true <-> valid f).

End BF_SOLVER.

Module Type INTERPRETER (sv : SV)
                        (Import es : EQUATION_SYSTEM sv with Module dom := Bool_Domain)
                        (Import bf : BOOL_FORMULA sv).
 
 Module sys_features := System_Features sv es.
 Import sys_features.

 Class B2F (A B : Type):= Interpret {
  interpret : A -> B
 }.
 Implicit Arguments Interpret [A B].
 
 Parameter b2f_ses : @B2F sat_equation_system bF .
 Parameter b2f_ies : @B2F impl_equation_system bF.
 Definition is_int := fun (is : impl_system) =>
  let (ies1,ies2) := is in
  let f1 := interpret (ies1) in
  let f2 := interpret (ies2) in
   implF f1 f2.
 Instance b2f_is : B2F _ _ := Interpret is_int.

 Parameter exF_quan : list var -> bF -> bF.
 Parameter allF_quan : list var -> bF -> bF.

 Axiom exF_quan_vars: forall l f v,
  In v (vars (exF_quan l f)) <-> In v (l++vars f).
 Axiom allF_quan_vars: forall l f v,
  In v (vars (allF_quan l f)) <-> In v (l++vars f).
 Axiom exF_quan_In: forall l bf v,
  In v l ->
  not_free v (exF_quan l bf).
 Axiom exF_quan_In_iff: forall l bf v,
  not_free v (exF_quan l bf) <-> (In v l \/ not_free v bf).
 Axiom allF_quan_In: forall l bf v,
  In v l ->
  not_free v (allF_quan l bf).
 Axiom allF_quan_In_iff: forall l bf v,
  not_free v (allF_quan l bf) <-> (In v l \/ not_free v bf).
 Axiom exF_quan_beval: forall l f (rho:context),
  beval rho (exF_quan l f) = true <-> 
  exists rho', beval ([l => rho']rho) f = true.
 Axiom allF_quan_beval: forall l f (rho:context),
  beval rho (allF_quan l f) = true <-> 
  forall rho', beval ([l => rho']rho) f = true.

 Definition vars_interpret_spec (A : Type) `{@B2F A bF} `{varsable A var}:= 
  forall a, sublist (vars (interpret a)) (vars a).
 Class vars_interpret_prop (A : Type) `{@B2F A bF} `{varsable A var} := Vars_interpret_prop {
  vars_int : vars_interpret_spec A
 }.

 Parameter ses_int_vars : vars_interpret_prop sat_equation_system.
 Parameter ies_int_vars : vars_interpret_prop impl_equation_system.
 Parameter is_int_vars : vars_interpret_prop impl_system.

 Definition beval_interpret_spec (A : Type) `{@B2F A bF} `{evalable context A}:=
  forall a rho, rho |= a <-> beval rho (interpret a) = true.

 Class beval_interpret_prop (A : Type) `{@B2F A bF} `{evalable context A} := Beval_interpret_prop {
  beval_int : beval_interpret_spec A
 }.

 Parameter ses_int_prop : beval_interpret_prop sat_equation_system.
 Parameter ies_int_prop : beval_interpret_prop impl_equation_system.
 Parameter is_int_prop : beval_interpret_prop impl_system.

 Axiom not_free_ies: forall v (ies : impl_equation_system),
  In v (vars (interpret ies)) ->
  (In v (impl_exvars ies) <-> not_free v (interpret ies)).

End INTERPRETER.

Module Type BOOL_SOLVER (sv : SV) (Import bf : BOOL_FORMULA sv)
                        (Import es : EQUATION_SYSTEM sv with Module dom := Bool_Domain).

 Parameter SATbsolver : sat_equation_system -> bool.
 Parameter IMPLbsolver : impl_system -> bool.

 Axiom SATbsolver_correct: forall (ses : sat_equation_system),
  SAT ses <-> SATbsolver ses = true.
 Axiom IMPLbsolver_correct : forall (ies : impl_system),
  IMPL ies <-> IMPLbsolver ies = true.

End BOOL_SOLVER.

Module Type SOLVER (sv : SV)
                   (Import es : EQUATION_SYSTEM sv with Module dom := Share_Domain).

 Parameter SATsolver : sat_equation_system -> bool.
 Parameter IMPLsolver : impl_system -> bool.

 Axiom SATsolver_correct : forall ses, SATsolver ses = true <-> SAT ses.
 Axiom IMPLsolver_correct : forall is, IMPLsolver is = true <-> IMPL is.

End SOLVER.


 
  
 