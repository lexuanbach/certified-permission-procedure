Require Import msl.msl_standard.
Require Import share_dec_base.
Require Import share_equation_system.
Require Import fbool_solver.
Require Import bool_solver.
Require Import partition_modules.
Require Import share_solver.
Require Import share_dec_interface.

Module Solver_with_partition 
  (sv : SV)
  (Import es : EQUATION_SYSTEM sv with Module dom := Share_Domain)
  (bf : BOOL_FORMULA sv)
  (bsf : BF_SOLVER sv bf) 
  <: SOLVER sv es.

 Module basic_solver := Solver sv es bf bsf.
 Module esf := System_Features sv es.
 Module partition_fun := System_Partition sv es esf.
 Import partition_fun.

 Definition SATsolver (ses : sat_equation_system) : bool :=
  basic_solver.eval_conjunct basic_solver.SATsolver (ses_partition ses).

 Lemma SATsolver_correct : forall ses, SATsolver ses = true <-> SAT ses.
 Proof with try tauto.
  intros. rewrite ses_partition_correct.
  unfold SATsolver.
  rewrite basic_solver.eval_conjunct_true.
  split;intros.
  spec H ses' H0.
  apply basic_solver.SATsolver_correct...
  spec H a H0.
  apply basic_solver.SATsolver_correct...
 Qed.

 Definition IMPLsolver (is : impl_system) : bool :=
  if (SATsolver (ies2ses (fst is))) then
   basic_solver.eval_conjunct basic_solver.IMPLsolver (impl_partition is)
  else true.

 Lemma IMPLsolver_correct : forall is, IMPLsolver is = true <-> IMPL is.
 Proof with try tauto.
  intros. unfold IMPLsolver.
  case_eq (SATsolver (ies2ses (fst is)));intro.
  apply SATsolver_correct in H.
  rewrite basic_solver.eval_conjunct_true.
  split;intros.
  apply is_partition_correct1. intros.
  spec H0 is' H1.
  apply basic_solver.IMPLsolver_correct in H0...
  apply basic_solver.IMPLsolver_correct...
  eapply is_partition_correct2;eauto.
  split;intros...
  assert (~SAT (ies2ses (fst is))).
   intro. apply SATsolver_correct in H1.
   rewrite H1 in H;inv H.
  repeat intro. elimtype False.
  apply H1. destruct H2.
  exists ([impl_exvars (fst is) => x]rho)...
 Qed.

End Solver_with_partition. 
(*

Extraction Language Ocaml.

Set Extraction AutoInline.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
 
Extraction Inline proj1_sig sigT_of_sig projT1.
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive prod => "(*)"  [ "(,)" ].
Extract Inductive sigT => "(*)"  [ "(,)" ].
Extract Inductive nat => "int"
  [ "0" "(fun x -> x + 1)" ]
  "(fun zero succ n ->
      if n=0 then zero () else succ (n-1))".

Extraction "Solver_new.ml" Solver_with_partition.
*)
