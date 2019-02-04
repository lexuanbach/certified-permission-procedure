(*Check basic properties of shares*)
Add LoadPath "..".
Require Import msl.msl_standard.
Require Import share_dec_base.
Require Import share_equation_system.
Require Import share_simplifier.
Require Import share_solver.
Require Import fbool_solver.
Require Import share_solver_with_partition.

Module Tester.

 Module es := Equation_system sv_nat Share_Domain.
 Module esf := System_Features sv_nat es.
 Module bf := Bool_formula sv_nat.
 Module bsf := BF_solver sv_nat bf.
 Import es.
 Module solver := Solver_with_partition sv_nat es bf bsf.
 Import solver.

 Definition a : var := 1.
 Definition b : var := 2.
 Definition c : var := 3.
 Definition c' : var := 4.
 Definition d : var := 5.
 Definition e : var := 6.
 Definition f : var := 7.
 Definition e' : var := 8.
 Definition a' : var := 9.
 Definition v1 : var := 10.
 Definition v2 : var := 11.
 Definition v3 : var := 12.
 Definition v4 : var := 13.
 Definition eqn0 : equation := (Vobject b, Vobject a, Vobject c).
 Definition eqn1 : equation := (Vobject a, Vobject b, Vobject c).
 Definition eqn2 : equation := (Vobject a, Vobject b, Vobject c').
 Definition eqn3 : equation := (Vobject c, Vobject d, Vobject e).
 Definition eqn4 : equation := (Vobject b, Vobject d, Vobject f).
 Definition eqn5 : equation := (Vobject a, Vobject f, Vobject e).
 Definition eqn6 : equation := (Vobject a', Vobject b, Vobject c).
 Definition eqn7 : equation := (Vobject a, Vobject a, Vobject b).
 Definition eqn8 : equation := (Vobject a, Vobject b, Vobject a).
 Definition eqn9 : equation := (Vobject d, Vobject f, Vobject c).
 Definition eqn10 : equation := (Vobject v1, Vobject v2, Vobject a).
 Definition eqn11 : equation := (Vobject v3, Vobject v4, Vobject b).
 Definition eqn12 : equation := (Vobject v1, Vobject v3, Vobject d).
 Definition eqn13 : equation := (Vobject v2, Vobject v4, Vobject f).
 Definition eqn14 : equation := (Vobject a, Cobject Share.bot, Vobject a).

 Definition eql1 : equality := (Vobject c, Vobject c').
 Definition eql2 : equality := (Vobject e, Vobject e').
 Definition eql3 : equality := (Vobject a, Vobject a').
 Definition eql4 : equality := (Vobject a, Vobject b).

 Definition comm : impl_system := (Impl_equation_system nil nil nil (eqn1::nil),Impl_equation_system nil nil nil (eqn0::nil)).
 Definition assoc : impl_system := (Impl_equation_system nil nil nil (eqn1::eqn3::nil),Impl_equation_system (f::nil) nil nil (eqn4::eqn5::nil)).
 Definition func : impl_system := (Impl_equation_system nil nil nil (eqn1::eqn2::nil),Impl_equation_system nil nil (eql1::nil) nil).
 Definition canc : impl_system := (Impl_equation_system nil nil nil (eqn1::eqn6::nil),Impl_equation_system nil nil (eql3::nil) nil).
 Definition dis : impl_system := (Impl_equation_system nil nil nil (eqn7::nil),Impl_equation_system nil nil (eql4::nil) nil).
 Definition unit : impl_system := (Impl_equation_system nil nil nil nil,Impl_equation_system (b::nil) nil nil (eqn8::nil)).
 Definition infi : impl_system := (Impl_equation_system nil (c::nil) nil nil,Impl_equation_system (a::b::nil) (a::b::nil) nil (eqn1::nil)).
 Definition cross : impl_system := (Impl_equation_system nil nil nil (eqn1::eqn9::nil),Impl_equation_system (v1::v2::v3::v4::nil) nil nil (eqn10::eqn11::eqn12::eqn13::nil)).
 Definition crossnz : impl_system := (Impl_equation_system nil (a::b::d::f::nil) nil (eqn1::eqn9::nil),Impl_equation_system (v1::v2::v3::v4::nil) (v1::v2::v3::v4::nil) nil (eqn10::eqn11::eqn12::eqn13::nil)).
 Definition unit' : impl_system := (Impl_equation_system nil nil nil nil,Impl_equation_system nil nil nil (eqn14::nil)).

 Definition properties := comm :: assoc :: func :: canc :: dis :: unit :: infi :: cross :: nil.

 Time Eval compute in (map IMPLsolver properties).

End Tester.
