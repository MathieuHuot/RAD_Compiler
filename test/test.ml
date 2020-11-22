open Syntax.Operators
open Syntax.SourceLanguage
open Syntax.PrettyPrinter
open Transforms.Anf
open Syntax.Rewrite

let x1 = ("x",1);;
let x2 = ("x",2);;
let var1 = Var(x1,Real);;
let var2 = Var(x2,Real);;
let f1 = Apply1(Cos, Const 7.);; 
let f2 = Let(x1,Real,Apply2(Plus, Const 5.,var2),Apply1(Sin,var1));;
let f3 = Apply2(Plus,Const 7.,Const 8.);;
let f4 = Apply1(Exp, Const 6.);;
let f5 = Apply1(Sin, var1);;
let f6 = Apply1(Cos, Const 0.716814692820);;
let f7 = Apply1(Sin, Var(Syntax.Vars.fresh(),Real));;

(* Random term generator tests *)
Lwt_io.print "random term:\n";;
Random.self_init();;
SourcePrinter.prettyPrinter(anf(Syntax.Generator.sourceSynGen(100)));;
Lwt_io.print "end random term\n";;
(* Printers tests*)

SourcePrinter.prettyPrinter f1;;
SourcePrinter.prettyPrinter f2;;
SourcePrinter.prettyPrinter f7;;

(* Interpreters tests*)
let printVal expr context = Lwt_io.print ((string_of_float (interpret expr context))^"\n");;
printVal (Const 7.) [] ;;
printVal f1 [];;
printVal f3 [];;
printVal f4 [];;
printVal f5 [(x1,Real,Const 0.)];;
printVal f5 [(x1,Real,Const 2.)];;
printVal f5 [(x1,Real,Const 8.283185307)];;
printVal f6 [];; 

(* capture avoiding substitutions tests *)


(* typing tests *)


(* ANF tests *)


(* forward mode tests *)


(* optimisation tests *)


(* semi-naive reverse mode tests *)

