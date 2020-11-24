open Syntax.Operators
open Syntax.SourceLanguage
open Syntax.TargetLanguage
open Syntax.PrettyPrinter
(* open Transforms.Anf *)
open Transforms.ReverseMode
open Rewrite.Catamorphisms
(* open Rewrite.Optimisations *)

(* let x1 = ("x",1);;
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
printVal f6 [];;  *)

(* capture avoiding substitutions tests *)


(* typing tests *)


(* ANF tests *)


(* forward mode tests *)


(* optimisation tests *)


(* semi-naive reverse mode tests *)

let x11 = ("x",1);;
let var11 = Syntax.SourceLanguage.Var(x11,Real);;
let f11 = Syntax.SourceLanguage.Apply1(Exp, var11);;
let cst : targetSyn list = [Const(0.);Const(1.)]
let f12 = semiNaiveReverseAD [(x11,Real)] f11;;
let f13 = match f12 with | Pair(_,x)-> App(x,cst) | _ -> failwith "f12 wrong format" ;;
let f14 = TargetCata.catamorphism [1;2;3;4;5;7;8;9;10;11;12;13;14;15;16] f13;;
let f15 = TargetCata.iterate 10 [1;2;3;4;5;7;8;9;10;11;12;13;14;15;16;17] f13;;
Lwt_io.print "variable:\n";;
SourcePrinter.prettyPrinter(var11);;
Lwt_io.print "term:\n";;
SourcePrinter.prettyPrinter(f11);;
Lwt_io.print "reverse derivative macro of term:\n";;
TargetPrinter.prettyPrinter(f12);;
Lwt_io.print "derivative of term:\n";;
TargetPrinter.prettyPrinter(f13);;
Lwt_io.print "partially reduced term:\n";;
TargetPrinter.prettyPrinter(f14);;
Lwt_io.print "fully reduced term:\n";;
TargetPrinter.prettyPrinter(f15);;

(* let f14 = deadVarsElim f13;; *)