open Syntax.Operators
open Syntax.SourceLanguage
open Syntax.TargetLanguage
open Syntax.PrettyPrinter
open Transforms.Anf
open Transforms.ReverseMode
open Rewrite.Catamorphisms
open Transforms.ForwardMode
open Rewrite.Optimisations

(* Helpers *)
let rec unfold_right f init =
  match f init with
  | None -> []
  | Some (x, next) -> x :: unfold_right f next

let range n =
  let irange x = if x > n then None else Some (x, x + 1) in
  unfold_right irange 1

let nb_opti = 27
let nb_opti_iterations = 200 

(* Random term generator tests *)
let x=2;;
Lwt_io.print "random term:\n";;
Random.self_init();;
SourcePrinter.prettyPrinter(anf(Syntax.Generator.sourceSynGen(10)));;
Lwt_io.print "end random term\n";;
Lwt_io.print "\n\n";;

(* Some terms for tests *)

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

(* Interpreters tests*)

let printVal expr context = TargetPrinter.prettyPrinter (interpret expr context);;
printVal (Const 7.) [] ;;
printVal f1 [];;
printVal f3 [];;
printVal f4 [];;
printVal f5 [(x1,Real,Const 0.)];;
printVal f5 [(x1,Real,Const 2.)];;
printVal f5 [(x1,Real,Const 8.283185307)];;
printVal f6 ([] : Syntax.TargetLanguage.context);; 
Lwt_io.print "\n\n";;

(* capture avoiding substitutions tests *)

OUnit2.assert_raises (Failure("trying to substitute a bound variable")) (fun () -> subst x1 Real f1 f2);;

(* typing tests *)

OUnit2.assert_equal (typeTarget var1) (Some(Real));;
OUnit2.assert_equal (typeTarget var2) (Some(Real));;
OUnit2.assert_equal (typeTarget f1) (Some(Real));;
OUnit2.assert_equal (typeTarget f2) (Some(Real));;
OUnit2.assert_equal (typeTarget f3) (Some(Real));;
OUnit2.assert_equal (typeTarget f4) (Some(Real));;
OUnit2.assert_equal (typeTarget f5) (Some(Real));;
OUnit2.assert_equal (typeTarget f6) (Some(Real));;
OUnit2.assert_equal (typeTarget f7) (Some(Real));;
let f8 = Apply1(Sin,Tuple([Const 2.;Const 3.]));;
OUnit2.assert_equal (typeTarget f8) None;;
let f9 = Apply1(Sin,Fun([(x1,Real)],Var(x1,Real)));;
OUnit2.assert_equal (typeTarget f9) None;;

(* ANF tests *)


(* forward mode tests *)

let f7 : sourceSyn = Apply1(Sin, Var(Syntax.Vars.fresh(),Real));;
let f8 = forwardAD f7;;
let f9 = TargetCata.iterate nb_opti_iterations (range nb_opti) f8;;
Lwt_io.print "Term:\n";;
SourcePrinter.prettyPrinter(f7);;
Lwt_io.print "Forward derivative of term:\n";;
TargetPrinter.prettyPrinter(f8);;
Lwt_io.print "Reduced derivative of term:\n";;
TargetPrinter.prettyPrinter(f9);;
Lwt_io.print "\n\n";;

let f6 = Syntax.Generator.sourceSynGen(5);;
let f7 : sourceSyn = anf(f6);;
let f8 = forwardAD f7;;
let f9 = TargetCata.iterate nb_opti_iterations (range nb_opti) f8;;
Lwt_io.print "Term:\n";;
SourcePrinter.prettyPrinter(f6);;
Lwt_io.print "\n";;
Lwt_io.print "Anf Term:\n";;
SourcePrinter.prettyPrinter(f7);;
Lwt_io.print "\n";;
Lwt_io.print "Forward derivative of term:\n";;
TargetPrinter.prettyPrinter(f8);;
Lwt_io.print "\n";;
Lwt_io.print "Reduced derivative of term:\n";;
TargetPrinter.prettyPrinter(f9);;
Lwt_io.print "\n\n";;

(* optimisation tests *)


(* reverse mode tests *)

let x11 = ("x",1);;
let var11 : sourceSyn = Var(x11,Real);;
let f11 : sourceSyn = Apply1(Exp, var11);;
let cst1 : targetSyn list = [Const(0.);Const(1.)]
let f12 = semiNaiveReverseAD [(x11,Real)] f11;;
let f13 = match f12 with | Pair(_,x)-> App(x,cst1) | _ -> failwith "f12 wrong format" ;;
let f14 = TargetCata.catamorphism (range nb_opti) f13;;
let f15 = TargetCata.iterate 10 (range nb_opti) f13;;
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
Lwt_io.print "\n\n";;

let x12 = ("x",2);;
let var12 : sourceSyn = Var(x12,Real);;
let f21 : sourceSyn = Apply2(Plus, var11,var12);;
let f22 = anf f21;;
let f23 = semiNaiveReverseAD [(x11,Real);(x12,Real)] f21;;
let cst2 : targetSyn list = [Const(0.);Const(0.);Const(1.)]
let f24 = match f23 with | Pair(_,x)-> App(x,cst2) | _ -> failwith "f12 wrong format" ;;
let f25 = TargetCata.iterate nb_opti_iterations (range nb_opti) f24;;

Lwt_io.print "term:\n";;
SourcePrinter.prettyPrinter(f21);;
Lwt_io.print "anf term:\n";;
SourcePrinter.prettyPrinter(f22);;
Lwt_io.print "reverse derivative macro of term:\n";;
TargetPrinter.prettyPrinter(f23);;
Lwt_io.print "derivative of term:\n";;
TargetPrinter.prettyPrinter(f24);;
Lwt_io.print "fully reduced term:\n";;
TargetPrinter.prettyPrinter(f25);;
Lwt_io.print "\n\n";;

Lwt_io.print "term:\n";;
let f1 : sourceSyn = Let(x11,Real,Const(3.),Var(x11,Real));;
SourcePrinter.prettyPrinter(f1);;
Lwt_io.print "reverse derivative macro of term:\n";;
let f2 = semiNaiveReverseAD [(x12,Real)] f1;;
TargetPrinter.prettyPrinter(f2);;
Lwt_io.print "fully reduced reverse derivative macro of term:\n";;
let f3 = TargetCata.iterate nb_opti_iterations (range nb_opti) f2;;
TargetPrinter.prettyPrinter(f3);;
Lwt_io.print "derivative of term:\n";;
let cst2 : targetSyn list = [Const(0.);Const(0.);Const(1.)];;
let f4 = match f3 with | Pair(_,x)-> App(x,cst2) | _ -> failwith "f3 wrong format" ;;
TargetPrinter.prettyPrinter(f4);; 
Lwt_io.print "fully reduced derivative of term:\n";;
let f5 = TargetCata.iterate nb_opti_iterations (range nb_opti) f4;;
TargetPrinter.prettyPrinter(f5);;
Lwt_io.print "\n\n";;

(* let g6 = Syntax.Generator.sourceSynGen(20);;  
let g7 : sourceSyn = anf(g6);;
let g8 = semiNaiveReverseAD [] g7;;
let g9 = TargetCata.iterate nb_opti_iterations (range nb_opti) g8;;
Lwt_io.print "Term:\n";;
SourcePrinter.prettyPrinter(g6);;
Lwt_io.print "\n";; 
Lwt_io.print "Anf Term:\n";;
SourcePrinter.prettyPrinter(g7);;
Lwt_io.print "\n";;
Lwt_io.print "Reverse derivative macro of term:\n";;
TargetPrinter.prettyPrinter(g8);;
Lwt_io.print "\n";;
Lwt_io.print "Reduced reverse derivative macro of term:\n";;
TargetPrinter.prettyPrinter(g9);;
Lwt_io.print "After dead-code elim:\n";;
let g10 = Opti.deadVarsElim g9;;
TargetPrinter.prettyPrinter(g10);;
Lwt_io.print "\n\n";; *)

(* let g6 : sourceSyn = Apply1(Minus,Apply1(Cos,Const 3.));;
let g7 : sourceSyn = anf(g6);; 
let g8 = semiNaiveReverseAD [(x12,Real)] g7;;
let g9 = TargetCata.iterate 30 (range nb_opti) g8;;
Lwt_io.print "Term:\n";;
SourcePrinter.prettyPrinter(g6);;
Lwt_io.print "\n";;
Lwt_io.print "Anf Term:\n";;
SourcePrinter.prettyPrinter(g7);;
Lwt_io.print "\n";;
Lwt_io.print "Reverse derivative macro of term:\n";;
TargetPrinter.prettyPrinter(g8);;
Lwt_io.print "\n";;
Lwt_io.print "Reduced reverse derivative macro of term:\n";;
TargetPrinter.prettyPrinter(g9);;
Lwt_io.print "\n\n";; *)


let g6 : sourceSyn  = Apply2(Times, Apply2(Plus,Var(x1,Real),Var(x2,Real)),Apply2(Plus,Var(x1,Real),Var(x2,Real)));;
let g7 = anf(g6);;
let g8 = semiNaiveReverseAD [(x1,Real);(x2,Real)] g7;;
let g9 = TargetCata.iterate nb_opti_iterations (range nb_opti) g8;;
Lwt_io.print "Term:\n";;
SourcePrinter.prettyPrinter(g6);;
Lwt_io.print "\n";; 
Lwt_io.print "Anf Term:\n";;
SourcePrinter.prettyPrinter(g7);;
Lwt_io.print "\n";;
Lwt_io.print "Reverse derivative macro of term:\n";;
TargetPrinter.prettyPrinter(g8);;
Lwt_io.print "\n";;
Lwt_io.print "Reduced reverse derivative macro of term:\n";;
TargetPrinter.prettyPrinter(g9);;
Lwt_io.print "After dead-code elim:\n";;
let g10 = Opti.deadVarsElim g9;;
TargetPrinter.prettyPrinter(g10);;
Lwt_io.print "\n\n";;