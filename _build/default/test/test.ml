open Syntax.Operators
open Syntax.SourceLanguage
open Syntax.PrettyPrinter

let f1 = Apply1(Cos, Const 7.);; 
let f2 = Let(1,Apply2(Plus, Const 5.,Var 2),Apply1(Sin,Var 1));;
let f3 = Apply2(Plus,Const 7.,Const 8.);;
let f4 = Apply1(Exp, Const 6.);;
let f5 = Apply1(Sin, Var 1);;
let f6 = Apply1(Cos, Const 0.716814692820);; 

prettyPrinter f1;;
prettyPrinter f2;;

let printVal expr context= Lwt_io.print ((string_of_float (interpreterSource expr context))^"\n");;
printVal (Const 7.) ;;
printVal f1 [];;
printVal f3;;
printVal f4 [];;
printVal f5 [(1,Const 0.)];;
printVal f5 [(1,Const 2.)];;
printVal f5 [(1,Const 8.283185307)];;
printVal f6 []
