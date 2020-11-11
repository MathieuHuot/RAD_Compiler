open Operators
open SourceLanguage
(* open TargetLanguage *)

let arrow = " ->"
let arrow2= " →"
let arrow3= "⟶"
let bra   = "⟨"
let ket   = "⟩"
let leftpar="("
let rightpar=")" 
let klambda= "λ"
let lambda = " fun"
let colon = " :" 
let comma = ", " 
let equal = " ="
let kcase = "case "
let return = "return" 
let kwith = " with"
let kof = " of "
let klet = "let "
let kequal = " = "
let kin = " in" 
let kdot= ". "

let printVar = function
| Var(str,n) -> str^(string_of_int n)
| _          -> failwith "this is not a variable"

let printConst = function
| Const c -> string_of_float c
| _       -> failwith "this is not a constant"

let printOp1 = function 
   | Cos  -> "cos "
   | Sin  -> "sin "
   | Exp  -> "exp "
   | Minus-> "-"

let isOp2Infix = function
| Plus | Times | Minus -> true

let printOp2 = function 
    | Plus  -> " + "
    | Times -> " * "
    | Minus -> " - "

let prettyPrinter (expr:synSource) = 
let rec prettyP = function
| Var x                     -> printVar (Var x)
| Const c                   -> printConst (Const c)
| Apply1(op,expr)           -> printOp1 op^"("^(prettyP expr)^")"  
| Apply2(op,expr1,expr2)    -> if (isOp2Infix op) then "("^(prettyP expr1)^(printOp2 op)^(prettyP expr2)^")"
else (printOp2 op)^"("^(prettyP expr1)^", "^(prettyP expr2)^")"
| Let(x,expr1,expr2)        -> klet^(printVar (Var x))^kequal^(prettyP expr1)^kin^"\n"^(prettyP expr2)
in Lwt_io.print ((prettyP expr)^"\n");;

(* let prettyPrinterTarget (expr: synTarget) = 
let rec prettyP = function
| Var x                     -> printVar (Var x)
| Const c                   -> printConst (Const c)
| Apply1(op,expr)           -> printOp1 op^leftpar^(prettyP expr)^rightpar 
| Apply2(op,expr1,expr2)    -> if (isOp2Infix op) then leftpar^(prettyP expr1)^(printOp2 op)^(prettyP expr2)^rightpar
else (printOp2 op)^leftpar^(prettyP expr1)^comma^(prettyP expr2)^rightpar
| Let(x,expr1,expr2)        -> klet^(printVar (Var x))^kequal^(prettyP expr1)^kin^"\n"^(prettyP expr2)
| Pair(expr1,expr2)         -> bra^(prettyP expr1)^comma^(prettyP expr2)^ket
| Fun(x,expr)               -> klambda^(printVar (Var x))^kdot^(prettyP expr)
| App(expr1,expr2)          -> leftpar^(prettyP expr1)^rightpar^(prettyP expr2)
| Case(expr1,x,y,expr2)     -> kcase^(prettyP expr1)^kof^bra^(printVar (Var x))^comma^(printVar (Var y))^ket^arrow3^(prettyP expr2)
in Lwt_io.print ((prettyP expr)^"\n") *)