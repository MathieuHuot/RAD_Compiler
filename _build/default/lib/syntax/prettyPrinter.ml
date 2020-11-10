open Operators
open SourceLanguage

let arrow = " ->"
let lambda = " fun"
let colon = " :" 
let equal = " ="
let kcase = "case "
let return = "return" 
let kwith = " with"
let kof = " of "
let klet = "let "
let kequal = " = "
let kin = " in" 

let printVar = function
| Var(str,n) -> str^(string_of_int n)
| _     -> failwith "this is not a variable"

let printConst = function
| Const c -> string_of_float c
| _       -> failwith "this is not a constant"

let printOp1 = function 
   | Cos -> "cos "
   | Sin -> "sin "
   | Exp -> "exp"

let isOp2Infix = function
| Plus | Times | Minus -> true

let printOp2 = function 
    | Plus -> " + "
    | Times -> " * " 
    | Minus -> " - "

let prettyPrinter expr = 
let rec prettyP = function
| Var x                     -> printVar (Var x)
| Const c                   -> printConst (Const c)
| Apply1(op,expr)           -> printOp1 op^"("^(prettyP expr)^")"  
| Apply2(op,expr1,expr2)    -> if (isOp2Infix op) then "("^(prettyP expr1)^(printOp2 op)^(prettyP expr2)^")"
else (printOp2 op)^"("^(prettyP expr1)^", "^(prettyP expr2)^")"
| Let(x,expr1,expr2)        -> klet^(printVar (Var x))^kequal^(prettyP expr1)^kin^"\n"^(prettyP expr2)
in Lwt_io.print ((prettyP expr)^"\n")