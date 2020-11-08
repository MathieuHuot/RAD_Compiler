open Operators
open Lwt_io

let arrow = " ->"
let lambda = " fun"
let colon = " :" 
let equal = " ="
let kcase = "case "
let return = "return" 
let kwith = " with"
let kof = " of "

 let printOp1 = function 
   | Cos -> "cos "
   | Sin -> "sin "
   | Exp -> "exp"

let printOp2 = function 
    | Plus -> " + "
    | Times -> " * " 
    | Minus -> " - "

let prettyPrinter = function
| _ -> printf "Hello" 