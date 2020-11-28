open Operators

let arrow = " ->"
let arrow2= " →"
let arrow3= "⟶"
let bra   = "⟨"
let ket   = "⟩"
let leftpar="("
let rightpar=")"
let leftbra="["
let rightbra="]"
let leftcurlbra="{"
let rightcurlbra="}" 
let klambda= "λ"
let lambda = " fun"
let colon = " :" 
let comma = ", "
let comma2 = "," 
let equal = " ="
let kcase = "case "
let return = "return" 
let kwith = " with"
let kof = " of "
let klet = "let "
let kequal = " = "
let kin = " in" 
let kdot= ". "
let kpower= "^"

let printOp1 = function 
   | Cos      -> "cos "
   | Sin      -> "sin "
   | Exp      -> "exp "
   | Minus    -> "-"
   | Power(n) -> kpower^string_of_int n

let isOp2Infix = function
| Plus | Times | Minus -> true

let printOp2 = function 
    | Plus  -> " + "
    | Times -> " * "
    | Minus -> " - "

module type PrettyPrinter = sig
    type types
    type terms
    val printVar : terms -> string
    val printConst : terms -> string
    val prettyPrinter : terms -> unit Lwt.t
end

module SourcePrinter : PrettyPrinter with type terms = SourceLanguage.sourceSyn = struct
open SourceLanguage
type types = sourceType
type terms = sourceSyn

let printVar (expr:sourceSyn) = match expr with
| Var((str,n),_) -> str^(string_of_int n)
| _              -> failwith "printVar: this is not a variable"

let printConst (expr:sourceSyn) = match expr with
| Const c -> string_of_float c
| _       -> failwith "printConst: this is not a constant"

let prettyPrinter (expr:sourceSyn) = 
let rec prettyP (expr:terms) = match expr with
| Var(x,ty)                 ->  printVar (Var(x,ty))
| Const c                   ->  printConst (Const c)
| Apply1(op,expr)           ->  printOp1 op
                                ^"("
                                ^(prettyP expr)
                                ^")"  
| Apply2(op,expr1,expr2)    ->  if (isOp2Infix op) 
                                then    "("
                                        ^(prettyP expr1)
                                        ^(printOp2 op)
                                        ^(prettyP expr2)
                                        ^")"
                                else    (printOp2 op)
                                        ^"("^(prettyP expr1)
                                        ^", "
                                        ^(prettyP expr2)
                                        ^")"
| Let(x,ty,expr1,expr2)     ->  klet
                                ^(printVar (Var(x,ty)))
                                ^kequal
                                ^(prettyP expr1)
                                ^kin
                                ^"\n"
                                ^(prettyP expr2)
in Lwt_io.print ((prettyP expr)^"\n");;
end

module TargetPrinter :  PrettyPrinter  with type terms = TargetLanguage.targetSyn = struct
open TargetLanguage
type types = targetType
type terms = targetSyn

let printVar = function
| Var((str,n),_) -> str^(string_of_int n)
| _              -> failwith "printVar: this is not a variable"

let printConst = function
| Const c -> string_of_float c
| _       -> failwith "printConst: this is not a constant"

let removeLast string = 
  let n = String.length string in 
  String.sub string 0 (n-1)

let prettyPrinter (expr: targetSyn) = 
let rec prettyP = function
| Var(x,ty)                     ->  printVar (Var(x,ty))
| Const c                       ->  printConst (Const c)
| Apply1(op,expr)               ->  printOp1 op
                                    ^leftpar^(prettyP expr)
                                    ^rightpar 
| Apply2(op,expr1,expr2)        ->  if (isOp2Infix op) 
                                    then    leftpar
                                            ^(prettyP expr1)
                                            ^(printOp2 op)
                                            ^(prettyP expr2)
                                            ^rightpar
                                    else    (printOp2 op)
                                            ^leftpar
                                            ^(prettyP expr1)
                                            ^comma
                                            ^(prettyP expr2)
                                            ^rightpar
| Let(x,ty,expr1,expr2)         ->  klet
                                    ^(printVar (Var(x,ty)))
                                    ^kequal
                                    ^(prettyP expr1)
                                    ^kin
                                    ^"\n"
                                    ^(prettyP expr2)
| Pair(expr1,expr2)             ->  bra
                                    ^(prettyP expr1)
                                    ^comma
                                    ^(prettyP expr2)
                                    ^ket
| Fun(varList,expr)             ->  klambda
                                    ^(if varList==[] then "" else removeLast (List.fold_left (fun acc (x,ty) -> acc^(printVar (Var(x,ty))^comma2)) "" varList))
                                    ^kdot
                                    ^(prettyP expr)
| App(expr1,exprList)           ->  leftpar
                                    ^(prettyP expr1)
                                    ^rightpar
                                    ^(if exprList==[] then  leftcurlbra^rightcurlbra else
                                    leftbra
                                    ^removeLast (removeLast(List.fold_left (fun acc expr -> acc^prettyP expr^comma) "" exprList))
                                    ^rightbra)
| Case(expr1,x,ty1,y,ty2,expr2) ->  
                                      (* kcase
                                    ^(prettyP expr1)
                                    ^kof
                                    ^bra
                                    ^(printVar (Var (x,ty1)))
                                    ^comma
                                    ^(printVar (Var(y,ty2)))
                                    ^ket
                                    ^arrow3
                                    ^"\n"
                                    ^(prettyP expr2) *)
                                    klet
                                    ^(printVar (Var(x,ty1)))
                                    ^comma
                                    ^(printVar (Var(y,ty2)))
                                    ^kequal
                                    ^prettyP expr1
                                    ^kin
                                    ^"\n"
                                    ^(prettyP expr2)
| Tuple(exprList)               ->  if exprList==[] then  leftcurlbra^rightcurlbra else
                                    leftcurlbra
                                    ^removeLast (List.fold_left (fun acc expr -> acc^prettyP expr^comma2) "" exprList)
                                    ^rightcurlbra
| NCase(expr1,varList,expr2)    ->  klet
                                    ^(if varList==[] then "" else removeLast (List.fold_left (fun acc (x,ty) -> acc^(printVar (Var(x,ty))^comma2)) "" varList))
                                    ^kequal
                                    ^prettyP expr1
                                    ^kin
                                    ^"\n"
                                    ^(prettyP expr2)
in Lwt_io.print ((prettyP expr)^"\n")
end