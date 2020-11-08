open Operators
open Vars

(* syntax *)
type synSource = Var of var
            | Const of float 
            | Apply1 of op1 * synSource 
            | Apply2 of op2 * synSource * synSource
            | Let of var * synSource * synSource

(* auxiliary for interpreter *)
let interpreterOp1 op v = match op with
| Cos -> cos(v)
| Sin -> sin(v)
| Exp -> exp(v)

let interpreterOp2 op val1 val2= match op with
| Plus  -> val1+.val2
| Times -> val1*.val2
| Minus -> val1-.val2

let rec subst (n:var) (expr1 : synSource) (expr2 : synSource) = match expr2 with 
| Var a -> if equal a n then expr1 else Var a
| Const a -> Const a
| Apply1(op,a) -> Apply1(op,subst n expr1 a)
| Apply2(op,a,b) -> Apply2(op,subst n expr1 a,subst n expr1 b)
| Let(m,a,b) -> if equal n m 
    then failwith "trying to substitute a bound variable"
    else Let(m,subst n expr1 a, subst n expr1 b)

let isValue expr = match expr with
| Const _   -> true
| _         -> false

let isContextOfValues (context : (var * synSource) list) = 
    List.fold_left (fun acc (_,v) -> (isValue v) && acc) true context 

let closingTerm expr context = if not(isContextOfValues context) 
    then failwith "context does not only contain real values"
    else List.fold_left (fun expr1 (n,v) -> subst n v expr1) expr context

(* interpreter *)
 let interpreterSource expr context = 
 let expr2 = closingTerm expr context in 
 let rec interp expr =
 match expr with
| Const a -> a
| Apply1(op,a) -> 
    let v = interp a in 
    interpreterOp1 op v
| Apply2(op,a,b) ->
    let val1 = interp a in 
    let val2 = interp b in 
    interpreterOp2 op val1 val2
| Let(n,a,b) -> let v = interp a in 
                let c = subst n (Const v) b in
                interp c
| _ -> failwith "the expression should not contain this pattern"
in interp expr2