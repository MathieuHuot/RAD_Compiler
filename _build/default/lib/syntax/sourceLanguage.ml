open Operators
open Vars

(* syntax *)
type synSource = Var of var
            | Const of float 
            | Apply1 of op1 * synSource 
            | Apply2 of op2 * synSource * synSource
            | Let of var * synSource * synSource

type context = (var * synSource) list

(* auxiliary for interpreter *)
let interpreterOp1 op v = match op with
| Cos -> cos(v)
| Sin -> sin(v)
| Exp -> exp(v)

let interpreterOp2 op val1 val2= match op with
| Plus  -> val1+.val2
| Times -> val1*.val2
| Minus -> val1-.val2

(* substitute variable n by expr1 in expr2*)
let rec subst (x:var) expr1 expr2 = match expr2 with 
| Var a -> if equal a x then expr1 else Var a
| Const a -> Const a
| Apply1(op,a) -> Apply1(op,subst x expr1 a)
| Apply2(op,a,b) -> Apply2(op,subst x expr1 a,subst x expr1 b)
| Let(y,a,b) -> if equal x y 
    then failwith "trying to substitute a bound variable"
    else Let(y,subst x expr1 a, subst x expr1 b)

let isValue = function
| Const _   -> true
| _         -> false

let isContextOfValues (cont : context) = 
    List.fold_left (fun acc (_,v) -> (isValue v) && acc) true cont 

let closingTerm expr (cont : context) = if not(isContextOfValues cont) 
    then failwith "context does not only contain values"
    else List.fold_left (fun expr1 (x,v) -> subst x v expr1) expr cont

let rec freeVars = function
| Var x -> [x]
| Apply1(_,expr) -> freeVars expr
| Apply2(_,expr1,expr2) -> 
    let expr1Fv = freeVars expr1 in 
    let expr2Fv = freeVars expr2 in 
    List.append expr1Fv (List.filter (fun x -> not (List.mem x expr1Fv)) expr2Fv)
| Let(y,expr1,expr2) -> let expr1Fv = freeVars expr1 in 
    let expr2Fv = freeVars expr2 in 
    List.append expr1Fv (List.filter (fun a -> not(equal a y) && not(List.mem y expr1Fv)) expr2Fv) 
| _ -> []

let rec varNameNotBound (name:string) expr = match expr with
| Let((str,_),expr1,expr2) -> str<> name && (varNameNotBound name expr1) && (varNameNotBound name expr2)
| _ -> true 

let index_of el lis = 
  let rec index_rec i = function
    | [] -> failwith "Element not found in the list"
    | hd::tl -> if hd == el then i else index_rec (i+1) tl
  in index_rec 0 lis

let canonicalAlphaRename (name:string) expr =
let freeV = freeVars expr in 
if varNameNotBound name expr then 
let rec canRen expr = match expr with
| Var s -> let i = index_of s freeV in Var (name,i)
| Let(y,expr1,expr2) -> Let(y,canRen expr1,canRen expr2)
| Apply1(op,expr1)  -> Apply1(op,canRen expr1)
| Apply2(op,expr1,expr2)  -> Apply2(op,canRen expr1,canRen expr2) 
| _  -> expr
in canRen expr
else failwith ("variable "^name^" is already used as a bound variable, can't rename free vars canonically with "^name)

(* interpreter *)
 let interpreterSource expr context = 
 let expr2 = closingTerm expr context in 
 let rec interp = function
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