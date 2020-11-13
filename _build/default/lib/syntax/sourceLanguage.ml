open Operators
open Vars

(* syntax *)
type sourceType = Real | Prod of sourceType * sourceType

and synSource = Var of var * sourceType
            | Const of float 
            | Apply1 of op1 * synSource 
            | Apply2 of op2 * synSource * synSource 
            | Let of var * sourceType * synSource * synSource

type context = (var * sourceType * synSource) list

(* substitute variable n by expr1 in expr2*)
let rec subst (x:var) expr1 expr2 = match expr2 with 
| Var (a,_)             -> if equal a x then expr1 else expr2
| Const _               -> expr2
| Apply1(op,expr2)      -> Apply1(op,subst x expr1 expr2)
| Apply2(op,expr2,expr3)-> Apply2(op,subst x expr1 expr2,subst x expr1 expr3)
| Let(y,ty,expr2,expr3) -> if equal x y 
    then failwith "trying to substitute a bound variable"
    else Let(y,ty,subst x expr1 expr2, subst x expr1 expr3)

let isValue = function
| Const _   -> true
| _         -> false

let isContextOfValues (cont : context) = 
    List.fold_left (fun acc (_,_,v) -> (isValue v) && acc) true cont 

let closingTerm expr (cont : context) = if not(isContextOfValues cont) 
    then failwith "context does not only contain values"
    else List.fold_left (fun expr1 (x,_,v) -> subst x v expr1) expr cont

let rec freeVars = function
| Var (x,_)             -> [x]
| Apply1(_,expr)        -> freeVars expr
| Apply2(_,expr1,expr2) -> 
    let expr1Fv = freeVars expr1 in 
    let expr2Fv = freeVars expr2 in 
    List.append expr1Fv (List.filter (fun x -> not (List.mem x expr1Fv)) expr2Fv)
| Let(y,_,expr1,expr2)  -> 
    let expr1Fv = freeVars expr1 in 
    let expr2Fv = freeVars expr2 in 
    List.append expr1Fv (List.filter (fun x -> not(equal x y) && not(List.mem y expr1Fv)) expr2Fv) 
| _                     -> []

let rec varNameNotBound (name:string) expr = match expr with
| Let((str,_),_,expr1,expr2) -> str<> name && (varNameNotBound name expr1) && (varNameNotBound name expr2)
| Apply1(_,expr)             ->  (varNameNotBound name expr)
| Apply2(_,expr1,expr2)      ->  (varNameNotBound name expr1) && (varNameNotBound name expr2)
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
| Var (s,ty)            -> let i = index_of s freeV in Var ((name,i),ty)
| Apply1(op,expr1)      -> Apply1(op,canRen expr1)
| Apply2(op,expr1,expr2)-> Apply2(op,canRen expr1,canRen expr2)
| Let(y,ty,expr1,expr2) -> Let(y,ty,canRen expr1,canRen expr2) 
| _                     -> expr
in canRen expr
else failwith ("variable "^name^" is already used as a bound variable, can't rename free vars canonically with "^name)

(* simple typecheker *)
let rec typeSource = function
| Const _           -> Real
| Var(_,ty)         -> ty
| Apply1(_,_)       -> Real
| Apply2(_,_,_)     -> Real
| Let(_,_,_,expr)   -> typeSource expr

let rec isWellTyped = function
| Const _               -> true
| Var _                 -> true
| Apply1(_,expr)        -> (typeSource expr) == Real && isWellTyped expr 
| Apply2(_,expr1,expr2) -> (typeSource expr1) == Real 
                        && (typeSource expr2) == Real 
                        && isWellTyped expr1 
                        && isWellTyped expr2
| Let(_,ty,expr1,expr2) -> ty == (typeSource expr1) && isWellTyped expr2
 
(* checks whether the context captures all the free variables of an expression*)
let contextComplete expr context =
    let exprFv = freeVars expr in 
    List.fold_left (fun acc x -> acc && (List.exists (fun (y,_,_) -> equal y x) context)) true exprFv

(* interpreter *)
let interpreter expr context = 
if not(isWellTyped expr) then failwith "the term is ill-typed";
if not(contextComplete expr context) then failwith "the context does not capture all free vars";
let expr2 = closingTerm expr context in 
let rec interp = function
| Const a               ->  a
| Apply1(op,expr)       ->  let v = interp expr in 
                            interpreterOp1 op v
| Apply2(op,expr1,expr2)->  let val1 = interp expr1 in 
                            let val2 = interp expr2 in 
                            interpreterOp2 op val1 val2
| Let(x,_,expr1,expr2)  ->  let v = interp expr1 in 
                            let expr3 = subst x (Const v) expr2 in
                            interp expr3
| _                     ->  failwith "the expression should not contain this pattern"
in interp expr2