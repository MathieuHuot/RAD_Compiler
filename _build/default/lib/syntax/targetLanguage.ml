open Operators
open Vars

(* syntax *)
type targetType = Real 
            | Prod of targetType * targetType
            | Arrow of targetType * targetType 

and synTarget = Var of var * targetType
            | Const of float 
            | Apply1 of op1 * synTarget 
            | Apply2 of op2 * synTarget * synTarget
            | Let of var * targetType * synTarget * synTarget
            | Pair of synTarget * synTarget
            | Fun of var * targetType * synTarget
            | App of synTarget * synTarget
            | Case of synTarget * var * targetType * var * targetType * synTarget

type context = (var * targetType * synTarget) list

let rec sourceToTargetType (ty : SourceLanguage.sourceType) : targetType = match ty with
| Real          -> Real
| Prod(ty1,ty2) -> Prod(sourceToTargetType ty1,sourceToTargetType ty2)

(* substitute variable n by expr1 in expr2*)
let rec subst (x:var) expr1 expr2 = match expr2 with 
| Var(a,_)                        -> if equal a x then expr1 else expr2
| Const _                         -> expr2
| Apply1(op,expr2)                -> Apply1(op,subst x expr1 expr2)
| Apply2(op,expr2,expr3)          -> Apply2(op,subst x expr1 expr2,subst x expr1 expr3)
| Let(y,ty,expr2,expr3)           -> if equal x y 
  then failwith "trying to substitute a bound variable"
  else Let(y,ty,subst x expr1 expr2, subst x expr1 expr3)
| Pair(expr2,expr3)               -> Pair(subst x expr1 expr2,subst x expr1 expr3)
| Fun(y,ty,expr2)                 -> if equal x y 
  then failwith "trying to substitute a bound variable"
  else Fun(y,ty,subst x expr1 expr2)
| App(expr2,expr3)                -> App(subst x expr1 expr2,subst x expr1 expr3)
| Case(expr2,y1,ty1,y2,ty2,expr3) -> if (equal x y1)||(equal x y2)
  then failwith "trying to substitute a bound variable"
  else Case(subst x expr1 expr2,y1,ty1,y2,ty2,subst x expr1 expr3)

let rec isValue = function
| Const _           -> true
| Pair(expr1,expr2) -> isValue expr1 && isValue expr2
| Fun(_,_,_)        -> true
| _                 -> false

let isContextOfValues (cont : context) = 
    List.fold_left (fun acc (_,_,v) -> (isValue v) && acc) true cont 

let closingTerm expr (cont : context) = if not(isContextOfValues cont) 
    then failwith "context does not only contain values"
    else List.fold_left (fun expr1 (x,_,v) -> subst x v expr1) expr cont

let rec freeVars = function
| Var (x,_)             -> [x]
| Apply1(_,expr)        -> freeVars expr
| Apply2(_,expr1,expr2)
| App(expr1,expr2) 
| Pair(expr1,expr2)     -> 
    let expr1Fv = freeVars expr1 in 
    let expr2Fv = List.filter (fun x -> not (List.mem x expr1Fv)) (freeVars expr2) in 
    List.append expr1Fv expr2Fv
| Let(y,_,expr1,expr2)  ->
    let expr1Fv = List.filter (fun x -> not(equal x y)) (freeVars expr1) in 
    let expr2Fv = List.filter (fun x -> not(List.mem x expr1Fv)) (freeVars expr2) in 
    List.append expr1Fv expr2Fv
| Fun(y,_,expr)         -> let exprFv = freeVars expr in
    List.filter (fun x -> not(equal x y)) exprFv
| Case(expr1,y1,_,y2,_,expr2) -> 
    let expr1Fv = freeVars expr1 in 
    let expr2Fv = List.filter (fun x -> not(equal x y1) && not(equal x y2)) (freeVars expr2) in 
    List.append expr1Fv (List.filter (fun x -> not(List.mem x expr1Fv)) expr2Fv)
| _ -> [] 

let rec varNameNotBound (name:string) expr = match expr with
| Let((str,_),_,expr1,expr2)              -> str<> name && (varNameNotBound name expr1) && (varNameNotBound name expr2)
| Apply1(_,expr)                          ->  (varNameNotBound name expr)
| Apply2(_,expr1,expr2)
| Pair(expr1,expr2)
| App(expr1,expr2)                        ->  (varNameNotBound name expr1) && (varNameNotBound name expr2)
| Fun((str,_),_,expr)                     -> str<> name && (varNameNotBound name expr)
| Case(expr1,(str1,_),_,(str2,_),_,expr2) -> str1<> name && str2<> name && (varNameNotBound name expr1) && (varNameNotBound name expr2)
| _ -> true 

let index_of el lis = 
  let rec index_aux i = function
    | [] -> failwith "Element not found in the list"
    | hd::tl -> if hd == el then i else index_aux (i+1) tl
  in index_aux 0 lis

let canonicalAlphaRename (name:string) expr =
let freeV = freeVars expr in 
if varNameNotBound name expr then 
let rec canRen expr = match expr with
| Var (s,ty)                      -> let i = index_of s freeV in Var ((name,i),ty)
| Apply1(op,expr1)                -> Apply1(op,canRen expr1)
| Apply2(op,expr1,expr2)          -> Apply2(op,canRen expr1,canRen expr2)
| Let(y,ty,expr1,expr2)           -> Let(y,ty,canRen expr1,canRen expr2)
| Pair(expr1,expr2)               -> Pair(canRen expr1,canRen expr2)
| App(expr1,expr2)                -> App(canRen expr1,canRen expr2) 
| Fun(y,ty,expr)                  -> Fun(y,ty,canRen expr)
| Case(expr1,y1,ty1,y2,ty2,expr2) -> Case(canRen expr1,y1,ty1,y2,ty2,canRen expr2)
| _                               -> expr
in canRen expr
else failwith ("variable "^name^" is already used as a bound variable, can't rename free vars canonically with "^name)

(* simple typecheker *)
let rec typeTarget = function
| Const _             -> Real
| Var(_,ty)           -> ty
| Apply1(_,_)         -> Real
| Apply2(_,_,_)       -> Real
| Let(_,_,_,expr)     -> typeTarget expr
| Pair(expr1,expr2)   -> Prod(typeTarget expr1,typeTarget expr2)
| Fun(_,ty,expr)      -> Arrow(ty,typeTarget expr)
| App(_,expr)         ->  begin
                          match (typeTarget expr) with 
                          | Arrow(_,ty2) -> ty2 
                          | _            -> failwith "the expression should have a function type"
                          end
| Case(_,_,_,_,_,expr)-> typeTarget expr

let rec isWellTyped = function
| Const _               -> true
| Var _                 -> true
| Apply1(_,expr)        -> (typeTarget expr) == Real && isWellTyped expr 
| Apply2(_,expr1,expr2) -> (typeTarget expr1) == Real 
                        && (typeTarget expr2) == Real 
                        && isWellTyped expr1 
                        && isWellTyped expr2
| Let(_,ty,expr1,expr2) -> ty == (typeTarget expr1) && isWellTyped expr2
| Pair(expr1,expr2)     -> isWellTyped expr1 && isWellTyped expr2
| Fun(_,_,expr)         -> isWellTyped expr
| App(expr1,expr2)      -> let ty1 = typeTarget expr1 in
                           let ty2 = typeTarget expr2 in
                           begin
                           match ty1 with 
                            | Arrow(ty11,_) -> ty2 == ty11 
                                                  && isWellTyped expr1 
                                                  && isWellTyped expr2
                            | _                -> false
                           end
| Case(expr1,_,ty1,_,ty2,expr2) ->  let ty3 = typeTarget expr1 in
                                    match ty3 with 
                                    | Prod(ty31,ty32) ->  ty1 == ty31 
                                                          && ty2 == ty32
                                                          && isWellTyped expr1 
                                                          && isWellTyped expr2
                                    | _               -> false
 
(* interpreter *)

(* checks whether the context captures all the free variables of an expression*)
let contextComplete expr context =
  let exprFv = freeVars expr in 
  List.fold_left (fun acc x -> acc && (List.exists (fun (y,_,_) -> equal y x) context)) true exprFv

let interpreterOp1T op expr = match expr with
| Const v -> begin
  match op with
  | Cos  -> Const(cos(v))
  | Sin  -> Const(sin(v))
  | Exp  -> Const(exp(v))
  | Minus-> Const(-.v)
  end
| _ -> failwith "the operand of a unary operator is not a real value"
  
let interpreterOp2T op expr1 expr2 = match expr1,expr2 with
| (Const v1,Const v2) -> begin
  match op with
  | Plus  -> Const(v1+.v2)
  | Times -> Const(v1*.v2)
  | Minus -> Const(v1-.v2)
  end
| _ -> failwith "one operand of a binary operator is not a real value"

(* assumes the context captures all free vars, and is only given values *)
let interpreter expr context = 
if not(isWellTyped expr) then failwith "the term is ill-typed";
if not(contextComplete expr context) then failwith "the context does not capture all free vars";
let expr2 = closingTerm expr context in 
let rec interp expr = match expr with
| expr when isValue(expr)     ->  expr
| Apply1(op,expr)             ->  let v = interp expr in 
                                  interpreterOp1T op v
| Apply2(op,expr1,expr2)      ->  let val1 = interp expr1 in 
                                  let val2 = interp expr2 in 
                                  interpreterOp2T op val1 val2
| Let(x,_,expr1,expr2)        ->  let v = interp expr1 in 
                                  interp (subst x v expr2)
| Pair(expr1,expr2)           ->  Pair(interp expr1,interp expr2)
| Case(expr1,y1,_,y2,_,expr2) -> begin match (interp expr1) with
    | Pair(v1,v2) -> interp (subst y2 v2 (subst y1 v1 expr2))
    | _           -> failwith "expression should reduce to a pair" end
| App(expr1,expr2)            ->  begin match (interp expr1) with
    | Fun(x,_,expr1)-> let v = interp expr2 in interp (subst x v expr1)
    | _             -> failwith "expression should reduce to a function" end
| _                           ->  expr
in interp expr2

(* Some algebraic simplifications, done unefficiently *)
let rec iterator f x n = 
  if n == 0 then x
  else let x = f x in iterator f x (n-1) 

let realOptimizer expr n =
  let rec optim expr = match expr with
  | Apply2(Plus,Const a,Const b)    -> Const(a+.b)
  | Apply2(Times,Const a,Const b)   -> Const(a*.b)
  | Apply2(Plus,Apply2(Times,expr1,expr2),Apply2(Times,expr3,expr4)) when expr1 == expr3 -> 
     Apply2(Times,expr1,Apply2(Plus,expr2,expr4))
  | Apply2(Plus,Apply2(Times,expr1,expr2),Apply2(Times,expr3,expr4)) when expr2 == expr4 -> 
    Apply2(Times,Apply2(Plus,expr1,expr3),expr2)
  | Apply1(op, expr)                -> Apply1(op,optim expr)
  | Apply2(op, expr1, expr2)        ->  Apply2(op, optim expr1, optim expr2)
  | Pair(expr1,expr2)               -> Pair(optim expr1,optim expr2) 
  | App(expr1,expr2)                -> App(optim expr1,optim expr2)
  | Fun(x,ty,expr)                  -> Fun(x,ty, optim expr) 
  | Case(expr1,x1,ty1,x2,ty2,expr2) -> Case(optim expr1,x1,ty1,x2,ty2,optim expr2)
  | _                               -> expr
  in iterator optim expr n