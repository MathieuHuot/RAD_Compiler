open Operators
open Vars

(* syntax *)
type targetType = Real 
            | Prod of targetType * targetType
            | Arrow of (targetType list ) * targetType 

and targetSyn = Var of var * targetType
            | Const of float 
            | Apply1 of op1 * targetSyn 
            | Apply2 of op2 * targetSyn * targetSyn
            | Let of var * targetType * targetSyn * targetSyn
            | Pair of targetSyn * targetSyn
            | Fun of ((var * targetType) list) * targetSyn
            | App of targetSyn * (targetSyn list)
            | Case of targetSyn * var * targetType * var * targetType * targetSyn

type context = (var * targetType * targetSyn) list

let rec sourceToTargetType (ty : SourceLanguage.sourceType) : targetType = match ty with
| Real          -> Real
| Prod(ty1,ty2) -> Prod(sourceToTargetType ty1,sourceToTargetType ty2)

let equalOp1 op1 op2 = match op1,op2 with
  | Cos,Cos     -> true
  | Sin,Sin     -> true
  | Exp,Exp     -> true
  | Minus,Minus -> true
  | _           -> false

let equalOp2 op1 op2 = match op1,op2 with
  | Plus,Plus   -> true
  | Times,Times -> true
  | Minus,Minus -> true
  | _           -> false

let rec equalTypes ty1 ty2 = match ty1,ty2 with
  | Real,Real                             -> true
  | Prod(ty11,ty12),Prod(ty21,ty22)       -> equalTypes ty11 ty21 
                                             && equalTypes ty12 ty22
  | Arrow(tyList1,ty1),Arrow(tyList2,ty2) -> equalTypes ty1 ty2 
                                             && List.for_all2 (fun ty11 ty22 -> equalTypes ty11 ty22 ) tyList1 tyList2
  | _                                     -> false
  
(* substitute variable x of type xTy by expr1 in expr2*)
let rec subst (x:var) xTy expr1 expr2 = match expr2 with 
| Var(a,ty)                       -> if equal a x && equalTypes ty xTy then expr1 else expr2
| Const _                         -> expr2
| Apply1(op,expr2)                -> Apply1(op,subst x xTy expr1 expr2)
| Apply2(op,expr2,expr3)          -> Apply2(op,subst x xTy expr1 expr2,subst x xTy expr1 expr3)
| Let(y,ty,expr2,expr3)           -> if equal x y 
                                     then failwith "trying to substitute a bound variable"
                                     else Let(y,ty,subst x xTy expr1 expr2, subst x xTy expr1 expr3)
| Pair(expr2,expr3)               -> Pair(subst x xTy expr1 expr2,subst x xTy expr1 expr3)
| Fun(varList,expr2)              -> if (List.exists (fun (y,ty) -> equal x y && equalTypes ty xTy) varList)
                                     then failwith "trying to substitute a bound variable"
                                     else Fun(varList,subst x xTy expr1 expr2)
| App(expr2,exprList)             -> App(subst x xTy expr1 expr2,List.map (subst x xTy expr1) exprList)
| Case(expr2,y1,ty1,y2,ty2,expr3) -> if (equal x y1)||(equal x y2)
                                     then failwith "trying to substitute a bound variable"
                                     else Case(subst x xTy expr1 expr2,y1,ty1,y2,ty2,subst x xTy expr1 expr3)

(*  Checks whether two terms are equal up to alpha renaming.
    Two variables match iff they are the same free variable or they are both bound and equal up to renaming.
    This renaming is checked by carrying an explicit list of pairs of bound variables found so far in the term. 
    When an occurence of bound variable is found deeper in the term, we check whether it matches the renaming *)
let equalTerms expr1 expr2 = 
let rec eqT expr1 expr2 list = match expr1,expr2 with
| Const a,Const b                                     -> a==b
| Var (a,ty1),Var (b,ty2)                             -> (equal a b || List.mem  ((a,ty1),(b,ty2)) list)
                                                         && equalTypes ty1 ty2
| Apply1(op1,expr11),Apply1(op2,expr22)               -> equalOp1 op1 op2 
                                                         && eqT expr11 expr22 list
| Apply2(op1,expr11,expr12),Apply2(op2,expr21,expr22) -> equalOp2 op1 op2 
                                                         &&  eqT expr11 expr21 list 
                                                         &&  eqT expr12 expr22 list
| Let(x,ty1,expr11,expr12), Let(y,ty2,expr21,expr22)  -> equalTypes ty1 ty2 
                                                         && eqT expr11 expr21 list
                                                         &&  eqT expr12 expr22 (((x,ty1),(y,ty2))::list)
| App(expr11,exprList1),App(expr21,exprList2)         -> eqT expr11 expr21 list
                                                         &&  List.for_all2 (fun x y -> eqT x y list) exprList1 exprList2
| Pair(expr11,expr12), Pair(expr21,expr22)            -> eqT expr11 expr21 list
                                                         && eqT expr12 expr22 list
| Fun(varList1,expr1),Fun(varList2,expr2)             -> eqT expr1 expr2 (List.append (List.combine varList1 varList2) list) 
                                                         && List.for_all2 (fun (_,ty1) (_,ty2) -> equalTypes ty1 ty2) varList1 varList2
| Case(expr11,x11,ty11,x12,ty12,expr12),
  Case(expr21,x21,ty21,x22,ty22,expr22)               -> eqT expr11 expr21 list
                                                         && eqT expr12 expr22 (((x11,ty11),(x21,ty21))::((x12,ty12),(x22,ty22))::list)
                                                         && equalTypes ty11 ty21  
                                                         && equalTypes ty12 ty22                                                          
| _                                                   -> false
in eqT expr1 expr2 []

let rec isValue = function
| Const _           -> true
| Pair(expr1,expr2) -> isValue expr1 && isValue expr2
| Fun(_,_)          -> true
| _                 -> false

let isContextOfValues (cont : context) = 
    List.fold_left (fun acc (_,_,v) -> (isValue v) && acc) true cont 

let closingTerm expr (cont : context) = if not(isContextOfValues cont) 
    then failwith "context does not only contain values"
    else List.fold_left (fun expr1 (x,ty,v) -> subst x ty v expr1) expr cont

let rec freeVars = function
| Var (x,_)                   -> [x]
| Apply1(_,expr)              -> freeVars expr
| Apply2(_,expr1,expr2)
| Pair(expr1,expr2)           -> 
    let expr1Fv = freeVars expr1 in 
    let expr2Fv = List.filter (fun x -> not (List.mem x expr1Fv)) (freeVars expr2) in 
    List.append expr1Fv expr2Fv
| Let(y,_,expr1,expr2)        ->
    let expr1Fv = List.filter (fun x -> not(equal x y)) (freeVars expr1) in 
    let expr2Fv = List.filter (fun x -> not(List.mem x expr1Fv)) (freeVars expr2) in 
    List.append expr1Fv expr2Fv
| App(expr1,exprList)         ->  
    let expr1Fv = freeVars expr1 in 
    let lis = List.map freeVars exprList in
    List.fold_left 
    (fun currentList newList ->  List.append  currentList 
                                              (List.filter (fun x -> not(List.mem x currentList)) newList)) 
    expr1Fv 
    lis
| Fun(varList,expr)           -> let exprFv = freeVars expr in
    List.fold_left 
    (fun list (y,_) -> List.filter (fun x -> not(equal x y)) list) 
    exprFv 
    varList
| Case(expr1,y1,_,y2,_,expr2) -> 
    let expr1Fv = freeVars expr1 in 
    let expr2Fv = List.filter (fun x -> not(equal x y1) && not(equal x y2)) (freeVars expr2) in 
    List.append 
    expr1Fv 
    (List.filter (fun x -> not(List.mem x expr1Fv)) expr2Fv)
| _ -> [] 

let rec varNameNotBound (name:string) expr = match expr with
| Let((str,_),_,expr1,expr2)              ->  str<> name 
                                              && (varNameNotBound name expr1) 
                                              && (varNameNotBound name expr2)
| Apply1(_,expr)                          ->  (varNameNotBound name expr)
| Apply2(_,expr1,expr2)
| Pair(expr1,expr2)                       ->  (varNameNotBound name expr1) 
                                              && (varNameNotBound name expr2)
| App(expr1,exprList)                     ->  (varNameNotBound name expr1) 
                                              && List.for_all (varNameNotBound name) exprList
| Fun(varList,expr)                       ->  (varNameNotBound name expr) 
                                              && List.for_all (fun ((str,_),_) -> str<>name) varList
| Case(expr1,(str1,_),_,(str2,_),_,expr2) ->  str1<> name 
                                              && str2<> name 
                                              && (varNameNotBound name expr1) 
                                              && (varNameNotBound name expr2)
| _                                       -> true 

let indexOf el lis = 
  let rec indexAux i = function
    | [] -> failwith "Element not found in the list"
    | hd::tl -> if equal hd el then i else indexAux (i+1) tl
  in indexAux 0 lis

let canonicalAlphaRename (name:string) expr =
let freeV = freeVars expr in 
if varNameNotBound name expr then 
let rec canRen expr = match expr with
| Var (s,ty)                      -> let i = indexOf s freeV in Var ((name,i),ty)
| Apply1(op,expr1)                -> Apply1(op,canRen expr1)
| Apply2(op,expr1,expr2)          -> Apply2(op,canRen expr1,canRen expr2)
| Let(y,ty,expr1,expr2)           -> Let(y,ty,canRen expr1,canRen expr2)
| Pair(expr1,expr2)               -> Pair(canRen expr1,canRen expr2)
| App(expr1,exprList)             -> App(canRen expr1,List.map canRen exprList) 
| Fun(varList,expr)               -> Fun(varList,canRen expr)
| Case(expr1,y1,ty1,y2,ty2,expr2) -> Case(canRen expr1,y1,ty1,y2,ty2,canRen expr2)
| _                               -> expr
in canRen expr
else failwith ("variable "^name^" is already used as a bound variable, can't rename free vars canonically with "^name)

(* simple typecheker *)
let rec typeTarget = function
| Const _                       -> Some Real
| Var(_,ty)                     -> Some ty
| Apply1(_,expr)                -> begin 
    match typeTarget expr with 
    | Some Real -> Some Real 
    | _         -> None
    end
| Apply2(_,expr1,expr2)         -> begin
    match typeTarget expr1,typeTarget expr2 with 
    | (Some Real,Some Real) -> Some Real
    | _                     -> None
    end
| Let(_,ty,expr1,expr2)         -> begin
    match typeTarget expr1,typeTarget expr2 with 
    | (Some ty1, Some ty2) when equalTypes ty1 ty   -> Some ty2
    | (_,_)                                         -> None
    end
| Pair(expr1,expr2)             -> begin
  match typeTarget expr1,typeTarget expr2 with 
  | (Some ty1,Some ty2) -> Some(Prod(ty1,ty2))
  | _                   -> None
  end
| Fun(varList,expr)             -> begin
  match typeTarget expr with
  | None      -> None
  | Some ty1  -> Some(Arrow(List.map snd varList,ty1)) 
  end
| App(expr1,exprList)           ->  begin
  match typeTarget expr1,List.map typeTarget exprList with 
  | Some Arrow(tyList1,ty1), tyList2 
    when List.for_all2 
        (fun ty11 ty2 -> match ty2 with | Some ty22 -> equalTypes ty11 ty22 
                                        | _         -> false ) 
          tyList1 
          tyList2  
        -> Some ty1 
  | _   -> None
  end
| Case(expr1,_,ty1,_,ty2,expr2) -> begin
  match typeTarget expr1,typeTarget expr2 with
  | Some Prod(ty3,ty4),Some ty5 when equalTypes ty1 ty3 && equalTypes ty2 ty4 -> Some ty5
  | _                                                                         -> None
  end

let isWellTyped expr = match (typeTarget expr) with
| None      -> false
| Some _    -> true
 
(* interpreter *)

(* checks whether the context captures all the free variables of an expression*)
let contextComplete expr context =
  let exprFv = freeVars expr in 
  List.fold_left (fun acc x -> acc && (List.exists (fun (y,_,_) -> equal y x) context)) true exprFv

let interpretOp1T op expr = match expr with
| Const v -> begin
  match op with
  | Cos  -> Const(cos(v))
  | Sin  -> Const(sin(v))
  | Exp  -> Const(exp(v))
  | Minus-> Const(-.v)
  end
| _       -> failwith "the operand of a unary operator is not a real value"
  
let interpretOp2T op expr1 expr2 = match expr1,expr2 with
| (Const v1,Const v2) -> begin
  match op with
  | Plus  -> Const(v1+.v2)
  | Times -> Const(v1*.v2)
  | Minus -> Const(v1-.v2)
  end
| _                   -> failwith "one operand of a binary operator is not a real value"

(* assumes the context captures all free vars, and is only given values *)
let interpret expr context = 
if not(isWellTyped expr) then failwith "the term is ill-typed";
if not(contextComplete expr context) then failwith "the context does not capture all free vars";
let expr2 = closingTerm expr context in 
let rec interp expr = match expr with
| expr when isValue(expr)         ->  expr
| Apply1(op,expr)                 ->  let v = interp expr in 
                                  interpretOp1T op v
| Apply2(op,expr1,expr2)          ->  let val1 = interp expr1 in 
                                  let val2 = interp expr2 in 
                                  interpretOp2T op val1 val2
| Let(x,ty,expr1,expr2)           ->  let v = interp expr1 in 
                                  interp (subst x ty v expr2)
| Pair(expr1,expr2)               ->  Pair(interp expr1,interp expr2)
| Case(expr1,y1,ty1,y2,ty2,expr2) -> begin match (interp expr1) with
    | Pair(v1,v2) -> interp (subst y2 ty2 v2 (subst y1 ty1 v1 expr2))
    | _           -> failwith "expression should reduce to a pair" end
| App(expr1,exprList)             ->  begin match (interp expr1) with
    | Fun(varList,expr1)  ->  let vList = List.map interp exprList in 
                              interp (List.fold_left2 
                                          (fun expr (x,ty) v -> subst x ty v expr) 
                                          expr1 
                                          varList 
                                          vList)
    | _                   ->  failwith "expression should reduce to a function" end
| _                               ->  expr
in interp expr2