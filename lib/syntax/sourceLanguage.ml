open Operators
open Vars

(* syntax *)
type 'a tuple = 'a list

type sourceType = Real | Prod of sourceType * sourceType

and sourceSyn = Var of var * sourceType
            | Const of float 
            | Apply1 of op1 * sourceSyn 
            | Apply2 of op2 * sourceSyn * sourceSyn 
            | Let of var * sourceType * sourceSyn * sourceSyn

type context = (var * sourceType * sourceSyn) list

let rec equalTypes ty1 ty2 = match ty1,ty2 with
| Real,Real                         ->  true
| Prod(ty11,ty12),Prod(ty21,ty22)   ->  equalTypes ty11 ty21 
                                        && equalTypes ty12 ty22
| _                                 ->  false

let isValue = function
| Const _   -> true
| _         -> false

let equalOp1 op1 op2 = match op1,op2 with
| Cos,Cos       -> true
| Sin,Sin       -> true
| Exp,Exp       -> true
| Minus,Minus   -> true
| _ -> false

let equalOp2 op1 op2 = match op1,op2 with
| Plus,Plus     -> true
| Times,Times   -> true
| Minus,Minus   -> true
| _             -> false

(* substitute variable x of type ty by expr1 in expr2 *)
let rec subst (x:var) ty expr1 expr2 = match expr2 with 
| Var (a,ty1)            -> if equal a x && equalTypes ty1 ty then expr1 else expr2
| Const _                -> expr2
| Apply1(op,expr2)       -> Apply1(op,subst x ty expr1 expr2)
| Apply2(op,expr2,expr3) -> Apply2(op,subst x ty expr1 expr2,subst x ty expr1 expr3)
| Let(y,ty1,expr2,expr3) -> if equal x y 
    then failwith "subst: trying to substitute a bound variable"
    else Let(y,ty1,subst x ty expr1 expr2, subst x ty expr1 expr3)

let isInContext (x,ty) context = List.fold_left (fun acc (y,ty2,_) -> acc || (equal x y && equalTypes ty ty2)) false context

let rec findInContext (x,ty) context = match context with
  | []                                                  -> failwith "variable not found in this context"
  | (y,ty2,expr)::_ when equal x y && equalTypes ty ty2 -> expr
  | _::tl                                               -> findInContext (x,ty) tl

 let rec simSubst context expr = match expr with
  | Var (a,ty1) when isInContext (a,ty1) context          
                           -> findInContext (a,ty1) context
  | Apply1(op,expr)        -> Apply1(op,simSubst context expr)
  | Apply2(op,expr1,expr2) -> Apply2(op,simSubst context expr1,simSubst context expr2)
  | Let(y,ty1,expr1,expr2) -> if isInContext (y,ty1) context
      then failwith "simsubst: trying to substitute a bound variable"
      else Let(y,ty1,simSubst context expr1,simSubst context expr2)
  | _                      -> expr

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
    | _                                                   -> false
    in eqT expr1 expr2 []

let isContextOfValues (cont : context) = 
    List.fold_left (fun acc (_,_,v) -> (isValue v) && acc) true cont 

let closingTerm expr (cont : context) = if not(isContextOfValues cont) 
    then failwith "context does not only contain values"
    else List.fold_left (fun expr1 (x,ty,v) -> subst x ty v expr1) expr cont

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
| Let((str,_),_,expr1,expr2) -> str<> name 
                                && (varNameNotBound name expr1) 
                                && (varNameNotBound name expr2)
| Apply1(_,expr)             -> (varNameNotBound name expr)
| Apply2(_,expr1,expr2)      -> (varNameNotBound name expr1) 
                                && (varNameNotBound name expr2)
| _                          -> true 

let indexOf el lis = 
  let rec index_rec i = function
    | [] -> failwith "Element not found in the list"
    | hd::tl -> if equal hd el then i else index_rec (i+1) tl
  in index_rec 0 lis

let canonicalAlphaRename (name:string) expr =
let freeV = freeVars expr in 
if varNameNotBound name expr then 
let rec canRen expr = match expr with
| Var (s,ty)            -> let i = indexOf s freeV in Var ((name,i),ty)
| Apply1(op,expr1)      -> Apply1(op,canRen expr1)
| Apply2(op,expr1,expr2)-> Apply2(op,canRen expr1,canRen expr2)
| Let(y,ty,expr1,expr2) -> Let(y,ty,canRen expr1,canRen expr2) 
| _                     -> expr
in canRen expr
else failwith ("variable "^name^" is already used as a bound variable, can't rename free vars canonically with "^name)

(* simple typecheker *)
let rec typeSource = function
| Const _               -> Some Real
| Var(_,ty)             -> Some ty
| Apply1(_,expr)        -> begin 
    match typeSource expr with 
    | Some Real -> Some Real 
    | _         -> None
    end
| Apply2(_,expr1,expr2) -> begin
    match typeSource expr1,typeSource expr2 with 
    | (Some Real,Some Real) -> Some Real
    | _                     -> None
    end
| Let(_,ty,expr1,expr2) -> begin
    match typeSource expr1,typeSource expr2 with 
    | (Some ty1, Some ty2) when equalTypes ty1 ty   -> Some ty2
    | (_,_)                                         -> None
    end

let isWellTyped expr = match (typeSource expr) with
| None      -> false
| Some _    -> true
    
(* checks whether the context captures all the free variables of an expression*)
let contextComplete expr context =
    let exprFv = freeVars expr in 
    List.fold_left (fun acc x -> acc && (List.exists (fun (y,_,_) -> equal y x) context)) true exprFv

let interpretOp1 op v = match op with
    | Cos  -> cos(v)
    | Sin  -> sin(v)
    | Exp  -> exp(v)
    | Minus-> -.v
    
let interpretOp2 op val1 val2= match op with
    | Plus  -> val1+.val2
    | Times -> val1*.val2
    | Minus -> val1-.val2

(* interpreter *)
let interpret expr context = 
if not(isWellTyped expr) then failwith "the term is ill-typed";
if not(contextComplete expr context) then failwith "the context does not capture all free vars";
let expr2 = closingTerm expr context in 
let rec interp = function
| Const a                -> a
| Apply1(op,expr)        -> let v = interp expr in 
                            interpretOp1 op v
| Apply2(op,expr1,expr2) -> let val1 = interp expr1 in 
                            let val2 = interp expr2 in 
                            interpretOp2 op val1 val2
| Let(x,ty,expr1,expr2)  -> let v = interp expr1 in 
                            let expr3 = subst x ty (Const v) expr2 in
                            interp expr3
| _                      -> failwith "the expression should not contain this pattern"
in interp expr2