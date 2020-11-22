open Syntax.TargetLanguage
open Strategies

(* real factorisation*)
let realFact expr = match expr with  
| Apply2(Plus,Apply2(Times,expr1,expr2),Apply2(Times,expr3,expr4)) when expr1 == expr3 -> 
  Apply2(Times,expr1,Apply2(Plus,expr2,expr4))
| Apply2(Plus,Apply2(Times,expr1,expr2),Apply2(Times,expr3,expr4)) when expr2 == expr4 -> 
  Apply2(Times,Apply2(Plus,expr1,expr3),expr2)
| _ -> expr

(* real constant factorisation *)
let realProp expr = match expr with  
| Apply2(Plus,Const a,Const b)    -> Const(a+.b)
| Apply2(Times,Const a,Const b)   -> Const(a*.b)
| _ -> expr

(* exp(a)exp(b) = exp(a+b) *)
let expFact expr = match expr with 
| Apply2(Times,Apply1(Exp,expr1),Apply1(Exp,expr2)) -> Apply1(Exp,Apply2(Plus,expr1,expr2))
| _ -> expr

(* simplifies 0 *)
let realZeroProp expr = match expr with
| Apply2(Times,_,Const 0.)   -> Const 0.
| Apply2(Times,Const 0.,_)   -> Const 0.
| Apply2(Plus,expr,Const 0.) -> expr
| Apply2(Plus,Const 0.,expr) -> expr
| _ -> expr

(* simplifies 1 *)
let realOneProp expr = match expr with
| Apply2(Times,expr,Const 1.) -> expr
| Apply2(Times,Const 1.,expr) -> expr
| _ -> expr

(* CBN evaluates a variable which has a function type *)
let funEval expr = match expr with 
| _ -> expr

(* replaces inlined lambdas in (fun x1...xn.e)[e1...en] to *)
(* let x1=e1 in let x2=e2 in ... in let xn=en in e *)
(* for later optimisations like forward substitution *)
let lambdaReplacement expr = match expr with 
| App(Fun(varList,expr),exprList) -> List.fold_left2 (fun acc (x,ty) expr -> Let(x,ty,expr,acc)) expr (List.rev varList) (List.rev exprList)
| _ -> expr

(* collects all variables -- bound and free -- in expr *)
let rec allVars = function
| Var (x,_)                   -> [x]
| Apply1(_,expr)              -> allVars expr
| Apply2(_,expr1,expr2)
| Pair(expr1,expr2)           -> 
    let expr1Fv = allVars expr1 in 
    let expr2Fv = List.filter (fun x -> not (List.mem x expr1Fv)) (allVars expr2) in 
    List.append expr1Fv expr2Fv
| Let(y,_,expr1,expr2)        ->
    let expr1Fv = List.filter (fun x -> not(Syntax.Vars.equal x y)) (allVars expr1) in 
    let expr2Fv = List.filter (fun x -> not(List.mem x expr1Fv)) (allVars expr2) in 
    y::(List.append expr1Fv expr2Fv)
| App(expr1,exprList)         ->  
    let expr1Fv = allVars expr1 in 
    let lis = List.map allVars exprList in
    List.fold_left (fun currentList newList ->  List.append currentList (List.filter (fun x -> not(List.mem x currentList)) newList)) expr1Fv lis
| Fun(varList,expr)           -> let exprFv = allVars expr in
    List.append (List.map fst varList) (List.fold_left (fun list (y,_) -> List.filter (fun x -> not(Syntax.Vars.equal x y)) list) exprFv varList)
| Case(expr1,y1,_,y2,_,expr2) -> 
    let expr1Fv = allVars expr1 in 
    let expr2Fv = List.filter (fun x -> not(Syntax.Vars.equal x y1) && not(Syntax.Vars.equal x y2)) (allVars expr2) in 
    List.append (List.append expr1Fv (y1::y2::[])) (List.filter (fun x -> not(List.mem x expr1Fv)) expr2Fv)
| _ -> [] 

(* collects the list of unused bound variables *)
let listUnusedVars expr =
  let rec aux expr =  match expr with
  | Let(x,_,e1,e2) -> (if (List.mem x (freeVars e1)) then [] else [x])@ aux e1 @ aux e2  
  | _ -> []
  in aux expr

(* dead code elimination of a list of unused variables *)
(* TODO: think about optimisation strategy, when to do each optimisation. *)
(* Right now I assume lambdas are already evaluated/removed and this elimination is done around the end *)
let deadVarsElim expr list = match expr with
| Let(x,ty,_,e) when (List.mem (x,ty) list) -> e
| _ -> expr 

(* Applies forward substitution: let x=y in e -> e[y/x] where y is a variable *)
let forwardSubst expr = match expr with
| Let(x,_,Var(y,ty),e) -> subst x ty (Var(y,ty)) e
| _ -> expr

(* let x=e1 in let y=e1 in e2 -> let x=e0 in let y=x in e2 *)
let exprFact expr = match expr with
| Let(x1,ty1,e0,Let(x2,ty2,e1,e2)) when (equalTerms e0 e1) -> Let(x1,ty1,e0,Let(x2,ty2,Var(x1,ty1),e2))
| _ -> expr

(* let x=e0 in let y=e1 in e2 -> let y=e1 in let x=e0 in e2 (x not a FV in e1) *)
let letSwap expr = match expr with
| Let(x1,ty1,e0,Let(x2,ty2,e1,e2)) when not(List.mem x1 (freeVars e1)) -> Let(x2,ty2,e1,Let(x1,ty1,e0,e2))
| _ -> expr