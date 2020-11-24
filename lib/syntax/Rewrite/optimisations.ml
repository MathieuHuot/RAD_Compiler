(* open Syntax.TargetLanguage

module Opti = struct
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
| Tuple(exprList)             -> 
  let lis = List.map allVars exprList in
  List.fold_left 
      (fun currentList newList ->  List.append  currentList 
                                                (List.filter (fun x -> not(List.mem x currentList)) newList)) 
      [] 
      lis
| _                           -> [] 

(* collects the list of unused bound variables *)
let listUnusedVars expr =
  let rec aux expr =  match expr with
    | Let(x, ty, expr1, expr2)             -> (if (List.mem x (freeVars expr2)) then [] else [(x,ty)]) @ aux expr1 @ aux expr2  
    | Var _                                -> []
    | Const _                              -> []
    | Apply1(_, expr)                      -> aux expr
    | Apply2(_, expr1, expr2)              -> aux expr1 @ aux expr2
    | Pair(expr1, expr2)                   -> aux expr1 @ aux expr2   
    | Tuple(exprList)                      -> List.flatten (List.map aux exprList)
    | App(expr, exprList)                  -> aux expr @ List.flatten (List.map aux exprList)
    | Fun(_, expr)                         -> aux expr
    | Case(expr1, x1, ty1, x2, ty2, expr2) -> (if (List.mem x1 (freeVars expr2)) then [] else [(x1,ty1)])
                                              @ (if (List.mem x2 (freeVars expr2)) then [] else [(x2,ty2)]) 
                                              @ aux expr1 
                                              @ aux expr2 
  in aux expr

(* dead code elimination of a list of unused variables *)
(* TODO: think about optimisation strategy, when to do each optimisation. *)
(* Right now I assume lambdas are already evaluated/removed and this elimination is done around the end *)
let deadVarsElim expr = 
let unusedVars = listUnusedVars expr in
let rec aux expr =
  match expr with
  | Let(x, ty,_,expr) 
    when (List.mem (x,ty) unusedVars)    -> expr
  | Case(_, x1, ty1, x2, ty2, expr2) 
    when (List.mem (x1,ty1) unusedVars) 
    && (List.mem (x2,ty2) unusedVars)    -> expr2
  | Var _                                -> expr
  | Const _                              -> expr
  | Apply1(op, expr)                     -> Apply1(op,aux expr)
  | Apply2(op, expr1, expr2)             -> Apply2(op,aux expr1, aux expr2)
  | Let(x, ty, expr1, expr2)             -> Let(x,ty,aux expr1, aux expr2)
  | Pair(expr1, expr2)                   -> Pair(aux expr1, aux expr2)   
  | Tuple(exprList)                      -> Tuple(List.map (aux) exprList)
  | App(expr, exprList)                  -> App(aux expr, List.map (aux) exprList)
  | Fun(varList, expr)                   -> Fun(varList, aux expr)
  | Case(expr1, x1, ty1, x2, ty2, expr2) -> Case(aux expr1,x1,ty1,x2,ty2,aux expr2)
in aux expr
end *)