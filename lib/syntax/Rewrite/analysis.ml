(* Some simple functions about variables in a term *)

open Syntax.TargetLanguage

(* collects all variables -- bound and free -- in expr *)
let rec allVars = function
| Const _                     -> []
| Var (x,_)                   -> [x]
| Apply1(_,expr)              -> allVars expr
| Apply2(_,expr1,expr2)       -> 
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
| Tuple(exprList)             -> 
  let lis = List.map allVars exprList in
  List.fold_left 
      (fun currentList newList ->  List.append  currentList 
                                                (List.filter (fun x -> not(List.mem x currentList)) newList)) 
      [] 
      lis
| NCase(expr1,varList,expr2)  -> 
  let expr1Fv = allVars expr1 in 
  let expr2Fv = List.filter (fun x -> not(List.mem x expr1Fv)) (allVars (Fun(varList,expr2))) in
  List.append expr1Fv expr2Fv

(* collects the list of unused bound variables *)
let listUnusedVars expr =
  let rec aux expr =  match expr with
    | Var _                                -> []
    | Const _                              -> []
    | Apply1(_, expr)                      -> aux expr
    | Apply2(_, expr1, expr2)              -> aux expr1 @ aux expr2
    | Let(x, ty, expr1, expr2)             -> (if (List.mem x (freeVars expr2)) then [] else [(x,ty)]) @ aux expr1 @ aux expr2  
    | Tuple(exprList)                      -> List.flatten (List.map aux exprList)
    | App(expr, exprList)                  -> aux expr @ List.flatten (List.map aux exprList)
    | Fun(_, expr)                         -> aux expr
    | NCase(expr1,varList, expr2)          -> aux expr1
                                              @(let fv = freeVars expr2 in List.filter (fun (y,_) -> not(List.mem y fv)) varList)
                                              @aux expr2
  in aux expr
