open Anf
open Syntax.SourceLanguage
open Syntax.TargetLanguage

type context = (Syntax.Vars.var * sourceType) tuple

let naiveReverseADType (ty: sourceType) (retTy: targetType) =
  let rec nRAD (ty: sourceType) = match ty with
  | Real          -> Prod(Real, Arrow([Real],retTy))
  | Prod(ty1,ty2) -> Prod(nRAD ty1, nRAD ty2)
  in nRAD ty

let semiNaiveReverseADType (ty: sourceType) (retTy: targetType) =
    Prod(sourceToTargetType ty, Arrow([sourceToTargetType ty], retTy))

(* takes a primal var as input and return a pair of the primal variable and a new tangent variable *)
(* assumes that no variable from the initial term starts with d, in other words that the new returned variable is fresh *)
let dvar var : Syntax.Vars.var *  Syntax.Vars.var = let str, i = var in (str, i), ("d"^str, i) 

(* Returns the target type for a context in the source language *)
(* let retTypeContext (cont: Syntax.SourceLanguage.context) : targetType = NProd(List.map (fun (_,ty,_) -> sourceToTargetType ty) cont) *)

let varToSyn varList = List.map (fun (x, ty) -> Var(x, ty)) varList

let getPos (x,ty) list = 
  let rec aux pos list = match list with
  | [] -> failwith "element not found"
  | (y,ty2)::tl -> if Syntax.Vars.equal x y && Syntax.SourceLanguage.equalTypes ty ty2 then pos else aux (pos+1) tl
  in aux 0 list

let rec addToPos i list y = match i, list with
  | _,[]      -> failwith "no element at this position in the list"
  | 0,x::tl   -> (Apply2(Plus, x, y))::tl
  | _,x::tl   -> x::(addToPos (i-1) tl y) 

let semiNaiveReverseAD (context: context) (expr: sourceSyn) : targetSyn =
  let new_var_List = List.map (fun (_,ty) -> Syntax.Vars.fresh(), sourceToTargetType ty) context in 
  let id_cont = Fun(new_var_List, Tuple(List.map (fun (x, ty) -> Var(x, ty)) new_var_List)) in

  let rec rad (context: context) (cont : targetSyn)  (expr : sourceSyn) : targetSyn * targetSyn = match expr with
    | Const c                   -> begin
                                    match cont with 
                                    | Fun(varList,_) ->                            
                                    let newContVarList =  List.append 
                                                          (List.map (fun (_,ty) -> Syntax.Vars.fresh(), ty) varList) 
                                                          [(Syntax.Vars.fresh(), Real)] 
                                    in
                                    let newCont = Fun(newContVarList, App(cont, varToSyn newContVarList)) in
                                    Pair(Const c, newCont), newCont
                                    | _ -> failwith "the continuation should be a function"
                                    end
    | Var(x, ty)                -> begin
                                    match cont with 
                                    | Fun(varList,_) ->
                                    let new_ty = sourceToTargetType ty in
                                    let pos_x = getPos (x,ty) context in
                                    let new_var = Syntax.Vars.fresh() in                           
                                    let newContVarList =  List.append 
                                                          (List.map (fun (_,ty) -> Syntax.Vars.fresh(), ty) varList) 
                                                          [(new_var, new_ty)] 
                                    in
                                    let newCont = Fun(newContVarList, 
                                                      App(cont,
                                                          addToPos pos_x (varToSyn newContVarList) (Var(new_var, new_ty) )
                                                          )
                                                      ) 
                                    in
                                    Pair(Var(x, new_ty), newCont), newCont
                                    | _ -> failwith "the continuation should be a function"
                                    end
    | Apply1(op, expr)          -> begin
                                    match cont,expr with 
                                    | Fun(varList,_), Var(x, ty) ->
                                    let new_ty = sourceToTargetType ty in
                                    let pos_x = getPos (x, ty) context in
                                    let new_var = Syntax.Vars.fresh() in 
                                    let newVarList = (List.map (fun (_,ty) -> Syntax.Vars.fresh(), ty) varList)  in                         
                                    let newContVarList =  List.append newVarList [(new_var, new_ty)] in
                                    let dop y = begin match op with
                                      | Cos   -> Apply1(Minus,Apply1(Sin, y))
                                      | Sin   -> Apply1(Cos, y)
                                      | Exp   -> Apply1(Exp, y)
                                      | Minus -> Const (-1.)
                                      end
                                    in
                                    let partialOp = fun z -> Apply2(Times, dop (Var(x, new_ty)), z) in
                                    let newCont = Fun(newContVarList, 
                                                      App(cont,
                                                          (Var (new_var, new_ty) |> partialOp |> addToPos pos_x (varToSyn newVarList))
                                                          )
                                                      ) 
                                    in
                                    Pair(Apply1(op, Var(x,new_ty)), newCont), newCont
                                    | _,_ -> failwith "the continuation should be a function"
                                    end
    | Apply2(op, expr1, expr2)  -> begin
                                    match cont,expr1,expr2 with 
                                    | Fun(varList,_), Var(x1, ty1), Var(x2, ty2) ->
                                    let new_ty1 = sourceToTargetType ty1 in
                                    let pos_x1 = getPos (x1, ty1) context in
                                    let new_ty2 = sourceToTargetType ty2 in
                                    let pos_x2 = getPos (x2, ty2) context in
                                    let new_var = Syntax.Vars.fresh() in 
                                    let newVarList = (List.map (fun (_,ty) -> Syntax.Vars.fresh(), ty) varList) in                         
                                    let newContVarList =  List.append newVarList [(new_var, Real)] in
                                    let d1op _ y2 = begin
                                      match op with
                                      | Plus  -> Const(1.)
                                      | Times -> y2
                                      | Minus -> Const(1.)
                                      end
                                    in 
                                    let d2op y1 _ = begin
                                      match op with
                                      | Plus  -> Const(1.)
                                      | Times -> y1
                                      | Minus -> Const(-1.)
                                      end
                                    in
                                    let partial1Op = fun z -> Apply2(Times, d1op (Var(x1, new_ty1)) (Var(x2, new_ty2)), z) in
                                    let partial2Op = fun z -> Apply2(Times, d2op (Var(x1, new_ty1)) (Var(x2, new_ty2)), z) in  
                                    let newCont = Fun(newContVarList, 
                                                      App(cont,
                                                           Var (new_var, Real) |> partial1Op |> addToPos pos_x1 
                                                          (Var (new_var, Real) |> partial2Op |> addToPos pos_x2 (varToSyn newVarList))
                                                          )
                                                      ) 
                                    in
                                    Pair(Apply2(op, Var(x1, new_ty1), Var(x2, new_ty2)), newCont), newCont
                                    | _,_,_ -> failwith "the continuation should be a function"
                                    end
    | Let(x, ty, expr1, expr2)  -> let dexpr1, cont = rad context cont expr1 in
                                   let x, newContVar = dvar x in
                                   match typeTarget cont with
                                    | None -> failwith "continuation ill-typed" 
                                    | Some(newContType) ->
                                   let newCont = Var(newContVar, newContType) in
                                   let dexpr2, newNewCont = rad context newCont expr2 in
                                   Case(dexpr1, x, sourceToTargetType ty, newContVar, newContType, dexpr2), newNewCont
  in expr |> weakAnf |> rad context id_cont  |> fst