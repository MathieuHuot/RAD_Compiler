(* Purely functional reverse-mode differentiation. 
   The reverse pass is done using a continuation *)

open Anf
open Syntax
open Syntax.Source

type context = (Syntax.Var.t * Type.t) Target.tuple

let dvar var : Syntax.Var.t * Syntax.Var.t = let str, i = var in (str, i), ("d"^str, i)

let getPos (x,ty) list = 
  let rec aux pos list = match list with
  | [] -> failwith "getPos: element not found"
  | (y,ty2)::tl -> if Syntax.Var.equal x y && Syntax.Source.Type.equal ty ty2 
                    then pos 
                    else aux (pos+1) tl
  in aux 0 list

let rec addToPos i list y = match i, list with
  | _,[]      -> failwith "addToPos: no element at this position in the list"
  | 0,x::tl   -> (Target.Apply2(Plus, x, y))::tl
  | _,x::tl   -> x::(addToPos (i-1) tl y) 

  let rec rad (context: context) (cont : Target.t)  (expr : t) : Target.t * Target.t * context = match expr with
    | Const c                   -> begin
                                    match Target.inferType cont with 
                                    | Result.Ok (Target.Type.Arrow(tyList,_)) ->
                                    let newVar,newTy = (Syntax.Var.fresh(), Target.Type.Real) in 
                                    let newVarList = List.map (fun ty -> Syntax.Var.fresh(), ty) tyList in                  
                                    let newContVarList =  List.append newVarList [(newVar,newTy)] in
                                    let newCont = Target.Fun(newContVarList, Target.App(cont, Target.varToSyn newVarList)) in
                                    Target.Tuple [Target.Const c; newCont], newCont, context
                                    | _ -> failwith "rad: the continuation should be a function"
                                    end
    | Var(x, ty)                -> begin
                                    match Target.inferType cont with 
                                    | Result.Ok(Target.Type.Arrow(tyList,_)) ->
                                    let new_var, new_ty = Syntax.Var.fresh(), Target.Type.from_source ty in  
                                    let newVarList = List.map (fun ty -> Syntax.Var.fresh(), ty) tyList in                          
                                    let newContVarList = List.append newVarList [(new_var, new_ty)] in
                                    let pos_x = getPos (x,ty) context in
                                    let newCont = Target.Fun(newContVarList, 
                                                      Target.App(cont,
                                                          addToPos pos_x (Target.varToSyn newVarList) (Target.Var(new_var, new_ty) )
                                                          )
                                                      ) 
                                    in
                                    Target.Tuple [Target.Var(x, new_ty); newCont], newCont, context
                                    | _ -> failwith "rad: the continuation should be a function"
                                    end
    | Apply1(op, expr)          -> begin
                                    match Target.inferType cont,expr with 
                                    | Result.Ok(Target.Type.Arrow(tyList,_)), Var(x, ty) ->
                                    let new_ty = Target.Type.from_source ty in
                                    let pos_x = getPos (x, ty) context in
                                    let new_var = Syntax.Var.fresh() in 
                                    let newVarList = (List.map (fun ty -> Syntax.Var.fresh(), ty) tyList)  in                         
                                    let newContVarList =  List.append newVarList [(new_var, new_ty)] in
                                    let dop y = begin match op with
                                      | Cos     -> Target.Apply1(Minus,Target.Apply1(Sin, y))
                                      | Sin     -> Target.Apply1(Cos, y)
                                      | Exp     -> Target.Apply1(Exp, y)
                                      | Minus   -> Target.Const (-1.)
                                      | Power 0 -> Target.Const(0.)
                                      | Power n -> Target.Apply2(Times, Target.Const(float_of_int (n-1)),Target.Apply1(Power(n-1),y))
                                      end
                                    in
                                    let partialOp = fun z -> Target.Apply2(Times, dop (Target.Var(x, new_ty)), z) in
                                    let newCont = Target.Fun(newContVarList, 
                                                      Target.App(cont,
                                                          (Target.Var (new_var, new_ty) |> partialOp |> addToPos pos_x (Target.varToSyn newVarList))
                                                          )
                                                      ) 
                                    in
                                    Target.Tuple [Target.Apply1(op, Target.Var(x,new_ty)); newCont], newCont, context
                                    | _,_ -> failwith "rad: the continuation should be a function"
                                    end
    | Apply2(op, expr1, expr2)  -> begin
                                    match Target.inferType cont,expr1,expr2 with 
                                    | Result.Ok(Target.Type.Arrow(tyList,_)), Var(x1, ty1), Var(x2, ty2) ->
                                    let new_ty1 = Target.Type.from_source ty1 in
                                    let pos_x1 = getPos (x1, ty1) context in
                                    let new_ty2 = Target.Type.from_source ty2 in
                                    let pos_x2 = getPos (x2, ty2) context in
                                    let new_var = Syntax.Var.fresh() in 
                                    let newVarList = (List.map (fun ty -> Syntax.Var.fresh(), ty) tyList) in                         
                                    let newContVarList =  List.append newVarList [(new_var, Target.Type.Real)] in
                                    let d1op _ y2 = begin
                                      match op with
                                      | Plus  -> Target.Const(1.)
                                      | Times -> y2
                                      | Minus -> Target.Const(1.)
                                      end
                                    in 
                                    let d2op y1 _ = begin
                                      match op with
                                      | Plus  -> Target.Const(1.)
                                      | Times -> y1
                                      | Minus -> Target.Const(-1.)
                                      end
                                    in
                                    let partial1Op = fun z -> Target.Apply2(Times, d1op (Target.Var(x1, new_ty1)) (Target.Var(x2, new_ty2)), z) in
                                    let partial2Op = fun z -> Target.Apply2(Times, d2op (Target.Var(x1, new_ty1)) (Target.Var(x2, new_ty2)), z) in  
                                    let newCont = Target.Fun(newContVarList, 
                                                      Target.App(cont,
                                                           Target.Var (new_var, Target.Type.Real) |> partial1Op |> addToPos pos_x1 
                                                          (Target.Var (new_var, Target.Type.Real) |> partial2Op |> addToPos pos_x2 (Target.varToSyn newVarList))
                                                          )
                                                      ) 
                                    in
                                    Target.Tuple [Target.Apply2(op, Target.Var(x1, new_ty1), Target.Var(x2, new_ty2)); newCont], newCont, context
                                    | _,_,_ -> failwith "rad: the continuation should be a function"
                                    end
    | Let(x, ty, expr1, expr2)  -> let dexpr1, cont, context = rad context cont expr1 in  
                                   let _, newContVar = dvar x in
                                   match Target.inferType cont with
                                    | Result.Error s    -> failwith (Printf.sprintf "rad: continuation ill-typed:%s" s)
                                    | Result.Ok(newContType) ->
                                   let newCont = Target.Var(newContVar, newContType) in
                                   let newContext = context @ [(x,ty)] in
                                   let dexpr2, newNewCont, context = rad newContext newCont expr2 in
                                   Target.NCase(dexpr1, [(x, Target.Type.from_source ty); (newContVar, newContType)], dexpr2), newNewCont, context

let semiNaiveReverseAD (context: context) (expr: t) : Target.t =
  let new_var_List = List.map (fun (_,ty) -> Syntax.Var.fresh(), Target.Type.from_source ty) context in 
  let id_cont = Target.Fun(new_var_List, Target.Tuple(List.map (fun (x, ty) -> Target.Var(x, ty)) new_var_List)) in
  expr |> SourceAnf.weakAnf |> rad context id_cont |> fun (a,_,_) -> a

(* To actually compute the gradient of a term, we need to initialize tangent variables as in imperative reverse-mode.
    Every tangent variable is initialized at 0 except from the last one which is the returned variable and is initialized at 1 *)
let rec initialize_rad list = match list with
 | []     -> failwith "initialize_rad: the gradient of a closed term won't give you much!" 
 | _::[] -> [Target.Const 1.] 
 | _::tl -> (Target.Const 0.)::initialize_rad tl

let grad (context: context) (expr: t) : Target.t =
  let new_var_List = List.map (fun (_,ty) -> Syntax.Var.fresh(), Target.Type.from_source ty) context in 
  let id_cont = Target.Fun(new_var_List, Target.Tuple(List.map (fun (x, ty) -> Target.Var(x, ty)) new_var_List)) in
  let dexpr, cont, _ = rad context id_cont (SourceAnf.anf expr) in
  match Target.inferType cont with
    | Result.Error s        -> failwith (Printf.sprintf "grad: continuation ill-typed: %s" s)
    | Result.Ok(Target.Type.Arrow(tyList,_)) ->
    let sensitivities = initialize_rad tyList in
    begin 
    match Target.inferType dexpr with
      | Result.Ok(Target.Type.NProd [ty1;ty2]) ->
      let x,dx= dvar (Syntax.Var.fresh()) in
      Target.NCase(dexpr,[(x,ty1);(dx,ty2)],Target.App(Target.Var(dx,ty2),sensitivities))
    | _                   -> failwith "grad: should return a pair"
    end
    | _ -> failwith "grad: continuation should have a function type"
