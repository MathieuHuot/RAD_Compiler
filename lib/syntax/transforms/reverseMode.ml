(* Purely functional reverse-mode differentiation. 
   The reverse pass is done using a continuation *)

open Anf
open Syntax
open Syntax.Source

type  gradient_variables = (Syntax.Var.t * Type.t) Target.tuple

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

let rec rad (context: gradient_variables) (cont : Target.t)  (expr : t) : Target.t * Target.t * gradient_variables = match expr with
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
                                    let partialOp = fun z -> Target.Apply2(Times, Target.dop op (Target.Var(x, new_ty)), z) in
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
                                    let partial1Op = fun z -> Target.Apply2(Times, Target.d1op op (Target.Var(x1, new_ty1)) (Target.Var(x2, new_ty2)), z) in
                                    let partial2Op = fun z -> Target.Apply2(Times, Target.d2op op (Target.Var(x1, new_ty1)) (Target.Var(x2, new_ty2)), z) in  
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
    | Let(x, ty, expr1, expr2)  -> begin let dexpr1, cont, context = rad context cont expr1 in  
                                   let _, newContVar = Var.dvar x in
                                   match Target.inferType cont with
                                    | Result.Error s    -> failwith (Printf.sprintf "rad: continuation ill-typed:%s" s)
                                    | Result.Ok(newContType) ->
                                   let newCont = Target.Var(newContVar, newContType) in
                                   let newContext = context @ [(x,ty)] in
                                   let dexpr2, newNewCont, context = rad newContext newCont expr2 in
                                   Target.NCase(dexpr1, [(x, Target.Type.from_source ty); (newContVar, newContType)], dexpr2), newNewCont, context end
    | _ -> failwith "TODO"

let semiNaiveReverseAD (context: gradient_variables) (expr: t) : Target.t =
  let new_var_List = List.map (fun (_,ty) -> Syntax.Var.fresh(), Target.Type.from_source ty) context in 
  let id_cont = Target.Fun(new_var_List, Target.Tuple(List.map (fun (x, ty) -> Target.Var(x, ty)) new_var_List)) in
  expr |> SourceAnf.weakAnf |> rad context id_cont |> fun (a,_,_) -> a

(* To actually compute the gradient of a term, we need to initialize tangent variables as in imperative reverse-mode.
    Every tangent variable is initialized at 0 except from the last one which is the returned variable and is initialized at 1 *)
let rec initialize_rad list = match list with
 | []     -> failwith "initialize_rad: the gradient of a closed term won't give you much!" 
 | _::[] -> [Target.Const 1.] 
 | _::tl -> (Target.Const 0.)::initialize_rad tl

let grad (context: gradient_variables) (expr: t) : Target.t =
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
      let x,dx= Var.dvar (Syntax.Var.fresh()) in
      Target.NCase(dexpr,[(x,ty1);(dx,ty2)],Target.App(Target.Var(dx,ty2),sensitivities))
    | _                   -> failwith "grad: should return a pair"
    end
    | _ -> failwith "grad: continuation should have a function type"

let newContinuation (oldCont: Target.t) newTy changeInReturn =
  match oldCont with 
  | Fun(varList, e) -> let newVar = Syntax.Var.fresh() in
                      Target.Fun(varList@[(newVar, newTy)], changeInReturn newVar varList e)
  | _               -> failwith "rad2: the continuation should be a function" 

(* Optimized version of rad where the continuation is not fully computed then optimized, but instead optimized as the term is built. *)
let rec rad2 (context: gradient_variables) (cont : Target.t)  (expr : t) : Target.t * Target.t * gradient_variables =
  match expr with
  | Const c                   ->  let newCont = newContinuation cont Target.Type.Real (fun _ _ e -> e) in
                                  Target.Tuple [Target.Const c; newCont], newCont, context
  | Var(x, ty)                ->  let newTy = Target.Type.from_source ty in
                                  let pos_x = getPos (x, ty) context in
                                  let newCont = newContinuation cont newTy 
                                  (fun newVar varList e -> let (y, ty2) = List.nth varList pos_x in Target.subst y ty2 (Apply2(Plus, Var(y, ty2), Var(newVar, newTy))) e) in
                                  Target.Tuple [Target.Var(x, newTy); newCont], newCont, context
  | Apply1(op, expr)          ->  begin match expr with 
                                    | Var(x,_) ->
                                      let pos_x = getPos (x, Type.Real) context in
                                      let partialOp = fun z -> Target.Apply2(Times, Target.dop op (Target.Var(x, Target.Type.Real)), z) in
                                      let newCont = newContinuation cont Target.Type.Real 
                                      (fun newVar varList e -> let (y, ty2) = List.nth varList pos_x in Target.subst y ty2 (Apply2(Plus, Var(y, ty2), partialOp(Var(newVar, Target.Type.Real)))) e) in
                                      Target.Tuple [Target.Apply1(op, Target.Var(x, Target.Type.Real)); newCont], newCont, context
                                    | _ -> failwith "rad2: a unary operator should be apply to a variable"
                                 end
  | Apply2(op, expr1, expr2)  -> begin match expr1, expr2 with 
                                    | Var(x1,_), Var(x2,_) ->
                                      let pos_x1 = getPos (x1, Type.Real) context in
                                      let pos_x2 = getPos (x2, Type.Real) context in

                                      let partial1Op = fun z -> Target.Apply2(Times, Target.d1op op (Target.Var(x1, Target.Type.Real)) (Target.Var(x2, Target.Type.Real)), z) in
                                      let partial2Op = fun z -> Target.Apply2(Times, Target.d2op op (Target.Var(x1, Target.Type.Real)) (Target.Var(x2, Target.Type.Real)), z) in  
                                      let newCont = newContinuation cont Target.Type.Real 
                                      (fun newVar varList e -> let (y1, ty3) = List.nth varList pos_x1 in
                                                        let (y2, ty4) = List.nth varList pos_x2 in  
                                                        Target.simSubst [((y1, ty3), Apply2(Plus, Var(y1, ty3), partial1Op(Var(newVar, Target.Type.Real)))); 
                                                                         ((y2, ty4), Apply2(Plus, Var(y2, ty4), partial2Op(Var(newVar, Target.Type.Real))))]  
                                                                                e) in
                                      Target.Tuple [Target.Apply2(op, Target.Var(x1, Target.Type.Real), Target.Var(x2, Target.Type.Real)); newCont], newCont, context
                                    | _ -> failwith "rad2:  a binary operator should be apply to two variables"
                                 end
  | Let(x, ty, expr1, expr2)  -> let _, cont, context = rad2 context cont expr1 in   
                                 let newContext = context @ [(x,ty)] in
                                 let dexpr2, cont, context = rad2 newContext cont expr2 in 
                                 Let(x, Target.Type.from_source ty, Target.from_source expr1, dexpr2), cont, context
  | _ -> failwith "TODO"


  (* Initialize the tangent variables for computing a gradient. That is for every primal x, dx=0, except for the output variable z for which dz=1.
     Also projects to the gradient part, so forgets some of the unused primal part. *)
let apply_sensitivities dexpr cont = 
  let f expr = match expr with
    | Target.Tuple([expr1; expr2]) when Target.equal expr2 cont -> 
      begin match cont with 
      | Target.Fun(varList, e) -> Target.simSubst (List.combine varList (initialize_rad varList)) e
      | _ -> failwith "apply_sensitivities: continuation should have a function type"
      end
    | _ -> expr
  in 
  Target.map f dexpr

let grad2 (context: gradient_variables) (expr: t) : Target.t =
  let new_var_List = List.map (fun (_,ty) -> Syntax.Var.fresh(), Target.Type.from_source ty) context in 
  let id_cont = Target.Fun(new_var_List, Target.Tuple(List.map (fun (x, ty) -> Target.Var(x, ty)) new_var_List)) in
  let dexpr, cont, _ = rad2 context id_cont (SourceAnf.anf expr) in
  apply_sensitivities dexpr cont
