open Operators

(* syntax *)
type 'a tuple = 'a list

type targetType = Real
                | Arrow of targetType * targetType
                | NProd of targetType tuple

and targetSyn = Var of Vars.t * targetType
                | Const of float
                | Apply1 of op1 * targetSyn
                | Apply2 of op2 * targetSyn * targetSyn
                | Let of Vars.t * targetType * targetSyn * targetSyn
                | Fun of ((Vars.t * targetType) list) * targetSyn
                | App of targetSyn * (targetSyn list)
                | Tuple of targetSyn tuple
                | NCase of targetSyn * ((Vars.t * targetType) list) * targetSyn

type context = ((Vars.t * targetType), targetSyn) CCList.Assoc.t

let rec to_string = function
  | Var (v, _) -> Vars.to_string v
  | Const c -> string_of_float c
  | Apply1 (op, expr) -> Printf.sprintf "%s(%s)" (to_string_op1 op) (to_string expr)
  | Apply2 (op, expr1, expr2) ->
    if is_infix op then Printf.sprintf "(%s %s %s)" (to_string expr1) (to_string_op2 op) (to_string expr2)
    else Printf.sprintf "(%s %s %s)" (to_string expr1) (to_string_op2 op) (to_string expr2)
  | Let (x, _t, expr1, expr2) -> Printf.sprintf "let %s = %s in\n%s" (Vars.to_string x) (to_string expr1) (to_string expr2)
  | Fun (vars, expr) -> Printf.sprintf "λ%s. %s" (CCList.to_string ~sep:"," (fun (v,_) -> Vars.to_string v) vars) (to_string expr)
  | App (expr, exprs) -> Printf.sprintf "(%s)[%s]" (to_string expr) (CCList.to_string to_string exprs)
  | Tuple exprs -> CCList.to_string ~start:"{" ~stop:"}" to_string exprs
  | NCase (expr1, vars, expr2) -> Printf.sprintf "let %s = %s in\n %s" (CCList.to_string ~sep:"," (fun (v,_) -> Vars.to_string v) vars) (to_string expr1) (to_string expr2)

let rec pp fmt = function
  | Var (v, _) -> Vars.pp fmt v
  | Const c -> Format.pp_print_float fmt c
  | Apply1 (op, expr) -> Format.fprintf fmt "%a(%a)" pp_op1 op pp expr
  | Apply2 (op, expr1, expr2) ->
    if is_infix op then Format.fprintf fmt "(%a %a %a)" pp expr1 pp_op2 op pp expr2
    else Format.fprintf fmt "(%a %a %a)" pp expr1 pp_op2 op pp expr2
  | Let (x, _t, expr1, expr2) -> Format.fprintf fmt "let %a = %a in@.%a" Vars.pp x pp expr1 pp expr2
  | Fun (vars, expr) -> Format.fprintf fmt "λ%a. %a" (CCList.pp ~pp_sep:(fun fmt () -> Format.pp_print_string fmt ",") (fun fmt (v,_) -> Vars.pp fmt v)) vars pp expr
  | App (expr, exprs) -> Format.fprintf fmt "(%a)[%a]" pp expr (CCList.pp ~pp_sep:(fun fmt () -> Format.pp_print_string fmt ", ") pp) exprs
  | Tuple exprs -> CCList.pp ~pp_start:(fun fmt () -> Format.pp_print_string fmt "{") ~pp_stop:(fun fmt () -> Format.pp_print_string fmt "}") ~pp_sep:(fun fmt () -> Format.pp_print_string fmt ",") pp fmt exprs
  | NCase (expr1, vars, expr2) -> Format.fprintf fmt "let %a = %a in@.%a" (CCList.pp ~pp_sep:(fun fmt () -> Format.pp_print_string fmt ",") (fun fmt (v,_) -> Vars.pp fmt v)) vars pp expr1 pp expr2

let isArrow ty = match ty with
| Arrow(_,_)  -> true
| _           -> false

let unfold_arrow t =
  let rec unfold l = function
    | (Real | NProd _) as t -> (l, t)
    | Arrow (ta, te) -> unfold (ta :: l) te
  in
  let l, ret_type = unfold [] t in
  (List.rev l, ret_type)

let rec sourceToTargetType (ty : SourceLanguage.sourceType) : targetType = match ty with
| Real          -> Real
| Prod(ty1,ty2) -> NProd [sourceToTargetType ty1;sourceToTargetType ty2]

let equalOp1 op1 op2 = match op1,op2 with
  | Cos,Cos     -> true
  | Sin,Sin     -> true
  | Exp,Exp     -> true
  | Minus,Minus -> true
  | Power n, Power m when n=m
                -> true
  | _           -> false

let equalOp2 op1 op2 = match op1,op2 with
  | Plus,Plus   -> true
  | Times,Times -> true
  | Minus,Minus -> true
  | _           -> false

let rec equalTypes ty1 ty2 = match ty1,ty2 with
  | Real, Real-> true
  | Arrow(arg_type1, ret_type1), Arrow(arg_type2, ret_type2) ->
    equalTypes arg_type1 arg_type2 && equalTypes ret_type1 ret_type2
  | NProd(tyList1), NProd(tyList2) ->
    if List.length tyList1 <> List.length tyList2
    then false
    else
      List.for_all2 (fun ty11 ty22 -> equalTypes ty11 ty22 ) tyList1 tyList2
  | _  -> false

(* substitute variable x of type xTy by expr1 in expr2 *)
let rec subst (x:Vars.t) xTy expr1 expr2 = match expr2 with 
| Var(a,ty)                       -> if Vars.equal a x && equalTypes ty xTy then expr1 else expr2
| Const _                         -> expr2
| Apply1(op,expr2)                -> Apply1(op,subst x xTy expr1 expr2)
| Apply2(op,expr2,expr3)          -> Apply2(op,subst x xTy expr1 expr2,subst x xTy expr1 expr3)
| Let(y,ty,expr2,expr3)           -> if (Vars.equal x y && equalTypes xTy ty)
                                     then failwith "sim: trying to substitute a bound variable"
                                     else Let(y,ty,subst x xTy expr1 expr2, subst x xTy expr1 expr3)
| Fun(varList,expr2)              -> if (List.exists (fun (y,ty) -> Vars.equal x y && equalTypes ty xTy) varList)
                                     then failwith "sim: trying to substitute a bound variable"
                                     else Fun(varList,subst x xTy expr1 expr2)
| App(expr2,exprList)             -> App(subst x xTy expr1 expr2,List.map (subst x xTy expr1) exprList)
| Tuple(exprList)                 -> Tuple(List.map (subst x xTy expr1) exprList)
| NCase(expr2,varList,expr3)      -> if (List.exists (fun (y,ty) -> Vars.equal x y && equalTypes ty xTy) varList)
                                     then failwith "sim: trying to substitute a bound variable"
                                     else NCase(subst x xTy expr1 expr2, varList, subst x xTy expr1 expr3)

let isInContext v context = List.mem_assoc v context

let findInContext v context = List.assoc v context

 let rec simSubst context expr = match expr with
  | Var (a,ty1) when isInContext (a,ty1) context          
                                    -> findInContext (a,ty1) context
  | Apply1(op,expr)                 -> Apply1(op,simSubst context expr)
  | Apply2(op,expr1,expr2)          -> Apply2(op,simSubst context expr1,simSubst context expr2)
  | Let(y,ty1,expr1,expr2)          -> if isInContext (y,ty1) context
      then failwith "simsubst: trying to substitute a bound variable"
      else Let(y,ty1,simSubst context expr1,simSubst context expr2)
  | Fun(varList,expr2)              -> if (List.exists (fun (y,ty) -> isInContext (y,ty) context) varList)
                                       then failwith "simsubst: trying to substitute a bound variable"
                                       else Fun(varList,simSubst context expr2)
  | App(expr2,exprList)             -> App(simSubst context expr2,List.map (simSubst context) exprList)
  | Tuple(exprList)                 -> Tuple(List.map (simSubst context) exprList)
  | NCase(expr1,varList,expr2)      -> if (List.exists (fun (y,ty) -> isInContext (y,ty) context) varList)
                                       then failwith "simsubst: trying to substitute a bound variable"
                                       else NCase(simSubst context expr1,varList,simSubst context expr2)
  | _                               -> expr 

(*  Checks whether two terms are equal up to alpha renaming.
    Two variables match iff they are the same free variable or they are both bound and equal up to renaming.
    This renaming is checked by carrying an explicit list of pairs of bound variables found so far in the term. 
    When an occurence of bound variable is found deeper in the term, we check whether it matches the renaming *)
let equalTerms expr1 expr2 = 
let rec eqT expr1 expr2 list = match expr1, expr2 with
| Const a,Const b                                     -> a=b
| Var (a,ty1),Var (b,ty2)                             -> (Vars.equal a b || List.mem  ((a,ty1),(b,ty2)) list)
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
| Fun(varList1,expr1),Fun(varList2,expr2)             -> if List.length varList1 <> List.length varList2 
                                                         then false 
                                                         else
                                                         eqT expr1 expr2 (List.append (List.combine varList1 varList2) list) 
                                                         && List.for_all2 (fun (_,ty1) (_,ty2) -> equalTypes ty1 ty2) varList1 varList2
| Tuple(exprList1), Tuple(exprList2)                  -> if List.length exprList1 <> List.length exprList2 
                                                         then false 
                                                         else
                                                         List.for_all2 (fun expr1 expr2 -> eqT expr1 expr2 list) exprList1 exprList2
| NCase(expr11,varList1,expr12), NCase(expr21,varList2,expr22)
                                                      -> if List.length varList1 <> List.length varList2 
                                                         then false 
                                                         else
                                                         eqT expr11 expr21 list 
                                                         && eqT expr12 expr22 (List.append (List.combine varList1 varList2) list)                                                   
| _                                                   -> false
in eqT expr1 expr2 []

let weakEqualTerms expr1 expr2 = 
let rec eqT expr1 expr2 list = match expr1, expr2 with
| Const a,Const b                                     -> CCFloat.(abs (a - b) < 0.00001 || a = nan || b = nan || a = infinity || b = infinity)
| Var (a,ty1),Var (b,ty2)                             -> (Vars.equal a b || List.mem  ((a,ty1),(b,ty2)) list)
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
| Fun(varList1,expr1),Fun(varList2,expr2)             -> if List.length varList1 <> List.length varList2 
                                                         then false 
                                                         else
                                                         eqT expr1 expr2 (List.append (List.combine varList1 varList2) list) 
                                                         && List.for_all2 (fun (_,ty1) (_,ty2) -> equalTypes ty1 ty2) varList1 varList2
| Tuple(exprList1), Tuple(exprList2)                  -> if List.length exprList1 <> List.length exprList2 
                                                         then false 
                                                         else
                                                         List.for_all2 (fun expr1 expr2 -> eqT expr1 expr2 list) exprList1 exprList2
| NCase(expr11,varList1,expr12), NCase(expr21,varList2,expr22)
                                                      -> if List.length varList1 <> List.length varList2 
                                                         then false 
                                                         else
                                                         eqT expr11 expr21 list 
                                                         && eqT expr12 expr22 (List.append (List.combine varList1 varList2) list)                                                   
| _                                                   -> false
in eqT expr1 expr2 []

let rec isValue = function
| Const _           -> true
| Fun(_,_)          -> true
| Tuple(exprList)   -> List.for_all isValue exprList
| _                 -> false

let isContextOfValues (cont : context) = 
    List.fold_left (fun acc (_,v) -> (isValue v) && acc) true cont 

let closingTerm expr (cont : context) = if not(isContextOfValues cont) 
    then failwith "closingTerm: context does not only contain values"
    else simSubst cont expr

let rec freeVars = function
| Var (x,_)                   -> [x]
| Apply1(_,expr)              -> freeVars expr
| Apply2(_,expr1,expr2)       -> 
    let expr1Fv = freeVars expr1 in 
    let expr2Fv = List.filter (fun x -> not (List.mem x expr1Fv)) (freeVars expr2) in 
    List.append expr1Fv expr2Fv
| Let(y,_,expr1,expr2)        ->
    let expr1Fv = freeVars expr1 in 
    let expr2Fv = List.filter (fun x -> not(Vars.equal x y) && not(List.mem x expr1Fv)) (freeVars expr2) in 
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
    (fun list (y,_) -> List.filter (fun x -> not(Vars.equal x y)) list) 
    exprFv 
    varList
| Tuple(exprList)             -> 
    let lis = List.map freeVars exprList in
    List.fold_left 
    (fun currentList newList ->  List.append  currentList 
                                              (List.filter (fun x -> not(List.mem x currentList)) newList)) 
    [] 
    lis
| NCase(expr1,varList,expr2)  -> 
  let expr1Fv = freeVars expr1 in 
  let expr2Fv = List.fold_left (fun list (y,_) -> List.filter (fun x -> not(Vars.equal x y)) list) (freeVars expr2) varList in 
  List.append expr1Fv (List.filter (fun x -> not(List.mem x expr1Fv)) expr2Fv)
| _ -> [] 

let rec varNameNotBound (name:string) expr = match expr with
| Let((str,_),_,expr1,expr2)              ->  str<> name 
                                              && (varNameNotBound name expr1) 
                                              && (varNameNotBound name expr2)
| Apply1(_,expr)                          ->  (varNameNotBound name expr)
| Apply2(_,expr1,expr2)                   ->  (varNameNotBound name expr1) 
                                              && (varNameNotBound name expr2)
| App(expr1,exprList)                     ->  (varNameNotBound name expr1) 
                                              && List.for_all (varNameNotBound name) exprList
| Fun(varList,expr)                       ->  (varNameNotBound name expr) 
                                              && List.for_all (fun ((str,_),_) -> str<>name) varList
| Tuple(exprList)                         ->  List.for_all (varNameNotBound name) exprList
| NCase(expr1,varList,expr2)              ->  varNameNotBound name expr1
                                              && List.for_all (fun ((str,_),_) -> str<>name) varList
                                              && varNameNotBound name expr2
| _                                       ->  true 

let indexOf el lis = 
  let rec indexAux i = function
    | [] -> failwith "canonicalAlphaRename: Element not found in the list"
    | hd::tl -> if Vars.equal hd el then i else indexAux (i+1) tl
  in indexAux 0 lis

let canonicalAlphaRename (name:string) expr =
let freeV = freeVars expr in 
if varNameNotBound name expr then 
let rec canRen expr = match expr with
| Var (s,ty)                      -> let i = indexOf s freeV in Var ((name,i),ty)
| Apply1(op,expr1)                -> Apply1(op,canRen expr1)
| Apply2(op,expr1,expr2)          -> Apply2(op,canRen expr1,canRen expr2)
| Let(y,ty,expr1,expr2)           -> Let(y,ty,canRen expr1,canRen expr2)
| App(expr1,exprList)             -> App(canRen expr1,List.map canRen exprList) 
| Fun(varList,expr)               -> Fun(varList,canRen expr)
| Tuple(exprList)                 -> Tuple(List.map canRen exprList)
| NCase(expr1,varList,expr2)      -> NCase(canRen expr1,varList,canRen expr2)
| _                               -> expr
in canRen expr
else failwith ("canonicalAlphaRename: variable "^name^" is already used as a bound variable, can't rename free vars canonically with "^name)

(* simple typecheker *)
let rec typeTarget = function
  | Const _ -> Result.Ok Real
  | Var (_, t) -> Result.Ok t
  | Apply1 (_, expr) -> (
      CCResult.(
        typeTarget expr >>= function
        | Real -> Ok Real
        | _ -> Error "Argument of Apply1 should be a Real"))
  | Apply2 (_, expr1, expr2) -> (
      CCResult.(
        typeTarget expr1 >>= function
        | Real -> (
            typeTarget expr2 >>= function
            | Real -> Ok Real
            | _ -> Error "Argumentt 2 of Apply2 should be a Real")
        | _ -> Error "Argument 1 of Apply2 should be a Real"))
  | Let (_, t, expr1, expr2) ->
    CCResult.(
      typeTarget expr1 >>= fun t1 ->
      if t = t1 then typeTarget expr2
      else
        Error
          "in Let binding type of the variable does not correspond to the \
           type of the expression")
  | Fun (l, expr) ->
    CCResult.(
      typeTarget expr >|= fun texp ->
      List.fold_right (fun (_, tv) t -> Arrow (tv, t)) l texp)
  | App (exp, l) ->
    CCResult.(
      typeTarget exp >|= unfold_arrow >>= fun (args_type, ret_type) ->
      if List.compare_lengths args_type l <> 0 then
        Error "Wrong number of arguments in App"
      else
        List.map typeTarget l |> flatten_l >>= fun l ->
        if CCList.equal equalTypes args_type l then Ok ret_type
        else Error "Type mismatch with arguments type")
  | Tuple l ->
    CCResult.(List.map typeTarget l |> flatten_l >>= fun l -> Ok (NProd l))
  | NCase (expr1, l, expr2) -> (
      CCResult.(
        typeTarget expr1 >>= function
        | NProd tl ->
          if List.for_all2 equalTypes tl (List.map snd l) then
            typeTarget expr2
          else Error "NCase: type mismatch"
        | _ -> Error "NCase: expression 1 should have type Prod"))

let isWellTyped expr = typeTarget expr |> Result.is_ok

(* interpreter *)

(* checks whether the context captures all the free variables of an expression*)
let contextComplete expr context =
  let exprFv = freeVars expr in 
  List.fold_left (fun acc x -> acc && (List.exists (fun ((y,_),_) -> Vars.equal y x) context)) true exprFv

let interpretOp1 op expr = match expr with
| Const v -> 
  begin
  match op with
  | Cos     -> Const(cos(v))
  | Sin     -> Const(sin(v))
  | Exp     -> Const(exp(v))
  | Minus   -> Const(-.v)
  | Power n -> Const(v ** float_of_int n)
  end
| _       -> failwith "interpretOp1: the operand of a unary operator is not a real value"
  
let interpretOp2 op expr1 expr2 = match expr1, expr2 with
| (Const v1,Const v2) -> 
  begin
  match op with
  | Plus  -> Const(v1+.v2)
  | Times -> Const(v1*.v2)
  | Minus -> Const(v1-.v2)
  end
| _                   -> failwith "interpretOp2: one operand of a binary operator is not a real value"

(* assumes the context captures all free vars, and is only given values *)
let interpret expr context = 
if not(isWellTyped expr) then failwith "interpret: the term is ill-typed";
if not(contextComplete expr context) then failwith "interpret: the context does not capture all free vars";
let expr2 = closingTerm expr context in 
let rec interp expr = match expr with
| expr when isValue(expr)         ->  expr
| Apply1(op,expr)                 ->  let v = interp expr in 
                                  interpretOp1 op v
| Apply2(op,expr1,expr2)          ->  let val1 = interp expr1 in 
                                  let val2 = interp expr2 in 
                                  interpretOp2 op val1 val2
| Let(x,ty,expr1,expr2)           ->  let v = interp expr1 in 
                                  interp (subst x ty v expr2)
| App(expr1,exprList)             ->  begin match (interp expr1) with
    | Fun(varList,expr1)  ->  let vList = List.map interp exprList in
                              if not(List.length varList = List.length vList)
                              then failwith "interp: Function applied to wrong number of arguments"
                              else
                              expr1 |> simSubst (List.combine varList vList) |> interp
    | _                   ->  failwith "interpret: expression should reduce to a function" end
| Tuple(exprList)                 -> Tuple(List.map interp exprList)
| NCase(expr1,varList,expr2)      -> begin match (interp expr1) with
    | Tuple(exprList) -> if not(List.length varList = List.length exprList)
                         then failwith ("interp: NCase argument should be a tuple of size "
                                        ^(string_of_int (List.length varList))
                                        ^"but is of size"
                                        ^(string_of_int (List.length exprList)))
                         else               
                         expr2 |> simSubst (List.combine varList exprList) |> interp

    | _               -> failwith "interpret: expression should reduce to a tuple" end
| _                               ->  expr
in interp expr2
