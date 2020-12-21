open Operators

module VarSet = CCSet.Make (struct
  type t = Var.t
  let compare x y = CCPair.compare CCString.compare CCInt.compare x y
end)

(* syntax *)
type 'a tuple = 'a list

module Type = struct
  type t = Real | Arrow of t tuple * t | NProd of t tuple

let rec pp fmt = function
  | Real -> Format.fprintf fmt "real"
  | Arrow (l, t) ->
      Format.fprintf fmt "%a@ ->@ (%a)"
        (CCList.pp
           ~pp_sep:(fun fmt () -> Format.fprintf fmt "@ ->@ ")
           (fun fmt -> Format.fprintf fmt "(%a)" pp))
        l pp t
  | NProd l ->
      Format.fprintf fmt "(%a)"
        (CCList.pp ~pp_sep:(fun fmt () -> Format.fprintf fmt "@ *@ ") pp)
        l

  let to_string = CCFormat.to_string pp

  let isArrow ty = match ty with Arrow _ -> true | _ -> false

  let rec sourceToTarget (ty : Source.sourceType) : t =
    match ty with
    | Real -> Real
    | Prod (ty1, ty2) ->
        NProd [ sourceToTarget ty1; sourceToTarget ty2 ]

  let rec equal ty1 ty2 =
    match (ty1, ty2) with
    | Real, Real -> true
    | Arrow (tyList1, ret_type1), Arrow (tyList2, ret_type2) ->
        CCList.equal equal tyList1 tyList2 && equal ret_type1 ret_type2
    | NProd tyList1, NProd tyList2 -> CCList.equal equal tyList1 tyList2
    | _ -> false
end

type targetSyn = Var of Var.t * Type.t
                | Const of float
                | Apply1 of op1 * targetSyn
                | Apply2 of op2 * targetSyn * targetSyn
                | Let of Var.t * Type.t * targetSyn * targetSyn
                | Fun of ((Var.t * Type.t) list) * targetSyn
                | App of targetSyn * (targetSyn list)
                | Tuple of targetSyn tuple
                | NCase of targetSyn * ((Var.t * Type.t) list) * targetSyn

type context = ((Var.t * Type.t), targetSyn) CCList.Assoc.t

let varToSyn varList = List.map (fun (x, ty) -> Var(x, ty)) varList

let rec pp fmt = function
  | Var (v, _) -> Var.pp fmt v
  | Const c -> Format.pp_print_float fmt c
  | Apply1 (op, expr) -> Format.fprintf fmt "@[%a(@;<0 2>%a@,)@]" pp_op1 op pp expr
  | Apply2 (op, expr1, expr2) ->
    if is_infix op then Format.fprintf fmt "@[(%a@ %a %a)@]" pp expr1 pp_op2 op pp expr2
    else Format.fprintf fmt "@[(%a %a %a)@]" pp expr1 pp_op2 op pp expr2
  | Let (x, _t, expr1, expr2) -> Format.fprintf fmt "@[<hv>let %a =@;<1 2>@[%a@]@ in@ %a@]" Var.pp x pp expr1 pp expr2
  | Fun (vars, expr) -> Format.fprintf fmt "@[λ%a.@;<1 2>%a@]" (CCList.pp (fun fmt (v,_) -> Var.pp fmt v)) vars pp expr
  | App (expr, exprs) -> Format.fprintf fmt "@[(%a)[@;<0 2>@[%a@]]@]" pp expr (CCList.pp pp) exprs
  | Tuple exprs -> CCList.pp ~pp_start:(fun fmt () -> Format.fprintf fmt "@[{@;<0 2>@[") ~pp_stop:(fun fmt () -> Format.fprintf fmt "@]@ }@]") pp fmt exprs
  | NCase (expr1, vars, expr2) -> Format.fprintf fmt "@[<hv>lets %a =@;<1 2>@[%a@]@ in@ %a@]" (CCList.pp ~pp_sep:(fun fmt () -> Format.pp_print_string fmt ",") (fun fmt (v,_) -> Var.pp fmt v)) vars pp expr1 pp expr2

let to_string = CCFormat.to_string pp

let equalOp1 op1 op2 = match op1,op2 with
  | Cos,Cos     -> true
  | Sin,Sin     -> true
  | Exp,Exp     -> true
  | Minus,Minus -> true
  | Power n, Power m -> n = m
  | _           -> false

let equalOp2 op1 op2 = match op1,op2 with
  | Plus,Plus   -> true
  | Times,Times -> true
  | Minus,Minus -> true
  | _           -> false

let rec map f expr = match f expr with
  | Var (_, _) | Const _ as expr -> expr
  | Apply1 (op, expr) -> Apply1(op, map f expr)
  | Apply2 (op, expr1,expr2) -> Apply2(op, map f expr1, map f expr2)
  | Let (y, ty, expr1, expr2) -> Let (y, ty, map f expr1, map f expr2)
  | Fun (l, expr) -> Fun (l, map f expr)
  | App (expr1, l) -> App (map f expr1, List.map (map f) l)
  | Tuple l -> Tuple (List.map (map f) l)
  | NCase (expr1, lType, expr2) -> NCase (map f expr1, lType, map f expr2)


let rec fold f expr a =
  f expr (match expr with
  | Var (_, _) | Const _ -> a
  | Apply1 (_, expr) -> fold f expr a
  | Apply2 (_, expr1,expr2)
  | Let (_, _, expr1, expr2) -> fold f expr2 (fold f expr1 a)
  | Fun (_, expr) -> fold f expr a
  | App (expr, l) -> List.fold_right (fun e a -> fold f e a) l (fold f expr a)
  | Tuple l -> List.fold_right (fun e a -> fold f e a) l a
  | NCase (expr1, _, expr2) -> fold f expr2 (fold f expr1 a))

(* substitute variable x of type xTy by expr1 in expr2 *)
let subst (x:Var.t) xTy expr1 expr2 =
  map (function
      | Var(a,ty) as expr         -> if Var.equal a x && Type.equal ty xTy then expr1 else expr
      | Let(y,ty,_,_) as expr     -> if (Var.equal x y && Type.equal xTy ty)
        then failwith "sim: trying to substitute a bound variable"
        else expr
      | Fun(varList,_) as expr    -> if (List.exists (fun (y,ty) -> Var.equal x y && Type.equal ty xTy) varList)
        then failwith "sim: trying to substitute a bound variable"
        else expr
      | NCase(_,varList,_) as expr -> if (List.exists (fun (y,ty) -> Var.equal x y && Type.equal ty xTy) varList)
        then failwith "sim: trying to substitute a bound variable"
        else expr
      | expr -> expr
    ) expr2

let isInContext v context = List.mem_assoc v context

let findInContext v context = CCList.Assoc.get ~eq:(CCPair.equal Var.equal Type.equal) v context

let simSubst context expr =
  map (function
      | Var (a,ty1) as expr       -> CCOpt.get_or ~default:expr (findInContext (a,ty1) context)
      | Let(y,ty1,_,_) as expr    -> if isInContext (y,ty1) context
        then failwith "simsubst: trying to substitute a bound variable"
        else expr
      | Fun(varList,_) as expr    -> if (List.exists (fun (y,ty) -> isInContext (y,ty) context) varList)
        then failwith "simsubst: trying to substitute a bound variable"
        else expr
      | NCase(_,varList,_) as expr -> if (List.exists (fun (y,ty) -> isInContext (y,ty) context) varList)
        then failwith "simsubst: trying to substitute a bound variable"
        else expr
      | expr                       -> expr
    ) expr

(*  Checks whether two terms are equal up to alpha renaming.
    Two variables match iff they are the same free variable or they are both bound and equal up to renaming.
    This renaming is checked by carrying an explicit list of pairs of bound variables found so far in the term.
    When an occurence of bound variable is found deeper in the term, we check whether it matches the renaming *)
let equal ?(eq = Float.equal) expr1 expr2 =
let module PVTSet = CCSet.Make (struct
  type t = (Var.t * Type.t) * (Var.t * Type.t)
  let compare = CCPair.compare
  (CCPair.compare (CCPair.compare CCString.compare CCInt.compare) compare)
  (CCPair.compare (CCPair.compare CCString.compare CCInt.compare) compare)
end) in
let rec eqT expr1 expr2 alpha_set = match expr1, expr2 with
| Const a,Const b                                     -> eq a b
| Var (a,ty1),Var (b,ty2)                             -> (Var.equal a b
                                                          || PVTSet.mem  ((a,ty1),(b,ty2)) alpha_set)
                                                         && Type.equal ty1 ty2
| Apply1(op1,expr11),Apply1(op2,expr22)               -> equalOp1 op1 op2
                                                         && eqT expr11 expr22 alpha_set
| Apply2(op1,expr11,expr12),Apply2(op2,expr21,expr22) -> equalOp2 op1 op2
                                                         &&  eqT expr11 expr21 alpha_set
                                                         &&  eqT expr12 expr22 alpha_set
| Let(x,ty1,expr11,expr12), Let(y,ty2,expr21,expr22)  -> Type.equal ty1 ty2
                                                         && eqT expr11 expr21 alpha_set
                                                         &&  eqT expr12 expr22 (PVTSet.add ((x,ty1),(y,ty2)) alpha_set)
| App(expr11,exprList1),App(expr21,exprList2)         -> eqT expr11 expr21 alpha_set
                                                         &&  List.for_all2 (fun x y -> eqT x y alpha_set) exprList1 exprList2
| Fun(varList1,expr1),Fun(varList2,expr2)             -> if CCList.compare_lengths varList1 varList2 <> 0
                                                         then false
                                                         else
                                                         eqT expr1 expr2 (PVTSet.add_list alpha_set (List.combine varList1 varList2))
                                                         && List.for_all2 (fun (_,ty1) (_,ty2) -> Type.equal ty1 ty2) varList1 varList2
| Tuple(exprList1), Tuple(exprList2)                  -> CCList.equal (fun expr1 expr2 -> eqT expr1 expr2 alpha_set) exprList1 exprList2
| NCase(expr11,varList1,expr12), NCase(expr21,varList2,expr22)
                                                      -> if CCList.compare_lengths varList1 varList2<> 0
                                                         then false
                                                         else
                                                         eqT expr11 expr21 alpha_set
                                                         && eqT expr12 expr22 (PVTSet.add_list alpha_set (List.combine varList1 varList2))
| _                                                   -> false
in eqT expr1 expr2 PVTSet.empty

let weakEqual =
  equal ~eq:(fun x y ->
      CCFloat.(
        equal x y
        || equal_precision ~epsilon:(0.00001 * abs x) x y
        || (x = nan && y = nan)
        || (x = -nan && y = -nan)
        || (x = neg_infinity && y = neg_infinity)
        || (x = infinity && y = infinity)))

let rec isValue = function
| Const _           -> true
| Fun(_,_)          -> true
| Tuple(exprList)   -> List.for_all isValue exprList
| _                 -> false

let isContextOfValues (cont : context) = List.for_all (fun (_,v) -> isValue v) cont

let closingTerm expr (cont : context) = if not(isContextOfValues cont) 
    then failwith "closingTerm: context does not only contain values"
    else simSubst cont expr

let freeVar expr =
  fold (fun expr set -> match expr with
| Var (x,_)          -> VarSet.add x set
| Let(y,_,_,_)       ->
    VarSet.filter (fun x -> not(Var.equal x y)) set
| Fun(varList,_)           ->
    VarSet.(diff set (of_list (List.map fst varList)))
| NCase(_,varList,_) ->
  VarSet.(diff set (of_list (List.map fst varList)))
| _                  -> set) expr VarSet.empty

(* collects the list of unused bound variables *)
let listUnusedVar expr =
  fold (fun expr l -> match expr with
    | Let(x, ty, _, expr2)             -> (if (VarSet.mem x (freeVar expr2)) then [] else [(x,ty)]) @ l
    | NCase(_,varList, expr2)          -> (let fv = freeVar expr2 in List.filter (fun (y,_) -> not(VarSet.mem y fv)) varList) @ l
    | _ -> l)
  expr []

let varNameNotBound (name : string) expr =
  let aux = function
    | Let ((str, _), _, _, _) -> str <> name
    | Fun (varList, _) ->
        List.for_all (fun ((str, _), _) -> str <> name) varList
    | NCase (_, varList, _) ->
        List.for_all (fun ((str, _), _) -> str <> name) varList
    | _ -> true
  in
  fold (fun expr b -> b && aux expr) expr true

let indexOf el lis = 
  let rec indexAux i = function
    | [] -> failwith "canonicalAlphaRename: Element not found in the list"
    | hd::tl -> if Var.equal hd el then i else indexAux (i+1) tl
  in indexAux 0 lis

let canonicalAlphaRename (name:string) expr =
let freeV = VarSet.to_list (freeVar expr) in 
if varNameNotBound name expr then 
let canRen = map (function
| Var (s,ty)                      -> let i = indexOf s freeV in Var ((name,i),ty)
| expr                            -> expr)
in canRen expr
else failwith (Printf.sprintf "canonicalAlphaRename: variable %s is already used as a bound variable, can't rename free vars canonically with %s" name name)

(* simple typecheker *)
let rec typeTarget = function
  | Const _ -> Result.Ok Type.Real
  | Var (_, t) -> Result.Ok t
  | Apply1 (_, expr) -> (
      CCResult.(
        typeTarget expr >>= function
        | Type.Real -> Ok Type.Real
        | _ -> Error "Argument of Apply1 should be a Type.Real"))
  | Apply2 (_, expr1, expr2) -> (
      CCResult.(
        typeTarget expr1 >>= function
        | Type.Real -> (
            typeTarget expr2 >>= function
            | Type.Real -> Ok Type.Real
            | _ -> Error "Argumentt 2 of Apply2 should be a Type.Real")
        | _ -> Error "Argument 1 of Apply2 should be a Type.Real"))
  | Let (_, t, expr1, expr2) ->
    CCResult.(
      typeTarget expr1 >>= fun t1 ->
      if Type.equal t t1 then typeTarget expr2
      else
        Error
          "in Let binding type of the variable does not correspond to the \
           type of the expression")
  | Fun (l, expr) ->
    CCResult.(
      typeTarget expr >|= fun texp ->
      Type.Arrow (List.map snd l, texp))
  | App (expr, l) ->
    CCResult.(
      typeTarget expr >>= function
      | Type.Arrow (tyList, retType) ->
        if List.compare_lengths tyList l <> 0 then
          Error "Wrong number of arguments in App"
        else
          List.map typeTarget l |> flatten_l >>= fun l ->
          if CCList.equal Type.equal tyList l then Ok retType
          else Error "Type mismatch with arguments type"
      | _ -> Error "App: expr should be of Type.Arrow type")
  | Tuple l ->
    CCResult.(List.map typeTarget l |> flatten_l >>= fun l -> Ok (Type.NProd l))
  | NCase (expr1, l, expr2) -> (
      CCResult.(
        typeTarget expr1 >>= function
        | Type.NProd tl ->
          if List.for_all2 Type.equal tl (List.map snd l) then
            typeTarget expr2
          else Error "NCase: type mismatch"
        | _ -> Error "NCase: expression 1 should have type Prod"))

let isWellTyped expr = typeTarget expr |> Result.is_ok

(* interpreter *)

(* checks whether the context captures all the free variables of an expression*)
let contextComplete expr context =
  let exprFv = freeVar expr in 
  VarSet.for_all (fun x -> (List.exists (fun ((y,_),_) -> Var.equal y x) context)) exprFv

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
| expr -> Apply1 (op, expr)

let interpretOp2 op expr1 expr2 = match expr1, expr2 with
| (Const v1,Const v2) ->
  begin
  match op with
  | Plus  -> Const(v1+.v2)
  | Times -> Const(v1*.v2)
  | Minus -> Const(v1-.v2)
  end
| expr1, expr2 -> Apply2(op, expr1, expr2)

(* assumes the context captures all free vars, and is only given values *)
let strict_interpret expr context =
if not(isWellTyped expr) then failwith "interpret: the term is ill-typed";
if not(contextComplete expr context) then failwith "interpret: the context does not capture all free vars";
let expr2 = closingTerm expr context in
let rec interp expr = match expr with
| expr when isValue(expr)         ->  expr
| Apply1(op,expr)                 -> begin
                                  let v = interp expr in
                                  match interpretOp1 op v with
                                  | Const _ as expr -> expr
                                  | _       -> failwith "interpretOp1: the operand of a unary operator is not a real value"
                                  end
| Apply2(op,expr1,expr2)          -> begin
                                  let val1 = interp expr1 in
                                  let val2 = interp expr2 in
                                  match interpretOp2 op val1 val2 with
                                  | Const _ as expr -> expr
                                  | _ -> failwith "interpretOp2: one operand of a binary operator is not a real value"
                                  end
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

let interpret expr context =
let expr2 = simSubst context expr in
let rec interp expr = match expr with
| Apply1(op,expr)                 ->  let v = interp expr in
                                  interpretOp1 op v
| Apply2(op,expr1,expr2)          ->  let val1 = interp expr1 in
                                  let val2 = interp expr2 in
                                  interpretOp2 op val1 val2
| Let(x,ty,expr1,expr2)           ->  let v = interp expr1 in
                                  interp (subst x ty v expr2)
| App(expr1,exprList)             ->  begin
  let vList = List.map interp exprList in
  match (interp expr1) with
    | Fun(varList,expr1) -> if not(List.length varList = List.length vList)
                            then App (Fun(varList, interp expr1), vList)
                            else
                            expr1 |> simSubst (List.combine varList vList) |> interp
    | expr               ->  App (expr, vList) end
| Tuple(exprList)                 -> Tuple(List.map interp exprList)
| NCase(expr1,varList,expr2)      -> begin match (interp expr1) with
    | Tuple(exprList) as expr -> if not(List.length varList = List.length exprList)
                                 then NCase(expr, varList, interp expr2)
                                 else
                                 expr2 |> simSubst (List.combine varList exprList) |> interp

    | expr                    -> NCase(expr, varList, interp expr2) end
| expr                               ->  expr
in interp expr2