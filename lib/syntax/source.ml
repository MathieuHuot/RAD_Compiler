open Operators

module VarSet = CCSet.Make (struct
  type t = Var.t
  let compare x y = CCPair.compare CCString.compare CCInt.compare x y
end)

(* syntax *)
type 'a tuple = 'a list

module Type = struct
  type t = Real | Prod of t * t

  let rec pp fmt = function
    | Real -> Format.fprintf fmt "real"
    | Prod (t1, t2) -> Format.fprintf fmt "(%a * %a)" pp t1 pp t2

  let to_string = CCFormat.to_string pp

  let rec equal ty1 ty2 =
    match (ty1, ty2) with
    | Real, Real -> true
    | Prod (t11, t12), Prod (t21, t22) -> equal t11 t21 && equal t12 t22
    | _ -> false
end

type t = Var of Var.t * Type.t
            | Const of float 
            | Apply1 of op1 * t 
            | Apply2 of op2 * t * t 
            | Let of Var.t * Type.t * t * t

type context = ((Var.t * Type.t), t) CCList.Assoc.t

let rec to_string = function
  | Var (v, _) -> Var.to_string v
  | Const c -> string_of_float c
  | Apply1 (op, expr) -> Printf.sprintf "%s(%s)" (to_string_op1 op) (to_string expr)
  | Apply2 (op, expr1, expr2) ->
    if is_infix op then Printf.sprintf "(%s %s %s)" (to_string expr1) (to_string_op2 op) (to_string expr2)
    else Printf.sprintf "(%s %s %s)" (to_string expr1) (to_string_op2 op) (to_string expr2)
  | Let (x, _t, expr1, expr2) -> Printf.sprintf "let %s = %s in\n%s" (Var.to_string x) (to_string expr1) (to_string expr2)

let rec pp fmt = function
  | Var (a, _) -> Var.pp fmt a
  | Const c -> Format.pp_print_float fmt c
  | Apply1 (op, expr) -> Format.fprintf fmt "%a(%a)" pp_op1 op pp expr
  | Apply2 (op, expr1, expr2) ->
    if is_infix op then Format.fprintf fmt "(%a %a %a)" pp expr1 pp_op2 op pp expr2
    else Format.fprintf fmt "(%a %a %a)" pp expr1 pp_op2 op pp expr2
  | Let (x, _t, expr1, expr2) -> Format.fprintf fmt "let %a = %a in@.%a" Var.pp x pp expr1 pp expr2

let rec map f expr = match f expr with
  | Var (_, _) | Const _ as expr -> expr
  | Apply1 (op, expr) -> Apply1(op, map f expr)
  | Apply2 (op, expr1,expr2) -> Apply2(op, map f expr1, map f expr2)
  | Let (y, ty, expr1, expr2) -> Let (y, ty, map f expr1, map f expr2)

let rec fold f expr a =
  f expr (match expr with
  | Var (_, _) | Const _ -> a
  | Apply1 (_, expr) -> fold f expr a
  | Apply2 (_, expr1,expr2)
  | Let (_, _, expr1, expr2) -> fold f expr2 (fold f expr1 a))

let isValue = function
| Const _   -> true
| _         -> false

(* substitute variable x of type ty by expr1 in expr2 *)
let subst (x: Var.t) ty expr1 expr2 = map (fun expr ->
    match expr with
    | Var (a, ty1)      -> if Var.equal a x && Type.equal ty1 ty then expr1 else expr
    | Const _           -> expr
    | Let(y, ty1, _, _) -> if (Var.equal x y && Type.equal ty ty1)
      then failwith "subst: trying to substitute a bound variable"
      else expr
    | _                 -> expr
  ) expr2


let isInContext v context = List.mem_assoc v context

let findInContext v context = List.assoc_opt v context

let simSubst context expr = map (fun expr ->
    match expr with
  | Var (a, ty1)      -> begin match findInContext (a, ty1) context with
                           | None -> expr
                           | Some expr -> expr
                         end
  | Let(y, ty1, _, _) -> if isInContext (y, ty1) context
      then failwith "simsubst: trying to substitute a bound variable"
      else expr
  | _                 -> expr
  ) expr

(*  Checks whether two terms are equal up to alpha renaming.
    Two variables match iff they are the same free variable or they are both bound and equal up to renaming.
    This renaming is checked by carrying an explicit list of pairs of bound variables found so far in the term. 
    When an occurence of bound variable is found deeper in the term, we check whether it matches the renaming *)
let equal ?(eq = Float.equal) expr1 expr2 = 
    let rec eqT expr1 expr2 list = match expr1, expr2 with
    | Const a,Const b                                          -> eq a b
    | Var (a, ty1), Var (b, ty2)                               -> (Var.equal a b || List.mem  ((a, ty1), (b, ty2)) list)
                                                                  && Type.equal ty1 ty2
    | Apply1(op1, expr11),Apply1(op2, expr22)                  -> equalOp1 op1 op2 
                                                                  && eqT expr11 expr22 list
    | Apply2(op1, expr11, expr12),Apply2(op2, expr21, expr22)  -> equalOp2 op1 op2 
                                                                  &&  eqT expr11 expr21 list 
                                                                  &&  eqT expr12 expr22 list
    | Let(x, ty1, expr11, expr12), Let(y, ty2, expr21, expr22) -> Type.equal ty1 ty2 
                                                                  && eqT expr11 expr21 list
                                                                  &&  eqT expr12 expr22 (((x, ty1), (y, ty2))::list)                                                      
    | _                                                        -> false
    in eqT expr1 expr2 []

let isContextOfValues (cont: context) =
    List.for_all (fun (_,v) -> (isValue v)) cont

let closingTerm expr (cont : context) = if not(isContextOfValues cont) 
    then failwith "closingTerm: context does not only contain values"
    else List.fold_left (fun expr1 ((x,ty),v) -> subst x ty v expr1) expr cont

let freeVar expr =
  fold (fun expr set -> match expr with
| Var (x,_)              -> VarSet.add x set
| Let(y,_, _, _)  ->
    VarSet.filter (fun x -> not(Var.equal x y)) set
| _                      -> set) expr VarSet.empty

let rec varNameNotBound (name:string) expr = match expr with
| Let((str,_),_, expr1, expr2) -> str<> name 
                                  && (varNameNotBound name expr1) 
                                  && (varNameNotBound name expr2)
| Apply1(_,expr)               -> (varNameNotBound name expr)
| Apply2(_,expr1, expr2)       -> (varNameNotBound name expr1) 
                                  && (varNameNotBound name expr2)
| _                            -> true 

(* returns theposition of el in lis *)
let indexOf el lis = 
  let rec index_rec i = function
    | [] -> failwith "canonicalAlphaRename: Element not found in the list"
    | hd::tl -> if Var.equal hd el then i else index_rec (i+1) tl
  in index_rec 0 lis

let canonicalAlphaRename (name: string) expr =
let freeV = VarSet.to_list (freeVar expr) in 
if varNameNotBound name expr then 
let canRen expr = map (fun expr -> match expr with
      | Var (s, ty)              -> let i = indexOf s freeV in Var ((name, i), ty)
      | _ -> expr
    ) expr
in canRen expr
else failwith ("canonicalAlphaRename: variable "^name^" is already used as a bound variable, can't rename free vars canonically with "^name)

(* simple typecheker *)
let rec inferType = function
| Const _                 -> Result.Ok Type.Real
| Var(_,ty)               -> Result.Ok ty
| Apply1(_,expr)          -> 
    begin 
    match inferType expr with 
    | Result.Ok Type.Real -> Result.Ok Type.Real 
    | _         -> Result.Error "Argument of Apply1 should be a Type.Real"
    end
| Apply2(_, expr1, expr2) -> 
    begin
    match inferType expr1,inferType expr2 with 
    | (Result.Ok Type.Real, Result.Ok Type.Real) -> Result.Ok Type.Real
    | _                      -> Error "Arguments of Apply2 should be a Type.Real"
    end
| Let(_,ty, expr1, expr2) -> 
    begin
    match inferType expr1,inferType expr2 with 
    | (Result.Ok ty1, Result.Ok ty2) when Type.equal ty1 ty   -> Result.Ok ty2
    | (_,_)                                         ->  Result.Error
          "in Let binding type of the variable does not correspond to the \
           type of the expression"

    end

let isWellTyped expr = inferType expr |> Result.is_ok

(* checks whether the context captures all the free variables of an expression*)
let contextComplete expr context =
    let exprFv = freeVar expr in 
    VarSet.for_all (fun x -> List.exists (fun ((y,_),_) -> Var.equal y x) context) exprFv

(* interpreter *)
let interpret expr context = 
if not(isWellTyped expr) then failwith "interpret: the term is ill-typed";
if not(contextComplete expr context) then failwith "interpret: the context does not capture all free vars";
let expr2 = closingTerm expr context in 
let rec interp = function
| Const a                   -> a
| Apply1(op, expr)          -> let v = interp expr in 
                               interpretOp1 op v
| Apply2(op, expr1, expr2)  -> let val1 = interp expr1 in 
                               let val2 = interp expr2 in 
                               interpretOp2 op val1 val2
| Let(x, ty, expr1, expr2)  -> let v = interp expr1 in 
                               let expr3 = subst x ty (Const v) expr2 in
                               interp expr3
| _                         -> failwith "interpret: the expression should not contain this pattern"
in interp expr2

(** {2 Traverse} *)
module Traverse (S : Strategy.S) = struct
  open S

  let rec map f expr =
    return expr >>= f >>= function
    | (Var (_, _) | Const _) as expr -> return expr
    | Apply1 (op, expr) ->
        map f expr >|= fun expr -> Apply1 (op, expr)
    | Apply2 (op, expr1, expr2) ->
        apply2 (map f) expr1 expr2 >|= fun (expr1,expr2) ->
        Apply2 (op, expr1, expr2)
    | Let (y, ty, expr1, expr2) ->
        apply2 (map f) expr1 expr2 >|= fun (expr1,expr2) ->
        Let (y, ty, expr1, expr2)
end
