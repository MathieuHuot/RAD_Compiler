open Operators

module VarSet = CCSet.Make (struct
  type t = Var.t
  let compare x y = CCPair.compare CCString.compare CCInt.compare x y
end)

(* syntax *)
type 'a tuple = 'a list

module Type = struct
  type t = Real | Prod of t * t | Array of int * t

  let rec pp fmt = function
    | Real          -> Format.fprintf fmt "real"
    | Prod (t1, t2) -> Format.fprintf fmt "(%a * %a)" pp t1 pp t2
    | Array (n, t)  -> Format.fprintf fmt "Array[%a][%a]" Format.pp_print_int n pp t

  let to_string = CCFormat.to_string pp

  let rec equal ty1 ty2 =
    match (ty1, ty2) with
    | Real, Real                       -> true
    | Prod (t11, t12), Prod (t21, t22) -> equal t11 t21 && equal t12 t22
    | Array (n1, t1), Array(n2, t2)    -> equal t1 t2 && n1=n2
    | _ -> false

  let rec isGroundType ty = 
    match ty with 
    | Real            -> true
    | Prod (ty1, ty2) -> isGroundType ty1 && isGroundType ty2
    | Array (_,ty)    -> isGroundType ty
end

type t = Var of Var.t * Type.t
            | Const of float 
            | Apply1 of op1 * t 
            | Apply2 of op2 * t * t 
            | Let of Var.t * Type.t * t * t
            | Map of Var.t * Type.t * t * t  (** map x ty e1 [a1,...,an] = [e1[a1/x],...,e1[an/x]] *)
            | Map2 of Var.t * Type.t * Var.t * Type.t * t * t * t (** map2 x ty2 y ty2 e1 [a1,...,an] [b1,...,bn] = [e1[a1/x,b1/y],...,e1[an/x,bn/y]] *)
            | Reduce of Var.t *  Type.t * Var.t * Type.t * t * t * t (** reduce x y e1 z A means reduce (x,y -> e1) from z on A *)
            | Scan of Var.t * Type.t * Var.t * Type.t * t * t * t   (** scan x ty1 y ty2 e1 z A *)
            | Get of int * t (** get i [a1,...,an] returns ai *)
            | Fold of  Var.t * Type.t * Var.t * Type.t * t * t * t(** fold z x ty1 y ty2 e z A means fold A from z with (x:ty1, y:ty2 -> e) *)
            | Array of t list 
            (* | Filter of (Var.t -> bool) *) (* currently not supported as we don't have boolean types *)
            (* | Scatter of t * t * t *)  (* kind of impure and low level: currently not supported *)
            
type context = ((Var.t * Type.t), t) CCList.Assoc.t 

let rec pp fmt = function
  | Var (a, _) -> Var.pp fmt a
  | Const c -> Format.pp_print_float fmt c
  | Apply1 (op, expr) -> Format.fprintf fmt "%a(%a)" pp_op1 op pp expr
  | Apply2 (op, expr1, expr2) ->
    if is_infix op then Format.fprintf fmt "(%a %a %a)" pp expr1 pp_op2 op pp expr2
    else Format.fprintf fmt "(%a %a %a)" pp expr1 pp_op2 op pp expr2
  | Let (x, _t, expr1, expr2) -> Format.fprintf fmt "let %a = %a in@.%a" Var.pp x pp expr1 pp expr2
  | Map (x, _t, expr1, expr2) -> Format.fprintf fmt "map (%a.%a) %a" Var.pp x pp expr1 pp expr2
  | Map2 (x, _t1, y, _t2, expr1, expr2, expr3) -> Format.fprintf fmt "map2 (%a,%a.%a) (%a) (%a)" Var.pp x Var.pp y pp expr1 pp expr2  pp expr3
  | Reduce (x, _t1, y, _t2, expr1, expr2, expr3) -> Format.fprintf fmt "reduce (%a,%a.%a) (%a) (%a)" Var.pp x Var.pp y pp expr1 pp expr2 pp expr3
  | Scan (x, _t1, y, _t2, expr1, expr2, expr3)  -> Format.fprintf fmt "scan (%a,%a.%a) (%a) (%a)" Var.pp x Var.pp y pp expr1 pp expr2 pp expr3
  | Get(n, expr)      -> Format.fprintf fmt "get %a %a" Format.pp_print_int n pp expr
  | Fold (x, _t1, y, _t2, expr1, expr2, expr3)  -> Format.fprintf fmt "fold (%a,%a.%a) (%a) (%a)" Var.pp x Var.pp y pp expr1 pp expr2 pp expr3
  | Array (exprList) -> CCList.pp ~pp_sep:(fun fmt () -> Format.pp_print_string fmt ",") ~pp_start:(fun fmt () -> Format.fprintf fmt "@[[@;<0 2>@[") ~pp_stop:(fun fmt () -> Format.fprintf fmt "@]@,]@]") pp fmt exprList

let to_string = CCFormat.to_string pp  

let rec map f expr = match f expr with
  | Var (_, _) | Const _ as expr -> expr
  | Apply1 (op, expr) -> Apply1(op, map f expr)
  | Apply2 (op, expr1,expr2) -> Apply2(op, map f expr1, map f expr2)
  | Let (y, ty, expr1, expr2) -> Let (y, ty, map f expr1, map f expr2)
  | Map (x, ty, expr1, expr2) -> Map (x, ty, map f expr1, map f expr2)
  | Map2 (x, t1, y, t2, expr1, expr2, expr3) -> Map2 (x, t1, y, t2, map f expr1, map f expr2, map f expr3)
  | Reduce (x, t1, y, t2, expr1, expr2, expr3) -> Reduce (x, t1, y, t2, map f expr1, map f expr2, map f expr3)
  | Scan (x, t1, y, t2, expr1, expr2, expr3) -> Scan (x, t1, y, t2, map f expr1, map f expr2, map f expr3)
  | Get(n, expr) -> Get(n, map f expr)
  | Fold (x, t1, y, t2, expr1, expr2, expr3) -> Fold (x, t1, y, t2, map f expr1, map f expr2, map f expr3)
  | Array (exprList) -> Array (List.map (map f) exprList)

let rec fold f expr a =
  f expr (match expr with
  | Var (_, _) | Const _ -> a
  | Apply1 (_, expr)
  | Get(_, expr) -> a |> fold f expr
  | Apply2 (_, expr1,expr2)
  | Let (_, _, expr1, expr2)
  | Map (_, _, expr1, expr2) -> a |> fold f expr1 |> fold f expr2
  | Map2 (_, _, _, _, expr1, expr2, expr3) 
  | Reduce (_, _, _, _, expr1, expr2, expr3) 
  | Scan (_, _, _, _, expr1, expr2, expr3)
  | Fold (_, _, _, _, expr1, expr2, expr3) -> a |> fold f expr1 |> fold f expr2 |> fold f expr3
  | Array (exprList) -> List.fold_right (fun e a -> fold f e a) exprList a)

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
    |  Map (y, ty1, _, _) -> if (Var.equal x y && Type.equal ty ty1)
      then failwith "subst: trying to substitute a bound variable"
      else expr
    | Map2 (y1, t1, y2, t2, _, _, _) 
    | Reduce (y1, t1, y2, t2, _, _, _) 
    | Scan (y1, t1, y2, t2, _, _, _) 
    | Fold (y1, t1, y2, t2, _, _, _) -> if (Var.equal x y1 && Type.equal ty t1) || (Var.equal x y2 && Type.equal ty t2)
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
  | Let(y, ty1, _, _) | Map (y, ty1, _, _) -> if isInContext (y, ty1) context
      then failwith "simsubst: trying to substitute a bound variable"
      else expr
  | Map2 (y1, t1, y2, t2, _, _, _) 
  | Reduce (y1, t1, y2, t2, _, _, _) 
  | Scan (y1, t1, y2, t2, _, _, _) 
  | Fold (y1, t1, y2, t2, _, _, _) ->  if isInContext (y1, t1) context || isInContext (y2, t2) context
    then failwith "simsubst: trying to substitute a bound variable"
    else expr 
  | _                 -> expr
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
    | Map (x, ty1, expr11, expr12), Map (y, ty2, expr21, expr22) 
                                                          -> Type.equal ty1 ty2 
                                                             && eqT expr12 expr22 alpha_set
                                                             && eqT expr11 expr21 (PVTSet.add ((x, ty1), (y, ty2)) alpha_set)
    | Map2 (x1, t11, y1, t12, expr11, expr12, expr13), Map2 (x2, t21, y2, t22, expr21, expr22, expr23)
    | Reduce (x1, t11, y1, t12, expr11, expr12, expr13), Reduce (x2, t21, y2, t22, expr21, expr22, expr23)
    | Scan (x1, t11, y1, t12, expr11, expr12, expr13), Scan (x2, t21, y2, t22, expr21, expr22, expr23)
    | Fold (x1, t11, y1, t12, expr11, expr12, expr13), Fold (x2, t21, y2, t22, expr21, expr22, expr23) 
                                                          -> Type.equal t11 t21 
                                                             && Type.equal t12 t22
                                                             && eqT expr12 expr22 alpha_set
                                                             && eqT expr13 expr23 alpha_set
                                                             &&  eqT expr11 expr21 (PVTSet.add ((y1, t12), (y2, t22)) (PVTSet.add ((x1, t11), (x2, t21)) alpha_set))                    
    | Get (n1,expr1), Get (n2,expr2) -> eqT expr1 expr2 alpha_set && n1 = n2
    | Array exprList1, Array exprList2 -> CCList.equal (fun expr1 expr2 -> eqT expr1 expr2 alpha_set) exprList1 exprList2
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

let isContextOfValues (cont: context) =
    List.for_all (fun (_,v) -> (isValue v)) cont

let closingTerm expr (cont : context) = if not(isContextOfValues cont) 
    then failwith "closingTerm: context does not only contain values"
    else List.fold_left (fun expr1 ((x,ty),v) -> subst x ty v expr1) expr cont

let freeVar expr =
  fold (fun expr set -> match expr with
| Var (x,_)              -> VarSet.add x set
| Let(y,_, _, _)
| Map(y,_,_,_)  ->
    VarSet.filter (fun x -> not(Var.equal x y)) set
| Map2(y1,_,y2,_,_,_,_)
| Reduce(y1,_,y2,_,_,_,_)  
| Scan(y1,_,y2,_,_,_,_) 
| Fold(y1,_,y2,_,_,_,_) ->  
  VarSet.filter (fun x -> not(Var.equal x y1) && not(Var.equal x y2)) set
| _                      -> set) expr VarSet.empty

(* collects the list of unused bound variables *)
let listUnusedVar expr =
  fold (fun expr l -> match expr with
    | Let(x, ty, _, expr2)             -> (if (VarSet.mem x (freeVar expr2)) then [] else [(x,ty)]) @ l
    | Map(x, ty, expr1, _)             -> (if (VarSet.mem x (freeVar expr1)) then [] else [(x,ty)]) @ l
    | Map2(y1, ty1, y2, ty2, expr,_,_) 
    | Reduce(y1, ty1, y2, ty2, expr,_,_)
    | Scan(y1, ty1, y2, ty2, expr,_,_)
    | Fold(y1, ty1, y2, ty2, expr,_,_) -> (let fv = freeVar expr in List.filter (fun (y,_) -> not(VarSet.mem y fv)) [(y1, ty1); (y2, ty2)]) @ l  
    | _ -> l)
  expr []

let varNameNotBound (name : string) expr =
  let aux = function
    | Let ((str, _), _, _, _) 
    | Map ((str,_), _, _, _) -> str <> name
    | Map2 ((str1,_), _, (str2,_), _, _, _, _) 
    | Reduce ((str1,_), _, (str2,_), _, _, _, _) 
    | Scan ((str1,_), _, (str2,_), _, _, _, _)  
    | Fold ((str1,_), _, (str2,_), _, _, _, _)  -> str1 <> name && str2 <> name
    | _ -> true
  in
  fold (fun expr b -> b && aux expr) expr true

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
let rec inferType expr =
  let open CCResult in
  match expr with
  | Const _ -> Ok Type.Real
  | Var (_, t) -> Ok t
  | Apply1 (_, expr) -> (
        inferType expr >>= function
        | Type.Real -> Ok Type.Real
        | _ -> Error "Argument of Apply1 should be a Type.Real")
  | Apply2 (_, expr1, expr2) -> (
        inferType expr1 >>= function
        | Type.Real -> (
            inferType expr2 >>= function
            | Type.Real -> Ok Type.Real
            | _ -> Error "Argument 2 of Apply2 should be a Type.Real")
        | _ -> Error "Argument 1 of Apply2 should be a Type.Real")
  | Let (_, t, expr1, expr2) ->
      let* t1 = (inferType expr1) in
      if Type.equal t t1 then inferType expr2
      else
        Error
          "in Let binding type of the variable does not correspond to the \
           type of the expression"
  | Map(_, ty, expr1, expr2) ->(
    let* t2 = inferType expr2 in
    match t2 with
    | Array(n, t2) ->
      if Type.equal ty t2 then (inferType expr1 >|= fun t1 -> Type.Array (n, t1))
      else
      Error
        "in Map type of the function argument does not correspond to the \
         type of the elements of the array"
    | _ -> Error "type of the expression should be array")
  | Map2 (_, ty1, _, ty2, expr1, expr2, expr3) -> (
      let* t2 = inferType expr2 in
      let* t3 = inferType expr3 in
      match t2,t3 with
      | Array(n, t2), Array(m, t3) ->
        if not(Type.equal ty1 t2) && not(Type.equal ty2 t3) then
        Error
          "in Map2 type of one of the function argument does not correspond to the \
           type of the elements of the array"
        else if not(n = m) then
          Error
            "in Map2 the two arguments should be vectors of the sam size"
        else (inferType expr1 >|= fun t1 -> Type.Array (n, t1))
      | _ -> Error "type of the expression should be array")
  | Reduce (_, ty1, _, ty2, expr1, expr2, expr3) -> (
        let* t1 = inferType expr1 in
        let* t2 = inferType expr2 in
        let* t3 = inferType expr3 in
        match t3 with
        | Array (_, t3) ->
            if Type.equal ty1 ty2 && Type.equal ty2 t1 && Type.equal t1 t2 && Type.equal t2 t3
            then Ok t1
            else Error
              "in Reduce not all the types are the same"
        | _ -> Error "type of the expression should be array")
  | Scan (_, ty1, _, ty2, expr1, expr2, expr3) -> (
        inferType expr2 >>= fun t2 ->
        if not(Type.equal ty1 t2) 
        then Error "In Scan type of the first argument does not match type of first variable of the function"
        else
        inferType expr3 >>= fun t3 ->
        match t3 with 
          | Array(n, t3) ->
            if not(Type.equal ty2 t3) 
            then Error "In Scan type of the second argument does not match type of second variable of the function"
            else 
            inferType expr1 >>= fun t1 ->
            if not(Type.equal ty1 t1) 
            then Error "In Scan type of the first argument does not match return type of the function"
            else
            Ok (Type.Array (n, t1))
          | _ -> Error "in Scan type of the third argument is not an array"
      )
  | Fold (_, ty1, _, ty2, expr1, expr2, expr3) -> (
        inferType expr2 >>= fun t2 ->
        if not(Type.equal ty1 t2) 
        then Error "In Fold type of the first argument does not match type of first variable of the function"
        else
        inferType expr3 >>= fun t3 ->
        match t3 with 
          | Array(_, t3) ->
            if not(Type.equal ty2 t3) 
            then Error "In Fold type of the second argument does not match type of second variable of the function"
            else 
            inferType expr1 >>= fun t1 ->
            if not(Type.equal ty1 t1) 
            then Error "In Fold type of the first argument does not match return type of the function"
            else
            Ok t1
          | _ -> Error "in Fold type of the third argument is not an array"
      )
  | Get (n, expr) -> (
    inferType expr >>= function
    | Type.Array(m, t1) -> if n<m then Ok t1 
                           else Error "trying to get an element out of bounds of an array"
    | _ -> Error "Argument 2 of Zip should be a Type.Array"
    )
  | Array exprList -> (
    List.map inferType exprList |> flatten_l >>= function
      | [] -> Error "Empty array"
      | h::t -> if CCList.for_all (Type.equal h) t then
          Ok (Type.Array (List.length exprList, h))
        else Error "All elements of an array should have the same type."
  )

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
                               interp expr3              (*TODO*)              
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
         | Map (x, ty, expr1, expr2) -> 
      apply2 (map f) expr1 expr2 >|= fun (expr1, expr2) ->
      Map (x, ty, expr1, expr2)
    | Map2 (x, t1, y, t2, expr1, expr2, expr3) -> 
      applyl (map f) [expr1; expr2; expr3] >|= fun l -> begin match l with 
        | [e1;e2;e3] -> Map2(x, t1, y, t2, e1, e2, e3)
        | _ -> assert false
        end
    | Reduce (x, t1, y, t2, expr1, expr2, expr3) -> 
     applyl (map f) [expr1; expr2; expr3] >|= fun l -> begin match l with 
        | [e1;e2;e3] -> Reduce(x, t1, y, t2, e1, e2, e3)
        | _ -> assert false
        end
    | Scan (x, t1, y, t2, expr1, expr2, expr3) -> 
     applyl (map f) [expr1; expr2; expr3] >|= fun l -> begin match l with 
        | [e1;e2;e3] -> Scan(x, t1, y, t2, e1, e2, e3)
        | _ -> assert false
        end
    | Get(n, expr) -> map f expr >|= fun expr -> Get(n, expr)
    | Fold (x, t1, y, t2, expr1, expr2, expr3) -> 
     applyl (map f) [expr1; expr2; expr3] >|= fun l -> begin match l with 
        | [e1;e2;e3] -> Fold(x, t1, y, t2, e1, e2, e3)
        | _ -> assert false
        end
    | Array (exprList) -> applyl (map f) exprList >|= fun l -> Array l
end
