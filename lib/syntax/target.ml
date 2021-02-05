open Operators

module VarSet = CCSet.Make (struct
  type t = Var.t
  let compare x y = CCPair.compare CCString.compare CCInt.compare x y
end)

(* syntax *)
type 'a tuple = 'a list

module Type = struct
  type t = Real | Arrow of t tuple * t | NProd of t tuple | Array of int * t

let rec pp fmt = function
  | Real         -> Format.fprintf fmt "real"
  | Arrow (l, t) ->
    begin match l with
    | [] ->
      Format.fprintf fmt "()@ ->@ (%a)" pp t
    | l ->
      Format.fprintf fmt "%a@ ->@ (%a)"
        (CCList.pp
           ~pp_sep:(fun fmt () -> Format.fprintf fmt "@ ->@ ")
           (fun fmt -> Format.fprintf fmt "(%a)" pp))
        l pp t
    end
  | NProd l      ->
      Format.fprintf fmt "(%a)"
        (CCList.pp ~pp_sep:(fun fmt () -> Format.fprintf fmt "@ *@ ") pp)
        l
  | Array (n, t)  -> Format.fprintf fmt "Array[%a][%a]" Format.pp_print_int n pp t

  let to_string = CCFormat.to_string pp

  let isArrow ty = match ty with Arrow _ -> true | _ -> false

  let rec from_source (ty : Source.Type.t) : t =
    match ty with
    | Real            -> Real
    | Prod (ty1, ty2) -> NProd [ from_source ty1; from_source ty2 ]
    | Array (n, ty)   -> Array (n, from_source ty) 

  let rec equal ty1 ty2 =
    match (ty1, ty2) with
    | Real, Real -> true
    | Arrow (tyList1, ret_type1), Arrow (tyList2, ret_type2) ->
        CCList.equal equal tyList1 tyList2 && equal ret_type1 ret_type2
    | NProd tyList1, NProd tyList2 -> CCList.equal equal tyList1 tyList2
    | Array (n, t1), Array(m, t2)            -> equal t1 t2 &&  n = m
    | _ -> false

    let rec isGroundType ty = 
      match ty with 
      | Real          -> true
      | NProd tyList  -> List.for_all isGroundType tyList
      | Array (_, ty) -> isGroundType ty
      | _             -> false 

  module Parse = struct
    open CCParse

    let pReal =
      map
        (function "real" -> Real | _ -> assert false)
        (skip_white *> string "real")

    let pNProd self =
      U.list ~start:"(" ~stop:")" ~sep:"*" self >|= fun l -> NProd l

    let pArray self =
      skip_white *> string "Array[" *> skip_white *> U.int >>= fun n ->
      skip_white *> string "][" *> skip_white *> self >>= fun t ->
      string "]" >|= fun _ -> Array (n, t)

    let pArrow self =
      skip_white
      *> (try_
            ( string "()" *> skip_white *> string "->" *> skip_white
            *> string "(" *> skip_white *> self <* skip_white <* string ")"
            >|= fun expr -> Arrow ([], expr) )
         <|> ( U.list ~start:"" ~stop:"" ~sep:"->"
                 (string "(" *> skip_white *> self <* skip_white <* string ")")
             >>= fun l ->
               match List.rev l with
               | [] | _::[] -> fail "Arrow: empty list"
               | h :: t -> return (Arrow (List.rev t, h)) ))

    let pType =
      fix @@ fun self ->
      try_ (pArrow self) <|> try_ pReal <|> try_ (pNProd self) <|> pArray self

    let of_string = parse_string pType
  end
end

(*TODO: might need to add map3 ...*)
type t = Var of Var.t * Type.t
                | Const of float
                | Apply1 of op1 * t
                | Apply2 of op2 * t * t
                | Let of Var.t * Type.t * t * t
                | Fun of ((Var.t * Type.t) list) * t
                | App of t * (t list)
                | Tuple of t tuple
                | NCase of t * ((Var.t * Type.t) list) * t
                | Map of Var.t * Type.t * t * t  (** map x ty e1 [a1,...,an] = [e1[a1/x],...,e1[an/x]] *)
                | Map2 of Var.t * Type.t * Var.t * Type.t * t * t * t (** map2 x ty1 y ty2 e1 [a1,...,an] [b1,...,bn] = [e1[a1/x,b1/y],...,e1[an/x,bn/y]] *)
                | Reduce of Var.t *  Type.t * Var.t * Type.t * t * t * t (** reduce x y e1 z A means reduce (x,y -> e1) from z on A *)
                | Scan of Var.t * Type.t * Var.t * Type.t * t * t * t   (** scan x ty1 y ty2 e1 z A *)
                | Zip of t * t (** zip [a1,...,an] [b1,...,bn] = [(a1,b1),...,(an,bn)] *)
                | Unzip of t (** Unzip [(a1,b1),...,(an,bn)] = [a1,...,an],[b1,...,bn] =  *)
                | Zip3 of t * t * t (** zip [a1,...,an] [b1,...,bn] [c1,...,cn] = [(a1,b1,c1),...,(an,bn,cn)] *)
                | Unzip3 of t (** Unzip  [(a1,b1,c1),...,(an,bn,cn)] = [a1,...,an],[b1,...,bn], [c1,...,cn] =  *)
                | Get of int * t (** get i [a1,...,an] returns ai *)
                | Fold of  Var.t * Type.t * Var.t * Type.t * t * t * t(** fold z x ty1 y ty2 e z A means fold A from z with (x:ty1, y:ty2 -> e). It's a fold LEFT operator. *)
                | Array of t list 

type context = ((Var.t * Type.t), t) CCList.Assoc.t

let varToSyn varList = List.map (fun (x, ty) -> Var(x, ty)) varList

let rec from_source (expr: Source.t) : t = match expr with
  | Const c                  -> Const c
  | Var(x, ty)               -> Var(x, Type.from_source ty)
  | Apply1(op, expr)         -> Apply1(op, from_source expr)
  | Apply2(op, expr1, expr2) -> Apply2(op, from_source expr1, from_source expr2)
  | Let(x, ty, expr1, expr2) -> Let(x, Type.from_source ty, from_source expr1, from_source expr2)
  | Map (x, ty, expr1, expr2) -> Map (x, Type.from_source ty, from_source expr1, from_source expr2)
  | Map2 (x, t1, y, t2, expr1, expr2, expr3) -> Map2 (x, Type.from_source t1, y, Type.from_source t2, from_source expr1, from_source expr2, from_source expr3)
  | Reduce (x, t1, y, t2, expr1, expr2, expr3) -> Reduce (x, Type.from_source t1, y, Type.from_source t2, from_source expr1, from_source expr2, from_source expr3)
  | Scan (x, t1, y, t2, expr1, expr2, expr3) -> Scan (x, Type.from_source t1, y, Type.from_source t2, from_source expr1, from_source expr2, from_source expr3)
  | Get(n, expr) -> Get(n, from_source expr)
  | Fold (x, t1, y, t2, expr1, expr2, expr3) -> Fold (x, Type.from_source t1, y, Type.from_source t2, from_source expr1, from_source expr2, from_source expr3)
  | Array (exprList) -> Array(List.map from_source exprList) 

let rec pp fmt = function
  | Var (a, t) -> Format.fprintf fmt "%a:%a" Var.pp a Type.pp t
  | Const c -> Format.fprintf fmt "%.18g" c
  | Apply1 (op, expr) -> Format.fprintf fmt "@[%a(@;<0 2>%a@,)@]" pp_op1 op pp expr
  | Apply2 (op, expr1, expr2) ->
    if is_infix op then Format.fprintf fmt "@[(%a@ %a %a)@]" pp expr1 pp_op2 op pp expr2
    else Format.fprintf fmt "@[(%a %a %a)@]" pp expr1 pp_op2 op pp expr2
  | Let (x, t, expr1, expr2) -> Format.fprintf fmt "@[<hv>let %a:%a =@;<1 2>@[%a@]@ in@ %a@]" Var.pp x Type.pp t pp expr1 pp expr2
  | Fun (vars, expr) -> Format.fprintf fmt "@[λ%a.@;<1 2>%a@]" (CCList.pp (fun fmt (v,t) -> Format.fprintf fmt "%a:%a" Var.pp v Type.pp t)) vars pp expr
  | App (expr, exprs) -> Format.fprintf fmt "@[(%a)[@;<0 2>@[%a@]]@]" pp expr (CCList.pp pp) exprs
  | Tuple exprs -> CCList.pp ~pp_start:(fun fmt () -> Format.fprintf fmt "@[{@;<0 2>@[") ~pp_stop:(fun fmt () -> Format.fprintf fmt "@]@,}@]") pp fmt exprs
  | NCase (expr1, vars, expr2) -> Format.fprintf fmt "@[<hv>lets %a =@;<1 2>@[%a@]@ in@ %a@]" (CCList.pp ~pp_sep:(fun fmt () -> Format.pp_print_string fmt ",") (fun fmt (v,t) -> Format.fprintf fmt "%a:%a" Var.pp v Type.pp t)) vars pp expr1 pp expr2
  | Map (x, t, expr1, expr2) -> Format.fprintf fmt "@[map@;<1 2>(%a:%a.%a)@ (%a)@]" Var.pp x Type.pp t pp expr1 pp expr2
  | Map2 (x, t1, y, t2, expr1, expr2, expr3) -> Format.fprintf fmt "@[map2@;<1 2>(%a:%a,%a:%a.%a)@ (%a)@ (%a)@]" Var.pp x Type.pp t1 Var.pp y Type.pp t2 pp expr1 pp expr2  pp expr3
  | Reduce (x, t1, y, t2, expr1, expr2, expr3) -> Format.fprintf fmt "@[reduce@;<1 2>(%a:%a,%a:%a.%a)@ (%a)@ (%a)@]" Var.pp x Type.pp t1 Var.pp y Type.pp t2 pp expr1 pp expr2 pp expr3
  | Scan (x, t1, y, t2, expr1, expr2, expr3)  -> Format.fprintf fmt "@[scan@;<1 2>(%a:%a,%a:%a.%a)@ (%a)@ (%a)@]" Var.pp x Type.pp t1 Var.pp y Type.pp t2 pp expr1 pp expr2 pp expr3
  | Zip(expr1, expr2) -> Format.fprintf fmt "@[zip@;<1 2>(%a) (%a)@]" pp expr1 pp expr2
  | Zip3(expr1, expr2, expr3) -> Format.fprintf fmt "@[zip3@;<1 2>(%a) (%a) (%a)@]" pp expr1 pp expr2 pp expr3
  | Unzip(expr) -> Format.fprintf fmt "@[unzip@;<1 2>(%a)@]" pp expr
  | Unzip3(expr) -> Format.fprintf fmt "@[unzip3@;<1 2>(%a)@]" pp expr 
  | Get(n, expr)      -> Format.fprintf fmt "get %i@;<1 2>(%a)" n pp expr
  | Fold (x, t1, y, t2, expr1, expr2, expr3)  -> Format.fprintf fmt "@[fold(%a:%a,%a:%a.%a)@ (%a)@ (%a)@]" Var.pp x Type.pp t1 Var.pp y Type.pp t2 pp expr1 pp expr2 pp expr3
  | Array (exprList) -> CCList.pp ~pp_sep:(fun fmt () -> Format.pp_print_string fmt ",") ~pp_start:(fun fmt () -> Format.fprintf fmt "@[[@;<0 2>@[") ~pp_stop:(fun fmt () -> Format.fprintf fmt "@]@,]@]") pp fmt exprList

let to_string = CCFormat.to_string pp

let rec map f expr = (match expr with
  | Var (_, _) | Const _ as expr -> expr
  | Apply1 (op, expr) -> Apply1(op, map f expr)
  | Apply2 (op, expr1,expr2) -> Apply2(op, map f expr1, map f expr2)
  | Let (y, ty, expr1, expr2) -> Let (y, ty, map f expr1, map f expr2)
  | Fun (l, expr) -> Fun (l, map f expr)
  | App (expr1, l) -> App (map f expr1, List.map (map f) l)
  | Tuple l -> Tuple (List.map (map f) l)
  | NCase (expr1, lType, expr2) -> NCase (map f expr1, lType, map f expr2)
  | Map (x, ty, expr1, expr2) -> Map (x, ty, map f expr1, map f expr2)
  | Map2 (x, t1, y, t2, expr1, expr2, expr3) -> Map2 (x, t1, y, t2, map f expr1, map f expr2, map f expr3)
  | Reduce (x, t1, y, t2, expr1, expr2, expr3) -> Reduce (x, t1, y, t2, map f expr1, map f expr2, map f expr3)
  | Scan (x, t1, y, t2, expr1, expr2, expr3) -> Scan (x, t1, y, t2, map f expr1, map f expr2, map f expr3)
  | Zip(expr1, expr2) ->  Zip(map f expr1, map f expr2)
  | Zip3(expr1, expr2, expr3) ->  Zip3(map f expr1, map f expr2, map f expr3)
  | Unzip(expr) ->  Unzip(map f expr)
  | Unzip3(expr) ->  Unzip3(map f expr)
  | Get(n, expr) -> Get(n, map f expr)
  | Fold (x, t1, y, t2, expr1, expr2, expr3) -> Fold (x, t1, y, t2, map f expr1, map f expr2, map f expr3)
  | Array (exprList) -> Array (List.map (map f) exprList)
  ) |> f

  let rec fold f expr a =
    f expr (match expr with
    | Var (_, _) | Const _ -> a
    | Apply1 (_, expr)
    | Fun (_, expr)
    | Get(_, expr) 
    | Unzip(expr)
    | Unzip3(expr) -> a |> fold f expr
    | Apply2 (_, expr1,expr2)
    | Let (_, _, expr1, expr2)
    | Zip(expr1, expr2)
    | Map (_, _, expr1, expr2)
    | NCase (expr1, _, expr2)  -> a |> fold f expr1 |> fold f expr2
    | Map2 (_, _, _, _, expr1, expr2, expr3) 
    | Reduce (_, _, _, _, expr1, expr2, expr3) 
    | Scan (_, _, _, _, expr1, expr2, expr3)
    | Fold (_, _, _, _, expr1, expr2, expr3)
    | Zip3(expr1, expr2, expr3) -> a |> fold f expr1 |> fold f expr2 |> fold f expr3
    | Array exprList
    | Tuple exprList -> List.fold_right (fun e a -> fold f e a) exprList a
    | App (expr, exprList) -> a |> fold f expr |> List.fold_right (fun e a -> fold f e a) exprList)

(* substitute variable x of type xTy by expr1 in expr2 *)
let subst (x:Var.t) xTy expr1 expr2 =
  map (function
      | Var(a,ty) as expr         -> if Var.equal a x && Type.equal ty xTy then expr1 else expr
      | Let(y,ty,_,_) as expr     -> if (Var.equal x y && Type.equal xTy ty)
        then failwith "subst: trying to substitute a bound variable"
        else expr
      | Fun(varList,_) as expr    -> if (List.exists (fun (y,ty) -> Var.equal x y && Type.equal ty xTy) varList)
        then failwith "subst: trying to substitute a bound variable"
        else expr
      | NCase(_,varList,_) as expr -> if (List.exists (fun (y,ty) -> Var.equal x y && Type.equal ty xTy) varList)
        then failwith "subst: trying to substitute a bound variable"
        else expr
      |  Map (y, ty1, _, _)  as expr -> if (Var.equal x y && Type.equal xTy ty1)
        then failwith "subst: trying to substitute a bound variable"
        else expr
      | Map2 (y1, t1, y2, t2, _, _, _) 
      | Reduce (y1, t1, y2, t2, _, _, _) 
      | Scan (y1, t1, y2, t2, _, _, _) 
      | Fold (y1, t1, y2, t2, _, _, _) as expr -> if (Var.equal x y1 && Type.equal xTy t1) || (Var.equal x y2 && Type.equal xTy t2)
        then failwith "subst: trying to substitute a bound variable"
        else expr  
      | expr -> expr
    ) expr2

let isInContext v context = List.mem_assoc v context

let findInContext v context = CCList.Assoc.get ~eq:(CCPair.equal Var.equal Type.equal) v context

let simSubst context expr =
  map (function
      | Var (a,ty1) as expr       -> CCOpt.get_or ~default:expr (findInContext (a,ty1) context)
      | Let(y,ty1,_,_) | Map (y, ty1, _, _) as expr    -> if isInContext (y,ty1) context
        then failwith "simsubst: trying to substitute a bound variable"
        else expr
      | Fun(varList,_) as expr    -> if (List.exists (fun (y,ty) -> isInContext (y,ty) context) varList)
        then failwith "simsubst: trying to substitute a bound variable"
        else expr
      | NCase(_,varList,_) as expr -> if (List.exists (fun (y,ty) -> isInContext (y,ty) context) varList)
        then failwith "simsubst: trying to substitute a bound variable"
        else expr
      | Map2 (y1, t1, y2, t2, _, _, _) 
      | Reduce (y1, t1, y2, t2, _, _, _) 
      | Scan (y1, t1, y2, t2, _, _, _) 
      | Fold (y1, t1, y2, t2, _, _, _) as expr ->  if isInContext (y1, t1) context || isInContext (y2, t2) context
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
| Zip (expr11, expr12), Zip (expr21, expr22)          -> eqT expr11 expr21 alpha_set 
                                                         &&  eqT expr12 expr22 alpha_set
| Zip3 (expr11, expr12, expr13), Zip3 (expr21, expr22, expr23) 
                                                      -> eqT expr11 expr21 alpha_set 
                                                         &&  eqT expr12 expr22 alpha_set    
                                                         &&  eqT expr13 expr23 alpha_set   
| Unzip(expr1), Unzip(expr2)                          -> eqT expr1 expr2 alpha_set
| Unzip3(expr1), Unzip3(expr2)                        -> eqT expr1 expr2 alpha_set                                                                                             
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

let rec isValue = function
| Const _           -> true
| Fun(_,_)          -> true
| Tuple(exprList)   -> List.for_all isValue exprList
| Array(exprList)   -> List.for_all isValue exprList
| _                 -> false

(* let isContextOfValues (cont : context) = List.for_all (fun (_,v) -> isValue v) cont *)

(* let closingTerm expr (cont : context) = if not(isContextOfValues cont) 
    then failwith "closingTerm: context does not only contain values"
    else simSubst cont expr *)

let freeVar expr =
  fold (fun expr set -> match expr with
| Var (x,_)          -> VarSet.add x set
| Let(y,_,_,_)       
| Map(y,_,_,_)  ->
  VarSet.filter (fun x -> not(Var.equal x y)) set
| Fun(varList,_)           ->
  VarSet.(diff set (of_list (List.map fst varList)))
| NCase(_,varList,_) ->
  VarSet.(diff set (of_list (List.map fst varList)))
| Map2(y1,_,y2,_,_,_,_)
| Reduce(y1,_,y2,_,_,_,_)  
| Scan(y1,_,y2,_,_,_,_) 
| Fold(y1,_,y2,_,_,_,_) ->  
  VarSet.filter (fun x -> not(Var.equal x y1) && not(Var.equal x y2)) set
| _                  -> set) expr VarSet.empty

(* collects the list of unused bound variables *)
let listUnusedVar expr =
  fold (fun expr l -> match expr with
    | Let(x, ty, _, expr2)             -> (if (VarSet.mem x (freeVar expr2)) then [] else [(x,ty)]) @ l
    | NCase(_,varList, expr2)          -> (let fv = freeVar expr2 in List.filter (fun (y,_) -> not(VarSet.mem y fv)) varList) @ l
    | Map(x, ty, expr1, _)             -> (if (VarSet.mem x (freeVar expr1)) then [] else [(x,ty)]) @ l
    | Map2(y1, ty1, y2, ty2, expr,_,_) 
    | Reduce(y1, ty1, y2, ty2, expr,_,_)
    | Scan(y1, ty1, y2, ty2, expr,_,_)
    | Fold(y1, ty1, y2, ty2, expr,_,_) -> (let fv = freeVar expr in List.filter (fun (y,_) -> not(VarSet.mem y fv)) [(y1, ty1); (y2, ty2)]) @ l  
    | _ -> l)
  expr []

let varNameNotBound (name : string) expr =
  let aux = function
    | Let ((str, _), _, _, _) -> str <> name
    | Fun (varList, _) ->
        List.for_all (fun ((str, _), _) -> str <> name) varList
    | NCase (_, varList, _) ->
        List.for_all (fun ((str, _), _) -> str <> name) varList
    | Map ((str,_), _, _, _) -> str <> name
    | Map2 ((str1,_), _, (str2,_), _, _, _, _) 
    | Reduce ((str1,_), _, (str2,_), _, _, _, _) 
    | Scan ((str1,_), _, (str2,_), _, _, _, _)  
    | Fold ((str1,_), _, (str2,_), _, _, _, _)  -> str1 <> name && str2 <> name
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
  | Fun (l, expr) ->
      let+ texp = inferType expr in
      Type.Arrow (List.map snd l, texp)
  | App (expr, l) -> (
      inferType expr >>= function
      | Type.Arrow (tyList, retType) ->
        if List.compare_lengths tyList l <> 0 then
          Error "Wrong number of arguments in App"
        else
          List.map inferType l |> flatten_l >>= fun l ->
          if CCList.equal Type.equal tyList l then Ok retType
          else Error "Type mismatch with arguments type"
      | _ -> Error "App: expr should be of Type.Arrow type")
  | Tuple l ->
    List.map inferType l |> flatten_l >|= fun l -> Type.NProd l
  | NCase (expr1, l, expr2) -> (
        inferType expr1 >>= function
        | Type.NProd tl ->
          if List.for_all2 Type.equal tl (List.map snd l) then
            inferType expr2
          else Error "NCase: type mismatch"
        | _ -> Error "NCase: expression 1 should have type Prod")
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
  | Zip (expr1, expr2) -> (
    inferType expr1 >>= function
    | Type.Array(n1, t1) -> (
        inferType expr2 >>= function
        | Type.Array(n2, t2) -> if n1=n2 then Ok (Type.Array(n1, Type.NProd([t1;t2]))) 
                                else Error "in Zip the two arrays should have the same length" 
        | _ -> Error "Argument 2 of Zip should be a Type.Array")
    | _ -> Error "Argument 1 of Zip should be a Type.Array")
  | Zip3 (expr1, expr2, expr3) -> (
    inferType expr1 >>= function
    | Type.Array(n1, t1) -> (
        inferType expr2 >>= function
        | Type.Array(n2, t2) ->  (inferType expr3 >>= function
              | Type.Array(n3, t3) -> if (n1=n2 && n1=n3) then Ok (Type.Array (n1, Type.NProd ([t1; t2; t3])))
                                      else Error "in Zip3 the three arrays should have the same length" 
              | _ -> Error "Argument 3 of Zip3 should be a Type.Array")
        | _ -> Error "Argument 2 of Zip3 should be a Type.Array")
    | _ -> Error "Argument 1 of Zip3 should be a Type.Array")
  | Unzip (expr) -> (
    inferType expr >>= function
    | Type.Array(m, Type.NProd([t1; t2])) -> Ok (Type.NProd ([Type.Array (m, t1); Type.Array (m ,t2)]))
    | _ -> Error "Argument of Unzip should be an array of pairs")
  | Unzip3 (expr) -> (
    inferType expr >>= function
    | Type.Array(m, Type.NProd([t1; t2; t3])) -> Ok (Type.NProd ([Type.Array (m, t1); Type.Array (m ,t2); Type.Array (m ,t3)]))
    | _ -> Error "Argument of Unzip3 should be an array of triples")
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

(* interpreter *)

(* checks whether the context captures all the free variables of an expression*)
(* let contextComplete expr context =
  let exprFv = freeVar expr in 
  VarSet.for_all (fun x -> (List.exists (fun ((y,_),_) -> Var.equal y x) context)) exprFv *)

let interpretOp1 op expr = match expr with
| Const v -> Const (interpretOp1 op v)
| expr -> Apply1 (op, expr)

let interpretOp2 op expr1 expr2 = match expr1, expr2 with
| (Const v1,Const v2) -> Const (interpretOp2 op v1 v2)
| expr1, expr2 -> Apply2(op, expr1, expr2)

module M = CCMap.Make(struct
    type t = Var.t * Type.t
    let compare = CCPair.compare (CCPair.compare CCString.compare CCInt.compare) compare
  end)

let interpret expr context =
  if not (isWellTyped expr) then failwith "interpret: ill typed term";
  let rec interp context expr =
    match expr with
    | Var (v, t) -> begin
        match M.get (v, t) context with
        | Some expr -> interp context expr
        | None -> expr
      end
    | Const _ -> expr
    | Fun (vars, expr) -> Fun (vars, interp context expr)
    | Apply1 (op, expr) ->
        let v = interp context expr in
        interpretOp1 op v
    | Apply2 (op, expr1, expr2) ->
        let val1 = interp context expr1 in
        let val2 = interp context expr2 in
        interpretOp2 op val1 val2
    | Let (x, ty, expr1, expr2) ->
        let v = interp context expr1 in
        interp (M.add (x, ty) v context) expr2
    | App (expr1, exprList) -> (
        let vList = List.map (interp context) exprList in
        match interp context expr1 with
        | Fun (varList, expr1) ->
            assert (List.compare_lengths varList vList = 0);
            interp (M.add_list context (List.combine varList vList)) expr1
        | expr -> App (expr, vList))
    | Tuple exprList -> Tuple (List.map (interp context) exprList)
    | NCase (expr1, varList, expr2) -> (
        match interp context expr1 with
        | Tuple exprList ->
          assert (List.compare_lengths varList exprList = 0);
          interp (M.add_list context (List.combine varList exprList)) expr2
        | expr -> NCase (expr, varList, interp context expr2))
    | Map (x, ty, expr1, expr2) -> (
        let expr1 = interp context expr1 in
        match interp context expr2 with
        | Array exprList ->
            Array (List.map (fun e -> interp (M.add (x, ty) e context) expr1) exprList)
        | expr2 -> Map (x, ty, expr1, expr2))
    | Map2 (x, t1, y, t2, expr1, expr2, expr3) -> (
        let expr1 = interp context expr1 in
        match (interp context expr2, interp context expr3) with
        | Array exprList1, Array exprList2 ->
            Array
              (List.map2
                 (fun e1 e2 -> interp (M.add (y, t2) e2 (M.add (x, t1) e1 context)) expr1)
                 exprList1 exprList2)
        | expr2, expr3 -> Map2 (x, t1, y, t2, expr1, expr2, expr3))
    | Fold (x, t1, y, t2, expr1, expr2, expr3)
    | Reduce (x, t1, y, t2, expr1, expr2, expr3) -> (
        let expr1 = interp context expr1 in
        let expr2 = interp context expr2 in
        match interp context expr3 with
        | Array exprList ->
            List.fold_left
              (fun acc e -> interp (M.add (y, t2) e (M.add (x, t1) acc context)) expr1)
              expr2 exprList
        | expr3 -> Reduce (x, t1, y, t2, expr1, expr2, expr3))
    | Scan (x, t1, y, t2, expr1, expr2, expr3) -> (
        let expr1 = interp context expr1 in
        let expr2 = interp context expr2 in
        match interp context expr3 with
        | Array exprList ->
            List.fold_left
              (fun (acc, l) e ->
                let tmp = interp (M.add (y, t2) e (M.add (x, t1) acc context)) expr1 in
                (tmp, tmp :: l))
              (expr2, []) exprList
            |> fun (_, l) -> Array (List.rev l)
        | expr3 -> Scan (x, t1, y, t2, expr1, expr2, expr3))
    | Zip (expr1, expr2) -> (
        match (interp context expr1, interp context expr2) with
        | Array exprList1, Array exprList2 ->
            Array (List.map2 (fun x y -> Tuple [ x; y ]) exprList1 exprList2)
        | expr1, expr2 -> Zip (expr1, expr2))
    | Zip3 (expr1, expr2, expr3) -> (
        match (interp context expr1, interp context expr2, interp context expr3) with
        | Array exprList1, Array exprList2, Array exprList3 ->
            Array
              (List.map2
                 (fun (x, y) z -> Tuple [ x; y; z ])
                 (List.combine exprList1 exprList2)
                 exprList3)
        | expr1, expr2, expr3 -> Zip3 (expr1, expr2, expr3))
    | Unzip exprList -> (
        match interp context exprList with
        | Array exprList ->
            if
              List.for_all
                (fun e -> match e with Tuple [ _; _ ] -> true | _ -> false)
                exprList
            then
              let exprList1, exprList2 =
                List.split
                  (List.map
                     (fun e ->
                       match e with
                       | Tuple [ e1; e2 ] -> (e1, e2)
                       | _ -> assert false)
                     exprList)
              in
              Tuple [ Array exprList1; Array exprList2 ]
            else Unzip (Array exprList)
        | exprList -> Unzip exprList)
    | Unzip3 exprList -> (
        match interp context exprList with
        | Array exprList ->
            if
              List.for_all
                (fun e -> match e with Tuple [ _; _; _ ] -> true | _ -> false)
                exprList
            then
              let exprList1, exprList2, exprList3 =
                List.fold_left
                  (fun (l1, l2, l3) (e1, e2, e3) ->
                    (e1 :: l1, e2 :: l2, e3 :: l3))
                  ([], [], [])
                  ((List.rev_map
                        (fun e ->
                          match e with
                          | Tuple [ e1; e2; e3 ] -> (e1, e2, e3)
                          | _ -> failwith "")
                        exprList))
              in
              Tuple [ Array exprList1; Array exprList2; Array exprList3 ]
            else Unzip3 (Array exprList)
        | exprList -> Unzip3 exprList)
    | Get (n, expr) -> (
        match interp context expr with
        | Array exprList -> List.nth exprList n
        | expr -> Get (n, expr))
    | Array exprList -> Array (List.map (interp context) exprList)
  in
  interp (M.of_list context) expr

(** {2 Traverse} *)
module Traverse (S : Strategy.S) = struct
  open S

  let rec map f expr =
    return expr >>= fun expr ->
    f expr >>= function
    | (Var (_, _) | Const _) as expr -> return expr
    | Apply1 (op, expr) -> map f expr >|= fun expr -> Apply1 (op, expr)
    | Apply2 (op, expr1, expr2) ->
        apply2 (map f) expr1 expr2 >|= fun (expr1, expr2) ->
        Apply2 (op, expr1, expr2)
    | Let (y, ty, expr1, expr2) ->
        apply2 (map f) expr1 expr2 >|= fun (expr1, expr2) ->
        Let (y, ty, expr1, expr2)
    | Fun (l, expr) -> map f expr >|= fun expr -> Fun (l, expr)
    | App (expr1, l) -> (
        applyl (map f) (expr1 :: l) >|= function
        | expr1 :: l -> App (expr1, l)
        | [] -> assert false)
    | Tuple l -> applyl (map f) l >|= fun l -> Tuple l
    | NCase (expr1, varList, expr2) ->
        apply2 (map f) expr1 expr2 >|= fun (expr1, expr2) ->
        NCase (expr1, varList, expr2)
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
    | Zip (expr1, expr2) ->  
      apply2 (map f) expr1 expr2 >|= fun (expr1, expr2) ->
      Zip (expr1, expr2)
    | Zip3 (expr1, expr2, expr3) ->  
      applyl (map f) [expr1; expr2; expr3] >|= fun l -> begin match l with 
        | [e1; e2; e3] -> Zip3(e1, e2, e3)
        | _ -> assert false
        end
    | Unzip (expr) ->  map f expr >|= fun expr -> Unzip (expr)
    | Unzip3 (expr) ->  map f expr >|= fun expr -> Unzip3 (expr)
    | Get (n, expr) -> map f expr >|= fun expr -> Get(n, expr)
    | Fold (x, t1, y, t2, expr1, expr2, expr3) -> 
     applyl (map f) [expr1; expr2; expr3] >|= fun l -> begin match l with 
        | [e1; e2; e3] -> Fold(x, t1, y, t2, e1, e2, e3)
        | _ -> assert false
        end
    | Array (exprList) -> applyl (map f) exprList >|= fun l -> Array l
end

(** {2 Parser} *)
module Parse = struct
  open CCParse

  let mk_var (x, t) = Var (x, t)

  let mk_const f = Const f

  let mk_apply1 (o, t) = Apply1 (o, t)

  let mk_plus (t1, t2) = Apply2 (Operators.Plus, t1, t2)

  let mk_minus (t1, t2) = Apply2 (Operators.Minus, t1, t2)

  let mk_times (t1, t2) = Apply2 (Operators.Times, t1, t2)

  let float =
    map2
      (fun c s -> String.make 1 c ^ s)
      (char_if (fun c -> is_num c || Char.equal c '-'))
      (chars_if (fun c ->
           is_num c || Char.equal c '-' || Char.equal c '.' || Char.equal c 'e'))
    >>= fun s ->
    try return (float_of_string s) with Failure _ -> fail "expected an float"

  let pVarType =
    skip_white
    *> U.pair ~start:"" ~stop:"" ~sep:":"
         (U.pair ~start:"" ~stop:"" ~sep:"" (chars_if is_alpha) U.int)
         Type.Parse.pType

  let pApply1 self =
    Operators.Parse.pOp1 >>= fun op ->
    skip_white *> string "(" *> self <* skip_white <* string ")" >|= fun expr ->
    Apply1 (op, expr)

  let pLet self =
    skip_white *> string "let" *> skip_white *> pVarType >>= fun (v, t) ->
    skip_white *> string "=" *> skip_white *> self >>= fun expr1 ->
    skip_white *> string "in" *> skip_white *> self >|= fun expr2 ->
    Let (v, t, expr1, expr2)

  let pFun self =
    skip_white *> string "λ" *> skip_white *> U.list ~start:"" ~stop:"" ~sep:"," pVarType >>= fun vars ->
    skip_white *> string "." *> skip_white *> self >|= fun expr -> Fun (vars, expr)

  let pApp self =
    skip_white *> string "(" *> skip_white *> self <* skip_white <* string ")" >>= fun expr ->
    skip_white *> U.list ~sep:"," self >|= fun exprs -> App (expr, exprs)

  let pTuple self = U.list ~start:"{" ~stop:"}" ~sep:"," self >|= fun l -> Tuple l

  let pNCase self =
    skip_white *> string "lets" *> skip_white *> U.list ~start:"" ~stop:"" ~sep:"," pVarType >>= fun vars ->
    skip_white *> string "=" *> skip_white *> self >>= fun expr1 ->
    skip_white *> string "in" *> skip_white *> self >|= fun expr2 ->
    NCase (expr1, vars, expr2)

  let pMap self =
    skip_white *> string "map" *> skip_white
    *> U.pair ~start:"(" ~stop:")" ~sep:"." pVarType self
    >>= fun ((x, t), expr1) ->
    skip_white *> string "(" *> skip_white *> self <* skip_white <* string ")"
    >|= fun expr2 -> Map (x, t, expr1, expr2)

  let pMap2 self =
    skip_white *> string "map2" *> skip_white
    *> U.pair ~sep:"."
         (U.pair ~start:"" ~stop:"" ~sep:"," pVarType pVarType)
         self
    >>= fun (((x, t1), (y, t2)), expr1) ->
    skip_white *> string "(" *> skip_white *> self <* skip_white <* string ")"
    >>= fun expr2 ->
    skip_white *> string "(" *> skip_white *> self <* skip_white <* string ")"
    >|= fun expr3 -> Map2 (x, t1, y, t2, expr1, expr2, expr3)

  let pReduce self =
    skip_white *> string "reduce" *> skip_white
    *> U.pair ~sep:"."
         (U.pair ~start:"" ~stop:"" ~sep:"," pVarType pVarType)
         self
    >>= fun (((x, t1), (y, t2)), expr1) ->
    skip_white *> string "(" *> skip_white *> self <* skip_white <* string ")"
    >>= fun expr2 ->
    skip_white *> string "(" *> skip_white *> self <* skip_white <* string ")"
    >|= fun expr3 -> Reduce (x, t1, y, t2, expr1, expr2, expr3)

  let pScan self =
    skip_white *> string "scan" *> skip_white
    *> U.pair ~sep:"."
         (U.pair ~start:"" ~stop:"" ~sep:"," pVarType pVarType)
         self
    >>= fun (((x, t1), (y, t2)), expr1) ->
    skip_white *> string "(" *> skip_white *> self <* skip_white <* string ")"
    >>= fun expr2 ->
    skip_white *> string "(" *> skip_white *> self <* skip_white <* string ")"
    >|= fun expr3 -> Scan (x, t1, y, t2, expr1, expr2, expr3)

  let pFold self =
    skip_white *> string "fold" *> skip_white
    *> U.pair ~sep:"."
         (U.pair ~start:"" ~stop:"" ~sep:"," pVarType pVarType)
         self
    >>= fun (((x, t1), (y, t2)), expr1) ->
    skip_white *> string "(" *> skip_white *> self <* skip_white <* string ")"
    >>= fun expr2 ->
    skip_white *> string "(" *> skip_white *> self <* skip_white <* string ")"
    >|= fun expr3 -> Fold (x, t1, y, t2, expr1, expr2, expr3)

  let pGet self =
    skip_white *> string "get" *> skip_white *> U.int >>= fun n ->
    skip_white *> string "(" *> skip_white *> self <* skip_white <* string ")"
    >|= fun expr -> Get (n, expr)

  let pArray self = U.list ~sep:"," self >|= fun l -> Array l

  let pTerm =
    fix @@ fun self ->
    skip_white
    *> (try_ (pure mk_const <*> float)
       <|> try_ (pure mk_var <*> pVarType)
       <|> try_ (pApply1 self)
       <|> try_ (pure mk_plus <*> U.pair ~start:"(" ~sep:"+" ~stop:")" self self)
       <|> try_
             (pure mk_minus <*> U.pair ~start:"(" ~sep:"-" ~stop:")" self self)
       <|> try_
             (pure mk_times <*> U.pair ~start:"(" ~sep:"*" ~stop:")" self self)
       <|> try_ (pLet self)
       <|> try_ (pFun self)
       <|> try_ (pApp self)
       <|> try_ (pTuple self)
       <|> try_ (pNCase self)
       <|> try_ (pMap self)
       <|> try_ (pMap2 self)
       <|> try_ (pReduce self)
       <|> try_ (pScan self)
       <|> try_ (pFold self)
       <|> try_ (pGet self)
       <|> pArray self)

  let of_string = parse_string pTerm
end

(* Derivatives of basic operators *)

(* Unary operators *)

(** First order derivative of unary operator: ∂op/∂x *)
let dop op y = match op with
| Cos     -> Apply1(Minus, Apply1(Sin, y))
| Sin     -> Apply1(Cos, y)
| Exp     -> Apply1(Exp, y)
| Minus   -> Const (-1.)
| Power 0 -> Const(0.)
| Power n -> Apply2(Times, Const(float_of_int (n-1)), Apply1(Power(n-1), y))
| Acos     -> Apply2(Div, Const (-1.), Apply1(Sqrt, Apply2(Minus, Const 1., Apply1(Power(2), y))))
| Asin     -> Apply2(Div, Const 1., Apply1(Sqrt, Apply2(Minus, Const 1., Apply1(Power(2), y))))
| Tan      -> Apply2(Div, Const 1., Apply1(Power(2), Apply1(Cos, y)))
| Atan     -> Apply2(Div, Const 1., Apply2(Plus, Const 1., Apply1(Power(2), y)))
| Cosh     -> Apply1(Sinh, y)
| Sinh     -> Apply1(Cosh, y)
| Tanh     -> Apply2(Div, Const 1., Apply1(Power(2), Apply1(Cosh, y)))
| Log      -> Apply2(Div, Const 1., y)
| Log10    -> Apply2(Div, Const 1., Apply2(Times, Apply1(Log, (Const 10.)), y))
| Sqrt     -> Apply2(Div, Const (-1.), Apply1(Sqrt, y))
(*
| Log2     -> Apply2(Div, Const 1., Apply2(Times, Apply1(Log, (Const 2.)), y))
| Atanh    -> Apply2(Div, Const 1., Apply2(Minus, Const 1., Apply1(Power(2), y)))
| Asinh    -> Apply2(Div, Const 1., Apply1(Sqrt, Apply2(Plus, Apply1(Power(2), y), Const 1.))
| Acosh    -> Apply2(Div, Const 1., Apply1(Sqrt, Apply2(Minus, Apply1(Power(2), y), Const 1.))
*)

(* ∂^2 op/∂x∂x *)                          
let ddop (op: op1) y = match op with
  | Cos     -> Apply1(Minus, Apply1(Sin, y))
  | Sin     -> Apply1(Cos, y)
  | Exp     -> Apply1(Exp, y)
  | Minus   -> Const (-1.)
  | Power 0 -> Const(0.)
  | Power n -> Apply2(Times, Const(float_of_int (n-1)), Apply1(Power(n-1), y))
  | Acos    -> Apply2(Div, Apply1(Minus, y), Apply1(Power(3), Apply1(Sqrt, Apply2(Minus, Const 1., Apply1(Power(2), y)))))
  | Asin    -> Apply2(Div, y, Apply1(Power(3), Apply1(Sqrt, Apply2(Minus, Const 1., Apply1(Power(2), y)))))
  | Tan     -> Apply2(Div, Apply2(Times, Const 2., Apply1(Tan, y)), Apply1(Power(2), Apply1(Cos, y)))
  | Atan    -> Apply2(Div, Apply2(Times, Const (-2.), y), Apply1(Power(2), Apply2(Plus, Const 1., Apply1(Power(2), y))))
  | Cosh    -> Apply1(Cosh, y)
  | Sinh    -> Apply1(Sinh, y)
  | Tanh    -> Apply2(Div, Apply2(Times, Const (-2.), Apply1(Tanh, y)), Apply1(Power(2), Apply1(Cosh, y)))
  | Log     -> Apply2(Div, Const (-1.), Apply1(Power(2), y))
  | Log10   -> Apply2(Div, Const (-1.), Apply2(Times, Apply1(Log, (Const 10.)), Apply1(Power(2), y)))
  | Sqrt    -> Apply2(Div, Const (2.5e-1), Apply1(Power(3), Apply1(Sqrt, y)))
  (*
  | Log2   -> Apply2(Div, Const (-1.), Apply2(Times, Apply1(Log, (Const 2.)), Apply1(Power(2), y)))
  | Atanh  -> Apply2(Div, Apply2(Times, Const 2., y), Apply1(Power(2), Apply2(Minus, Const 1., Apply1(Power(2), y))))
  | Asinh  -> Apply2(Div, Apply1(Minus, y), Apply1(Power(3), Apply1(Sqrt, Apply2(Plus, Const 1., Apply1(Power(2), y)))))
  | Acosh  -> Apply2(Div, Apply1(Minus, y), Apply1(Power(3), Apply1(Sqrt, Apply2(Minus, Apply1(Power(2), y), Const 1.))))
  *)

(** Second order derivative of binary operator *)
let dop22 (op: op1) x d1x d2x ddx  = Apply2(Plus, Apply2(Times, ddop op x, Apply2(Times, d1x, d2x)), Apply2(Times, dop op x, ddx))

(* Binary operators *)

(** First partial first order derivative of binary operator: ∂op/∂x1*)
let d1op op _ y2 = match op with
  | Plus  -> Const(1.)
  | Times -> y2
  | Minus -> Const(1.)
  | Div   -> Apply2(Div, Const 1., y2)

(** Second partial first order derivative of binary operator: ∂op/∂x2 *)
let d2op op y1 y2 = match op with
  | Plus  -> Const(1.)
  | Times -> y1
  | Minus -> Const(-1.) 
  | Div   -> Apply2(Div, Apply1(Minus, y1), Apply1(Power(2), y2))

(* ∂^2 op/∂x1∂x1 *)
let d1d1op (op: op2) _ _ = match op with
  | Plus  -> Const 0.
  | Minus -> Const 0.
  | Times -> Const 0.
  | Div   -> Const 0.
 
 (* ∂^2 op/∂x1∂x2 *)
let d1d2op (op: op2) _ y2 = match op with
  | Plus  -> Const 0.
  | Minus -> Const 0.
  | Times -> Const 1.
  | Div   -> Apply2(Div, Const (-1.), Apply1(Power(2), y2))
 
 (* ∂^2 op/∂x2∂x1 *) 
let d2d1op (op: op2) _ y2 = match op with
  | Plus  -> Const 0.
  | Minus -> Const 0.
  | Times -> Const 1. 
  | Div   -> Apply2(Div, Const (-1.), Apply1(Power(2), y2))

 (* ∂^2 op/∂x2∂x2 *)
let d2d2op (op: op2) y1 y2 = match op with
  | Plus  -> Const 0.
  | Minus -> Const 0.
  | Times -> Const 0.
  | Div   -> Apply2(Div, Apply2(Times, Const 2., y1), Apply1(Power(3), y2)) 

(** Second order derivative of binary operator *)
let d2op22 (op: op2) x d1x d2x ddx y d1y d2y ddy  = match op with
  | Plus  -> Apply2(Plus, ddx, ddy)
  | Minus -> Apply2(Minus, ddx, ddy)
  | Times -> Apply2(Plus,
                    Apply2(Plus, Apply2(Times, ddx, y), Apply2(Times, x, ddy)), Apply2(Plus, Apply2(Times, d1x, d2y), Apply2(Times, d1y, d2y)))
  | Div   -> Apply2(Plus,
                    Apply2(Plus, Apply2(Times, d1op Div x y , ddx), Apply2(Times, d2op Div x y, ddy)),
                    Apply2(Plus,
                            Apply2(Plus, Apply2(Times, d1d1op Div x y, Apply2(Times, d1x, d2x)), Apply2(Times, d1d2op Div x y, Apply2(Times, d1x, d2y))),
                            Apply2(Plus, Apply2(Times, d2d1op Div x y, Apply2(Times, d1y, d2x)), Apply2(Times, d2d2op Div x y, Apply2(Times, d1y, d2y)))))
