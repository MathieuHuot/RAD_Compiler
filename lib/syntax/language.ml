module Op = Operators

module VarSet = CCSet.Make (struct
  type t = Var.t

  let compare x y = CCPair.compare CCString.compare CCInt.compare x y
end)

(* syntax *)
type 'a tuple = 'a list

type source = private Source

type target = private Target

module Type = struct
  type 'a t =
    | Real : 'a t
    | Prod : 'a t tuple -> 'a t
    | Arrow : target t tuple * target t -> target t
    | Array : int * 'a t -> 'a t

  let rec pp : type a. Format.formatter -> a t -> unit =
   fun fmt t ->
    match t with
    | Real -> Format.fprintf fmt "real"
    | Arrow (l, t) -> (
        match l with
        | [] -> Format.fprintf fmt "()@ ->@ (%a)" pp t
        | l ->
            Format.fprintf fmt "%a@ ->@ (%a)"
              (CCList.pp
                 ~pp_sep:(fun fmt () -> Format.fprintf fmt "@ ->@ ")
                 (fun fmt -> Format.fprintf fmt "(%a)" pp))
              l pp t)
    | Prod l ->
        Format.fprintf fmt "(%a)"
          (CCList.pp ~pp_sep:(fun fmt () -> Format.fprintf fmt "@ *@ ") pp)
          l
    | Array (n, t) ->
        Format.fprintf fmt "Array[%a][%a]" Format.pp_print_int n pp t

  let to_string : type a. a t -> string = fun t -> CCFormat.to_string pp t

  let isArrow ty = match ty with Arrow _ -> true | _ -> false

  let rec sourceToTarget : source t -> target t = function
    | Real -> Real
    | Prod l -> Prod (List.map sourceToTarget l)
    | Array (n, ty) -> Array (n, sourceToTarget ty)

  let rec equal : type a. a t -> a t -> _ =
   fun t1 t2 ->
    match (t1, t2) with
    | Real, Real -> true
    | Arrow (tyList1, ret_type1), Arrow (tyList2, ret_type2) ->
        CCList.equal equal tyList1 tyList2 && equal ret_type1 ret_type2
    | Prod tyList1, Prod tyList2 -> CCList.equal equal tyList1 tyList2
    | Array (n, t1), Array (m, t2) -> equal t1 t2 && n = m
    | _ -> false

  let rec isGroundType = function
    | Real -> true
    | Prod tyList -> List.for_all isGroundType tyList
    | Array (_, ty) -> isGroundType ty
    | _ -> false

  module Parse = struct
    open CCParse

    let pReal =
      map
        (function "real" -> Real | _ -> assert false)
        (skip_white *> string "real")

    let pProd self =
      U.list ~start:"(" ~stop:")" ~sep:"*" self >|= fun l -> Prod l

    let pArray self =
      skip_white *> string "Array[" *> skip_white *> U.int >>= fun n ->
      skip_white *> string "][" *> skip_white *> self >>= fun t ->
      string "]" >|= fun _ -> Array (n, t)

    let pArrow self =
      skip_white
      *> (try_
            ( string "()" *> skip_white *> string "->" *> skip_white
              *> string "(" *> skip_white *> self
            <* skip_white <* string ")"
            >|= fun expr -> Arrow ([], expr) )
         <|> ( U.list ~start:"" ~stop:"" ~sep:"->"
                 (string "(" *> skip_white *> self <* skip_white <* string ")")
             >>= fun l ->
               match List.rev l with
               | [] | [ _ ] -> fail "Arrow: empty list"
               | h :: t -> return (Arrow (List.rev t, h)) ))

    let pType =
      fix @@ fun self ->
      try_ (pArrow self) <|> try_ pReal <|> try_ (pProd self) <|> pArray self

    let of_string = parse_string pType
  end
end

type 'a ast =
  | Var : Var.t * 'a Type.t -> 'a ast
  | Const : float -> 'a ast
  | Apply1 : Op.op1 * 'a ast -> 'a ast
  | Apply2 : Op.op2 * 'a ast * 'a ast -> 'a ast
  | Let : Var.t * 'a Type.t * 'a ast * 'a ast -> 'a ast
  | Fun : (Var.t * target Type.t) list * target ast -> target ast
  | App : target ast * target ast list -> target ast
  | Tuple : target ast tuple -> target ast
  | NCase : target ast * (Var.t * target Type.t) list * target ast -> target ast
  | Map : Var.t * 'a Type.t * 'a ast * 'a ast -> 'a ast
      (** map x ty e1 [a1,...,an] = [e1[a1/x],...,e1[an/x]] *)
  | Map2 :
      Var.t
      * target Type.t
      * Var.t
      * target Type.t
      * target ast
      * target ast
      * target ast
      -> target ast
      (** map2 x ty1 y ty2 e1 [a1,...,an] [b1,...,bn] = [e1[a1/x,b1/y],...,e1[an/x,bn/y]] *)
  | Map3 :
      Var.t
      * target Type.t
      * Var.t
      * target Type.t
      * Var.t
      * target Type.t
      * target ast
      * target ast
      * target ast
      * target ast
      -> target ast
      (** map3 x1 ty1 x2 ty2 x3 ty3 e [a1,...,an] [b1,...,bn] [c1,...,cn] = [e[a1/x1,b1/x2,c1/x3],...,e[an/x1,bn/x2,cn/x3]] *)
  | Reduce :
      Var.t * 'a Type.t * Var.t * 'a Type.t * 'a ast * 'a ast * 'a ast
      -> 'a ast  (** reduce x y e1 z A means reduce (x,y -> e1) from z on A *)
  | Scan :
      Var.t * 'a Type.t * Var.t * 'a Type.t * 'a ast * 'a ast * 'a ast
      -> 'a ast  (** scan x ty1 y ty2 e1 z A *)
  | Zip : target ast * target ast -> target ast
      (** zip [a1,...,an] [b1,...,bn] = [(a1,b1),...,(an,bn)] *)
  | Unzip : target ast -> target ast
      (** Unzip [(a1,b1),...,(an,bn)] = [a1,...,an],[b1,...,bn] =  *)
  | Zip3 : target ast * target ast * target ast -> target ast
      (** zip [a1,...,an] [b1,...,bn] [c1,...,cn] = [(a1,b1,c1),...,(an,bn,cn)] *)
  | Unzip3 : target ast -> target ast
      (** Unzip  [(a1,b1,c1),...,(an,bn,cn)] = [a1,...,an],[b1,...,bn], [c1,...,cn] =  *)
  | Fold :
      Var.t * 'a Type.t * Var.t * 'a Type.t * 'a ast * 'a ast * 'a ast
      -> 'a ast
      (** fold z x ty1 y ty2 e z A means fold A from z with (x:ty1, y:ty2 -> e). It's a fold LEFT operator. *)
  | Array : 'a ast list -> 'a ast

let var v t = Var (v, t)

let const f = Const f

let apply1 op expr = Apply1 (op, expr)

let apply2 op expr1 expr2 = Apply2 (op, expr1, expr2)

let clet v t expr1 expr2 = Let (v, t, expr1, expr2)

let cfun l expr = Fun (l, expr)

let app expr1 expr2 = App (expr1, expr2)

let tuple l = Tuple l

let ncase expr1 l expr2 = NCase (expr1, l, expr2)

let cmap v t expr1 expr2 = Map (v, t, expr1, expr2)

let cmap2 v1 t1 v2 t2 expr1 expr2 expr3 =
  Map2 (v1, t1, v2, t2, expr1, expr2, expr3)

let cmap3 v1 t1 v2 t2 v3 t3 expr1 expr2 expr3 expr4 =
  Map3 (v1, t1, v2, t2, v3, t3, expr1, expr2, expr3, expr4)

let reduce v1 t1 v2 t2 expr1 expr2 expr3 =
  Reduce (v1, t1, v2, t2, expr1, expr2, expr3)

let scan v1 t1 v2 t2 expr1 expr2 expr3 =
  Scan (v1, t1, v2, t2, expr1, expr2, expr3)

let zip expr1 expr2 = Zip (expr1, expr2)

let unzip expr = Unzip expr

let zip3 expr1 expr2 expr3 = Zip3 (expr1, expr2, expr3)

let unzip3 expr = Unzip3 expr

let cfold v1 t1 v2 t2 expr1 expr2 expr3 =
  Fold (v1, t1, v2, t2, expr1, expr2, expr3)

let array l = Array l

type 'a context = (Var.t * 'a Type.t, 'a ast) CCList.Assoc.t

let varToSyn varList = List.map (fun (x, ty) -> Var (x, ty)) varList

let rec sourceToTarget : source ast -> target ast = function
  | Const c -> Const c
  | Var (x, tx) -> Var (x, Type.sourceToTarget tx)
  | Apply1 (op, expr) -> Apply1 (op, sourceToTarget expr)
  | Apply2 (op, expr1, expr2) ->
      Apply2 (op, sourceToTarget expr1, sourceToTarget expr2)
  | Let (x, tx, expr1, expr2) ->
      Let (x, Type.sourceToTarget tx, sourceToTarget expr1, sourceToTarget expr2)
  | Map (x, tx, expr1, expr2) ->
      Map (x, Type.sourceToTarget tx, sourceToTarget expr1, sourceToTarget expr2)
  | Reduce (x, tx, y, ty, expr1, expr2, expr3) ->
      Reduce
        ( x,
          Type.sourceToTarget tx,
          y,
          Type.sourceToTarget ty,
          sourceToTarget expr1,
          sourceToTarget expr2,
          sourceToTarget expr3 )
  | Scan (x, tx, y, ty, expr1, expr2, expr3) ->
      Scan
        ( x,
          Type.sourceToTarget tx,
          y,
          Type.sourceToTarget ty,
          sourceToTarget expr1,
          sourceToTarget expr2,
          sourceToTarget expr3 )
  | Fold (x, tx, y, ty, expr1, expr2, expr3) ->
      Fold
        ( x,
          Type.sourceToTarget tx,
          y,
          Type.sourceToTarget ty,
          sourceToTarget expr1,
          sourceToTarget expr2,
          sourceToTarget expr3 )
  | Array exprList -> Array (List.map sourceToTarget exprList)

let rec pp : type a. Format.formatter -> a ast -> unit =
 fun fmt expr ->
  match expr with
  | Var (a, t) -> Format.fprintf fmt "%a:%a" Var.pp a Type.pp t
  | Const c -> Format.fprintf fmt "%.18g" c
  | Apply1 (op, expr) ->
      Format.fprintf fmt "@[%a(@;<0 2>%a@,)@]" Op.pp_op1 op pp expr
  | Apply2 (op, expr1, expr2) ->
      if Op.is_infix op then
        Format.fprintf fmt "@[(%a@ %a %a)@]" pp expr1 Op.pp_op2 op pp expr2
      else Format.fprintf fmt "@[(%a %a %a)@]" pp expr1 Op.pp_op2 op pp expr2
  | Let (x, t, expr1, expr2) ->
      Format.fprintf fmt "@[<hv>let %a:%a =@;<1 2>@[%a@]@ in@ %a@]" Var.pp x
        Type.pp t pp expr1 pp expr2
  | Fun (vars, expr) ->
      Format.fprintf fmt "@[λ%a.@;<1 2>%a@]"
        (CCList.pp (fun fmt (v, t) ->
             Format.fprintf fmt "%a:%a" Var.pp v Type.pp t))
        vars pp expr
  | App (expr, exprs) ->
      Format.fprintf fmt "@[(%a)[@;<0 2>@[%a@]]@]" pp expr (CCList.pp pp) exprs
  | Tuple exprs ->
      CCList.pp
        ~pp_start:(fun fmt () -> Format.fprintf fmt "@[{@;<0 2>@[")
        ~pp_stop:(fun fmt () -> Format.fprintf fmt "@]@,}@]")
        pp fmt exprs
  | NCase (expr1, vars, expr2) ->
      Format.fprintf fmt "@[<hv>lets %a =@;<1 2>@[%a@]@ in@ %a@]"
        (CCList.pp
           ~pp_sep:(fun fmt () -> Format.pp_print_string fmt ",")
           (fun fmt (v, t) -> Format.fprintf fmt "%a:%a" Var.pp v Type.pp t))
        vars pp expr1 pp expr2
  | Map (x, t, expr1, expr2) ->
      Format.fprintf fmt "@[map@;<1 2>(%a:%a.%a)@ (%a)@]" Var.pp x Type.pp t pp
        expr1 pp expr2
  | Map2 (x, t1, y, t2, expr1, expr2, expr3) ->
      Format.fprintf fmt "@[map2@;<1 2>(%a:%a,%a:%a.%a)@ (%a)@ (%a)@]" Var.pp x
        Type.pp t1 Var.pp y Type.pp t2 pp expr1 pp expr2 pp expr3
  | Map3 (x, t1, y, t2, z, t3, expr1, expr2, expr3, expr4) ->
      Format.fprintf fmt
        "@[map2@;<1 2>(%a:%a,%a:%a,%a:%a.%a)@ (%a)@ (%a)@ (%a)@]" Var.pp x
        Type.pp t1 Var.pp y Type.pp t2 Var.pp z Type.pp t3 pp expr1 pp expr2 pp
        expr3 pp expr4
  | Reduce (x, t1, y, t2, expr1, expr2, expr3) ->
      Format.fprintf fmt "@[reduce@;<1 2>(%a:%a,%a:%a.%a)@ (%a)@ (%a)@]" Var.pp
        x Type.pp t1 Var.pp y Type.pp t2 pp expr1 pp expr2 pp expr3
  | Scan (x, t1, y, t2, expr1, expr2, expr3) ->
      Format.fprintf fmt "@[scan@;<1 2>(%a:%a,%a:%a.%a)@ (%a)@ (%a)@]" Var.pp x
        Type.pp t1 Var.pp y Type.pp t2 pp expr1 pp expr2 pp expr3
  | Zip (expr1, expr2) ->
      Format.fprintf fmt "@[zip@;<1 2>(%a) (%a)@]" pp expr1 pp expr2
  | Zip3 (expr1, expr2, expr3) ->
      Format.fprintf fmt "@[zip3@;<1 2>(%a) (%a) (%a)@]" pp expr1 pp expr2 pp
        expr3
  | Unzip expr -> Format.fprintf fmt "@[unzip@;<1 2>(%a)@]" pp expr
  | Unzip3 expr -> Format.fprintf fmt "@[unzip3@;<1 2>(%a)@]" pp expr
  | Fold (x, t1, y, t2, expr1, expr2, expr3) ->
      Format.fprintf fmt "@[fold(%a:%a,%a:%a.%a)@ (%a)@ (%a)@]" Var.pp x Type.pp
        t1 Var.pp y Type.pp t2 pp expr1 pp expr2 pp expr3
  | Array exprList ->
      CCList.pp
        ~pp_sep:(fun fmt () -> Format.pp_print_string fmt ",")
        ~pp_start:(fun fmt () -> Format.fprintf fmt "@[[@;<0 2>@[")
        ~pp_stop:(fun fmt () -> Format.fprintf fmt "@]@,]@]")
        pp fmt exprList

let to_string : type a. a ast -> string = fun expr -> CCFormat.to_string pp expr

let rec map : type a. (a ast -> a ast) -> a ast -> a ast =
 fun f expr ->
  f
    (match expr with
    | (Var (_, _) | Const _) as expr -> expr
    | Apply1 (op, expr) -> Apply1 (op, map f expr)
    | Apply2 (op, expr1, expr2) -> Apply2 (op, map f expr1, map f expr2)
    | Let (y, ty, expr1, expr2) -> Let (y, ty, map f expr1, map f expr2)
    | Fun (l, expr) -> Fun (l, map f expr)
    | App (expr1, l) -> App (map f expr1, List.map (map f) l)
    | Tuple l -> Tuple (List.map (map f) l)
    | NCase (expr1, lType, expr2) -> NCase (map f expr1, lType, map f expr2)
    | Map (x, ty, expr1, expr2) -> Map (x, ty, map f expr1, map f expr2)
    | Map2 (x, t1, y, t2, expr1, expr2, expr3) ->
        Map2 (x, t1, y, t2, map f expr1, map f expr2, map f expr3)
    | Map3 (x, t1, y, t2, z, t3, expr1, expr2, expr3, expr4) ->
        Map3
          ( x,
            t1,
            y,
            t2,
            z,
            t3,
            map f expr1,
            map f expr2,
            map f expr3,
            map f expr4 )
    | Reduce (x, t1, y, t2, expr1, expr2, expr3) ->
        Reduce (x, t1, y, t2, map f expr1, map f expr2, map f expr3)
    | Scan (x, t1, y, t2, expr1, expr2, expr3) ->
        Scan (x, t1, y, t2, map f expr1, map f expr2, map f expr3)
    | Zip (expr1, expr2) -> Zip (map f expr1, map f expr2)
    | Zip3 (expr1, expr2, expr3) -> Zip3 (map f expr1, map f expr2, map f expr3)
    | Unzip expr -> Unzip (map f expr)
    | Unzip3 expr -> Unzip3 (map f expr)
    | Fold (x, t1, y, t2, expr1, expr2, expr3) ->
        Fold (x, t1, y, t2, map f expr1, map f expr2, map f expr3)
    | Array exprList -> Array (List.map (map f) exprList))

let rec fold : type a. (a ast -> 'b -> 'b) -> a ast -> 'b -> 'b =
 fun f expr a ->
  f expr
    (match expr with
    | Var (_, _) | Const _ -> a
    | Apply1 (_, expr) -> fold f expr a
    | Fun (_, expr) -> fold f expr a
    | Unzip expr -> fold f expr a
    | Unzip3 expr -> fold f expr a
    | Apply2 (_, expr1, expr2)
    | Let (_, _, expr1, expr2)
    | Map (_, _, expr1, expr2) ->
        a |> fold f expr1 |> fold f expr2
    | Zip (expr1, expr2) -> a |> fold f expr1 |> fold f expr2
    | NCase (expr1, _, expr2) -> a |> fold f expr1 |> fold f expr2
    | Reduce (_, _, _, _, expr1, expr2, expr3)
    | Scan (_, _, _, _, expr1, expr2, expr3)
    | Fold (_, _, _, _, expr1, expr2, expr3) ->
        a |> fold f expr1 |> fold f expr2 |> fold f expr3
    | Map2 (_, _, _, _, expr1, expr2, expr3) ->
        a |> fold f expr1 |> fold f expr2 |> fold f expr3
    | Zip3 (expr1, expr2, expr3) ->
        a |> fold f expr1 |> fold f expr2 |> fold f expr3
    | Map3 (_, _, _, _, _, _, expr1, expr2, expr3, expr4) ->
        a |> fold f expr1 |> fold f expr2 |> fold f expr3 |> fold f expr4
    | Array exprList -> List.fold_right (fun e a -> fold f e a) exprList a
    | Tuple exprList -> List.fold_right (fun e a -> fold f e a) exprList a
    | App (expr, exprList) ->
        a |> fold f expr |> List.fold_right (fun e a -> fold f e a) exprList)

(* substitute variable x of type xTy by expr in expr2 *)
let subst : type a. Var.t -> a Type.t -> a ast -> a ast -> a ast =
 fun x xTy expr1 expr2 ->
  let aux : a ast -> a ast = function
    | Var (a, ty) as expr ->
        if Var.equal a x && Type.equal ty xTy then expr1 else expr
    | Let (y, ty, _, _) as expr ->
        if Var.equal x y && Type.equal xTy ty then
          invalid_arg "Language.subst: trying to substitute a bound variable"
        else expr
    | Fun (varList, _) as expr ->
        if
          List.exists
            (fun (y, ty) -> Var.equal x y && Type.equal ty xTy)
            varList
        then invalid_arg "Language.subst: trying to substitute a bound variable"
        else expr
    | NCase (_, varList, _) as expr ->
        if
          List.exists
            (fun (y, ty) -> Var.equal x y && Type.equal ty xTy)
            varList
        then invalid_arg "Language.subst: trying to substitute a bound variable"
        else expr
    | Map (y, ty1, _, _) as expr ->
        if Var.equal x y && Type.equal xTy ty1 then
          invalid_arg "Language.subst: trying to substitute a bound variable"
        else expr
    | Map2 (y1, t1, y2, t2, _, _, _) as expr ->
        if
          (Var.equal x y1 && Type.equal xTy t1)
          || (Var.equal x y2 && Type.equal xTy t2)
        then invalid_arg "Language.subst: trying to substitute a bound variable"
        else expr
    | ( Reduce (y1, t1, y2, t2, _, _, _)
      | Scan (y1, t1, y2, t2, _, _, _)
      | Fold (y1, t1, y2, t2, _, _, _) ) as expr ->
        if
          (Var.equal x y1 && Type.equal xTy t1)
          || (Var.equal x y2 && Type.equal xTy t2)
        then invalid_arg "Language.subst: trying to substitute a bound variable"
        else expr
    | Map3 (y1, t1, y2, t2, y3, t3, _, _, _, _) as expr ->
        if
          (Var.equal x y1 && Type.equal xTy t1)
          || (Var.equal x y2 && Type.equal xTy t2)
          || (Var.equal x y3 && Type.equal xTy t3)
        then invalid_arg "Language.subst: trying to substitute a bound variable"
        else expr
    | expr -> expr
  in
  map aux expr2

let isInContext v context = List.mem_assoc v context

let findInContext v context =
  CCList.Assoc.get ~eq:(CCPair.equal Var.equal Type.equal) v context

let simSubst : type a. a context -> a ast -> a ast =
 fun context expr ->
  let aux : a ast -> a ast = function
    | Var (a, ty1) as expr ->
        CCOpt.get_or ~default:expr (findInContext (a, ty1) context)
    | Let (y, ty1, _, _) as expr ->
        if isInContext (y, ty1) context then
          invalid_arg "Language.simSubst: trying to substitute a bound variable"
        else expr
    | Fun (varList, _) as expr ->
        if List.exists (fun (y, ty) -> isInContext (y, ty) context) varList then
          invalid_arg "Language.simSubst: trying to substitute a bound variable"
        else expr
    | NCase (_, varList, _) as expr ->
        if List.exists (fun (y, ty) -> isInContext (y, ty) context) varList then
          invalid_arg "Language.simSubst: trying to substitute a bound variable"
        else expr
    | Map2 (y1, t1, y2, t2, _, _, _) as expr ->
        if isInContext (y1, t1) context || isInContext (y2, t2) context then
          invalid_arg "Language.simSubst: trying to substitute a bound variable"
        else expr
    | ( Reduce (y1, t1, y2, t2, _, _, _)
      | Scan (y1, t1, y2, t2, _, _, _)
      | Fold (y1, t1, y2, t2, _, _, _) ) as expr ->
        if isInContext (y1, t1) context || isInContext (y2, t2) context then
          invalid_arg "Language.simSubst: trying to substitute a bound variable"
        else expr
    | Map3 (y1, t1, y2, t2, y3, t3, _, _, _, _) as expr ->
        if
          isInContext (y1, t1) context
          || isInContext (y2, t2) context
          || isInContext (y3, t3) context
        then
          invalid_arg "Language.simSubst: trying to substitute a bound variable"
        else expr
    | expr -> expr
  in
  map aux expr

(*  Checks whether two terms are equal up to alpha renaming.
    Two variables match iff they are the same free variable or they are both bound and equal up to renaming.
    This renaming is checked by carrying an explicit list of pairs of bound variables found so far in the term.
    When an occurence of bound variable is found deeper in the term, we check whether it matches the renaming *)
let equal : type a. ?eq:_ -> a ast -> a ast -> _ =
 fun ?(eq = Float.equal) expr1 expr2 ->
  let module PVTSet = CCSet.Make (struct
    type t = (Var.t * a Type.t) * (Var.t * a Type.t)

    let compare =
      CCPair.compare
        (CCPair.compare (CCPair.compare CCString.compare CCInt.compare) compare)
        (CCPair.compare (CCPair.compare CCString.compare CCInt.compare) compare)
  end) in
  let rec eqT : a ast -> a ast -> _ -> _ =
   fun expr1 expr2 alpha_set ->
    match (expr1, expr2) with
    | Const a, Const b -> eq a b
    | Var (a, ty1), Var (b, ty2) ->
        (Var.equal a b || PVTSet.mem ((a, ty1), (b, ty2)) alpha_set)
        && Type.equal ty1 ty2
    | Apply1 (op1, expr11), Apply1 (op2, expr22) ->
        Op.equalOp1 op1 op2 && eqT expr11 expr22 alpha_set
    | Apply2 (op1, expr11, expr12), Apply2 (op2, expr21, expr22) ->
        Op.equalOp2 op1 op2
        && eqT expr11 expr21 alpha_set
        && eqT expr12 expr22 alpha_set
    | Let (x, ty1, expr11, expr12), Let (y, ty2, expr21, expr22) ->
        Type.equal ty1 ty2
        && eqT expr11 expr21 alpha_set
        && eqT expr12 expr22 (PVTSet.add ((x, ty1), (y, ty2)) alpha_set)
    | App (expr11, exprList1), App (expr21, exprList2) ->
        eqT expr11 expr21 alpha_set
        && List.for_all2 (fun x y -> eqT x y alpha_set) exprList1 exprList2
    | Fun (varList1, expr1), Fun (varList2, expr2) ->
        if CCList.compare_lengths varList1 varList2 <> 0 then false
        else
          eqT expr1 expr2
            (PVTSet.add_list alpha_set (List.combine varList1 varList2))
          && List.for_all2
               (fun (_, ty1) (_, ty2) -> Type.equal ty1 ty2)
               varList1 varList2
    | Tuple exprList1, Tuple exprList2 ->
        CCList.equal
          (fun expr1 expr2 -> eqT expr1 expr2 alpha_set)
          exprList1 exprList2
    | NCase (expr11, varList1, expr12), NCase (expr21, varList2, expr22) ->
        if CCList.compare_lengths varList1 varList2 <> 0 then false
        else
          eqT expr11 expr21 alpha_set
          && eqT expr12 expr22
               (PVTSet.add_list alpha_set (List.combine varList1 varList2))
    | Map (x, ty1, expr11, expr12), Map (y, ty2, expr21, expr22) ->
        Type.equal ty1 ty2
        && eqT expr12 expr22 alpha_set
        && eqT expr11 expr21 (PVTSet.add ((x, ty1), (y, ty2)) alpha_set)
    | ( Map2 (x1, t11, y1, t12, expr11, expr12, expr13),
        Map2 (x2, t21, y2, t22, expr21, expr22, expr23) ) ->
        Type.equal t11 t21 && Type.equal t12 t22
        && eqT expr12 expr22 alpha_set
        && eqT expr13 expr23 alpha_set
        && eqT expr11 expr21
             (PVTSet.add
                ((y1, t12), (y2, t22))
                (PVTSet.add ((x1, t11), (x2, t21)) alpha_set))
    | ( Reduce (x1, t11, y1, t12, expr11, expr12, expr13),
        Reduce (x2, t21, y2, t22, expr21, expr22, expr23) )
    | ( Scan (x1, t11, y1, t12, expr11, expr12, expr13),
        Scan (x2, t21, y2, t22, expr21, expr22, expr23) )
    | ( Fold (x1, t11, y1, t12, expr11, expr12, expr13),
        Fold (x2, t21, y2, t22, expr21, expr22, expr23) ) ->
        Type.equal t11 t21 && Type.equal t12 t22
        && eqT expr12 expr22 alpha_set
        && eqT expr13 expr23 alpha_set
        && eqT expr11 expr21
             (PVTSet.add
                ((y1, t12), (y2, t22))
                (PVTSet.add ((x1, t11), (x2, t21)) alpha_set))
    | Zip (expr11, expr12), Zip (expr21, expr22) ->
        eqT expr11 expr21 alpha_set && eqT expr12 expr22 alpha_set
    | Zip3 (expr11, expr12, expr13), Zip3 (expr21, expr22, expr23) ->
        eqT expr11 expr21 alpha_set
        && eqT expr12 expr22 alpha_set
        && eqT expr13 expr23 alpha_set
    | Unzip expr1, Unzip expr2 -> eqT expr1 expr2 alpha_set
    | Unzip3 expr1, Unzip3 expr2 -> eqT expr1 expr2 alpha_set
    | Array exprList1, Array exprList2 ->
        CCList.equal
          (fun expr1 expr2 -> eqT expr1 expr2 alpha_set)
          exprList1 exprList2
    | ( Map3 (x1, t11, y1, t12, z1, t13, expr11, expr12, expr13, expr14),
        Map3 (x2, t21, y2, t22, z2, t23, expr21, expr22, expr23, expr24) ) ->
        Type.equal t11 t21 && Type.equal t12 t22 && Type.equal t13 t23
        && eqT expr12 expr22 alpha_set
        && eqT expr13 expr23 alpha_set
        && eqT expr14 expr24 alpha_set
        && eqT expr11 expr21
             (PVTSet.add
                ((z1, t13), (z2, t23))
                (PVTSet.add
                   ((y1, t12), (y2, t22))
                   (PVTSet.add ((x1, t11), (x2, t21)) alpha_set)))
    | _ -> false
  in
  eqT expr1 expr2 PVTSet.empty

let weakEqual : type a. a ast -> a ast -> _ =
 fun expr1 expr2 ->
  equal
    ~eq:(fun x y ->
      CCFloat.(
        equal_precision ~epsilon:(0.00001 * abs x) x y
        || (x = nan && y = nan)
        || (x = -nan && y = -nan)
        || (x = neg_infinity && y = neg_infinity)
        || (x = infinity && y = infinity)))
    expr1 expr2

let rec isValue : type a. a ast -> _ = function
  | Const _ -> true
  | Fun (_, _) -> true
  | Tuple exprList -> List.for_all isValue exprList
  | Array exprList -> List.for_all isValue exprList
  | _ -> false

let freeVar : type a. a ast -> _ =
 fun expr ->
  let aux : a ast -> _ =
   fun expr set ->
    match expr with
    | Var (x, _) -> VarSet.add x set
    | Let (y, _, _, _) -> VarSet.filter (fun x -> not (Var.equal x y)) set
    | Fun (varList, _) -> VarSet.(diff set (of_list (List.map fst varList)))
    | NCase (_, varList, _) ->
        VarSet.(diff set (of_list (List.map fst varList)))
    | Map2 (y1, _, y2, _, _, _, _)
    | Reduce (y1, _, y2, _, _, _, _)
    | Scan (y1, _, y2, _, _, _, _)
    | Fold (y1, _, y2, _, _, _, _) ->
        VarSet.filter
          (fun x -> (not (Var.equal x y1)) && not (Var.equal x y2))
          set
    | Map3 (y1, _, y2, _, y3, _, _, _, _, _) ->
        VarSet.filter
          (fun x ->
            (not (Var.equal x y1))
            && (not (Var.equal x y2))
            && not (Var.equal x y3))
          set
    | _ -> set
  in
  fold aux expr VarSet.empty

(* collects the list of unused bound variables *)
let listUnusedVar : type a. a ast -> (_ * a Type.t) list =
 fun expr ->
  let aux : a ast -> (Var.t * a Type.t) list -> (Var.t * a Type.t) list =
   fun expr l ->
    match expr with
    | Let (x, ty, _, expr2) ->
        (if VarSet.mem x (freeVar expr2) then [] else [ (x, ty) ]) @ l
    | NCase (_, varList, expr2) ->
        (let fv = freeVar expr2 in
         List.filter (fun (y, _) -> not (VarSet.mem y fv)) varList)
        @ l
    | Map (x, ty, expr1, _) ->
        (if VarSet.mem x (freeVar expr1) then [] else [ (x, ty) ]) @ l
    | Map2 (y1, ty1, y2, ty2, expr, _, _) ->
        (let fv = freeVar expr in
         List.filter
           (fun (y, _) -> not (VarSet.mem y fv))
           [ (y1, ty1); (y2, ty2) ])
        @ l
    | Reduce (y1, ty1, y2, ty2, expr, _, _)
    | Scan (y1, ty1, y2, ty2, expr, _, _)
    | Fold (y1, ty1, y2, ty2, expr, _, _) ->
        (let fv = freeVar expr in
         List.filter
           (fun (y, _) -> not (VarSet.mem y fv))
           [ (y1, ty1); (y2, ty2) ])
        @ l
    | Map3 (y1, ty1, y2, ty2, y3, ty3, expr, _, _, _) ->
        (let fv = freeVar expr in
         List.filter
           (fun (y, _) -> not (VarSet.mem y fv))
           [ (y1, ty1); (y2, ty2); (y3, ty3) ])
        @ l
    | _ -> l
  in
  fold aux expr []

let varNameNotBound : type a. string -> a ast -> _ =
 fun name expr ->
  let aux : a ast -> _ = function
    | Let ((str, _), _, _, _) -> str <> name
    | Fun (varList, _) ->
        List.for_all (fun ((str, _), _) -> str <> name) varList
    | NCase (_, varList, _) ->
        List.for_all (fun ((str, _), _) -> str <> name) varList
    | Map ((str, _), _, _, _) -> str <> name
    | Map2 ((str1, _), _, (str2, _), _, _, _, _)
    | Reduce ((str1, _), _, (str2, _), _, _, _, _)
    | Scan ((str1, _), _, (str2, _), _, _, _, _)
    | Fold ((str1, _), _, (str2, _), _, _, _, _) ->
        str1 <> name && str2 <> name
    | Map3 ((str1, _), _, (str2, _), _, (str3, _), _, _, _, _, _) ->
        str1 <> name && str2 <> name && str3 <> name
    | _ -> true
  in
  fold (fun expr b -> b && aux expr) expr true

let indexOf el a =
  match CCArray.find_idx (( = ) el) a with
  | None ->
      invalid_arg "Language.canonicalAlphaRename: Element not found in the list"
  | Some (i, _) -> i

let canonicalAlphaRename (name : string) expr =
  let freeV = VarSet.to_list (freeVar expr) |> Array.of_list in
  if varNameNotBound name expr then
    let canRen =
      map (function
        | Var (s, ty) ->
            let i = indexOf s freeV in
            Var ((name, i), ty)
        | expr -> expr)
    in
    canRen expr
  else
    invalid_arg
      (Printf.sprintf
         "Language.canonicalAlphaRename: variable %s is already used as a \
          bound variable, can't rename free vars canonically with %s"
         name name)

(* simple typecheker *)
let rec inferType : type a. a ast -> (a Type.t, _) Result.t =
 fun expr ->
  let open CCResult in
  match expr with
  | Const _ -> Result.Ok Type.Real
  | Var (_, t) -> Result.Ok t
  | Apply1 (_, expr) -> (
      inferType expr >>= function
      | Real -> Ok Type.Real
      | _ -> Error "Argument of Apply1 should be a Real")
  | Apply2 (_, expr1, expr2) -> (
      inferType expr1 >>= function
      | Real -> (
          inferType expr2 >>= function
          | Real -> Ok Type.Real
          | _ -> Error "Argumentt 2 of Apply2 should be a Real")
      | _ -> Error "Argument 1 of Apply2 should be a Real")
  | Let (_, t, expr1, expr2) ->
      inferType expr1 >>= fun t1 ->
      if t = t1 then inferType expr2
      else
        Error
          "in Let binding type of the variable does not correspond to the type \
           of the expression"
  | Fun (l, expr) ->
      inferType expr >|= fun texp -> Type.Arrow (List.map snd l, texp)
  | App (expr, l) -> (
      inferType expr >>= function
      | Arrow (tyList, retType) ->
          if List.compare_lengths tyList l <> 0 then
            Error "Wrong number of arguments in App"
          else
            List.map inferType l |> flatten_l >>= fun l ->
            if CCList.equal Type.equal tyList l then Ok retType
            else Error "Type mismatch with arguments type"
      | _ -> Error "App: expr should be of Arrow type")
  | Tuple l -> List.map inferType l |> flatten_l >>= fun l -> Ok (Type.Prod l)
  | NCase (expr1, l, expr2) -> (
      inferType expr1 >>= function
      | Prod tl ->
          if List.for_all2 Type.equal tl (List.map snd l) then inferType expr2
          else Error "NCase: type mismatch"
      | _ -> Error "NCase: expression 1 should have type Prod")
  | Map (_, ty, expr1, expr2) -> (
      let* t2 = inferType expr2 in
      match t2 with
      | Array (n, t2) ->
          if Type.equal ty t2 then
            inferType expr1 >|= fun t1 -> Type.Array (n, t1)
          else
            Error
              "in Map type of the function argument does not correspond to the \
               type of the elements of the array"
      | _ -> Error "type of the expression should be array")
  | Map2 (_, ty1, _, ty2, expr1, expr2, expr3) -> (
      let* t2 = inferType expr2 in
      let* t3 = inferType expr3 in
      match (t2, t3) with
      | Array (n, t2), Array (m, t3) ->
          if (not (Type.equal ty1 t2)) || not (Type.equal ty2 t3) then
            Error
              "in Map2 type of one of the function argument does not \
               correspond to the type of the elements of the array"
          else if not (n = m) then
            Error "in Map2 the two arguments should be vectors of the same size"
          else inferType expr1 >|= fun t1 -> Type.Array (n, t1)
      | _ -> Error "type of the expression should be array")
  | Map3 (_, ty1, _, ty2, _, ty3, expr1, expr2, expr3, expr4) -> (
      let* t2 = inferType expr2 in
      let* t3 = inferType expr3 in
      let* t4 = inferType expr4 in
      match (t2, t3, t4) with
      | Array (n, t2), Array (m, t3), Array (p, t4) ->
          if
            (not (Type.equal ty1 t2))
            || (not (Type.equal ty2 t3))
            || not (Type.equal ty3 t4)
          then
            Error
              "in Map3 type of one of the function argument does not \
               correspond to the type of the elements of the array"
          else if not (n = m && n = p) then
            Error
              "in Map3 the three arguments should be vectors of the same size"
          else inferType expr1 >|= fun t1 -> Type.Array (n, t1)
      | _ -> Error "type of the expression should be array")
  | Reduce (_, ty1, _, ty2, expr1, expr2, expr3) -> (
      let* t1 = inferType expr1 in
      let* t2 = inferType expr2 in
      let* t3 = inferType expr3 in
      match t3 with
      | Array (_, t3) ->
          if
            Type.equal ty1 ty2 && Type.equal ty2 t1 && Type.equal t1 t2
            && Type.equal t2 t3
          then Ok t1
          else Error "in Reduce not all the types are the same"
      | _ -> Error "type of the expression should be array")
  | Scan (_, ty1, _, ty2, expr1, expr2, expr3) -> (
      inferType expr2 >>= fun t2 ->
      if not (Type.equal ty1 t2) then
        Error
          "In Scan type of the first argument does not match type of first \
           variable of the function"
      else
        inferType expr3 >>= fun t3 ->
        match t3 with
        | Array (n, t3) ->
            if not (Type.equal ty2 t3) then
              Error
                "In Scan type of the second argument does not match type of \
                 second variable of the function"
            else
              inferType expr1 >>= fun t1 ->
              if not (Type.equal ty1 t1) then
                Error
                  "In Scan type of the first argument does not match return \
                   type of the function"
              else Ok (Type.Array (n, t1))
        | _ -> Error "in Scan type of the third argument is not an array")
  | Fold (_, ty1, _, ty2, expr1, expr2, expr3) -> (
      inferType expr2 >>= fun t2 ->
      if not (Type.equal ty1 t2) then
        Error
          "In Fold type of the first argument does not match type of first \
           variable of the function"
      else
        inferType expr3 >>= fun t3 ->
        match t3 with
        | Array (_, t3) ->
            if not (Type.equal ty2 t3) then
              Error
                "In Fold type of the second argument does not match type of \
                 second variable of the function"
            else
              inferType expr1 >>= fun t1 ->
              if not (Type.equal ty1 t1) then
                Error
                  "In Fold type of the first argument does not match return \
                   type of the function"
              else Ok t1
        | _ -> Error "in Fold type of the third argument is not an array")
  | Zip (expr1, expr2) -> (
      inferType expr1 >>= function
      | Type.Array (n1, t1) -> (
          inferType expr2 >>= function
          | Type.Array (n2, t2) ->
              if n1 = n2 then Ok (Type.Array (n1, Type.Prod [ t1; t2 ]))
              else Error "in Zip the two arrays should have the same length"
          | _ -> Error "Argument 2 of Zip should be a Type.Array")
      | _ -> Error "Argument 1 of Zip should be a Type.Array")
  | Zip3 (expr1, expr2, expr3) -> (
      inferType expr1 >>= function
      | Type.Array (n1, t1) -> (
          inferType expr2 >>= function
          | Type.Array (n2, t2) -> (
              inferType expr3 >>= function
              | Type.Array (n3, t3) ->
                  if n1 = n2 && n1 = n3 then
                    Ok (Type.Array (n1, Type.Prod [ t1; t2; t3 ]))
                  else
                    Error "in Zip3 the three arrays should have the same length"
              | _ -> Error "Argument 3 of Zip3 should be a Type.Array")
          | _ -> Error "Argument 2 of Zip3 should be a Type.Array")
      | _ -> Error "Argument 1 of Zip3 should be a Type.Array")
  | Unzip expr -> (
      inferType expr >>= function
      | Type.Array (m, Type.Prod [ t1; t2 ]) ->
          Ok (Type.Prod [ Type.Array (m, t1); Type.Array (m, t2) ])
      | _ -> Error "Argument of Unzip should be an array of pairs")
  | Unzip3 expr -> (
      inferType expr >>= function
      | Type.Array (m, Type.Prod [ t1; t2; t3 ]) ->
          Ok
            (Type.Prod
               [ Type.Array (m, t1); Type.Array (m, t2); Type.Array (m, t3) ])
      | _ -> Error "Argument of Unzip3 should be an array of triples")
  (* | Get (n, expr) -> (
     inferType expr >>= function
     | Type.Array(m, t1) -> if n<m then Ok t1
                            else Error "trying to get an element out of bounds of an array"
     | _ -> Error "Argument 2 of Zip should be a Type.Array"
     ) *)
  | Array exprList -> (
      List.map inferType exprList |> flatten_l >>= function
      | [] -> Error "Empty array"
      | h :: t ->
          if CCList.for_all (Type.equal h) t then
            Ok (Type.Array (List.length exprList, h))
          else Error "All elements of an array should have the same type.")

let isWellTyped expr = inferType expr |> Result.is_ok

(* interpreter *)

(* checks whether the context captures all the free variables of an expression*)
let contextComplete expr context =
  VarSet.for_all
    (fun x -> List.exists (fun ((y, _), _) -> Var.equal y x) context)
    (freeVar expr)

let interpretOp1 op expr =
  match expr with
  | Const v -> Const (Op.interpretOp1 op v)
  | expr -> Apply1 (op, expr)

let interpretOp2 op expr1 expr2 =
  match (expr1, expr2) with
  | Const v1, Const v2 -> Const (Op.interpretOp2 op v1 v2)
  | expr1, expr2 -> Apply2 (op, expr1, expr2)

let interpret : type a. a ast -> a context -> a ast =
 fun expr context ->
  let module M = CCMap.Make (struct
    type t = Var.t * a Type.t

    let compare =
      CCPair.compare (CCPair.compare CCString.compare CCInt.compare) compare
  end) in
  if not (isWellTyped expr) then failwith "interpret: ill typed term";
  let rec interp : a ast M.t -> a ast -> a ast =
   fun context expr ->
    match expr with
    | Var (v, t) -> (
        match M.get (v, t) context with
        | Some expr -> interp context expr
        | None -> expr)
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
            Array
              (List.map
                 (fun e -> interp (M.add (x, ty) e context) expr1)
                 exprList)
        | expr2 -> Map (x, ty, expr1, expr2))
    | Map2 (x, t1, y, t2, expr1, expr2, expr3) -> (
        let expr1 = interp context expr1 in
        match (interp context expr2, interp context expr3) with
        | Array exprList1, Array exprList2 ->
            Array
              (List.map2
                 (fun e1 e2 ->
                   interp (M.add (y, t2) e2 (M.add (x, t1) e1 context)) expr1)
                 exprList1 exprList2)
        | expr2, expr3 -> Map2 (x, t1, y, t2, expr1, expr2, expr3))
    | Map3 (x, t1, y, t2, z, t3, expr1, expr2, expr3, expr4) -> (
        let expr1 = interp context expr1 in
        match
          (interp context expr2, interp context expr3, interp context expr4)
        with
        | Array exprList1, Array exprList2, Array exprList3 ->
            let rec map3 f l1 l2 l3 =
              match (l1, l2, l3) with
              | [], [], [] -> []
              | a :: l1, b :: l2, c :: l3 -> f a b c :: map3 f l1 l2 l3
              | _ -> assert false
            in
            Array
              (map3
                 (fun e1 e2 e3 ->
                   interp
                     (M.add (z, t3) e3
                        (M.add (y, t2) e2 (M.add (x, t1) e1 context)))
                     expr1)
                 exprList1 exprList2 exprList3)
        | expr2, expr3, expr4 ->
            Map3 (x, t1, y, t2, z, t3, expr1, expr2, expr3, expr4))
    | Fold (x, t1, y, t2, expr1, expr2, expr3)
    | Reduce (x, t1, y, t2, expr1, expr2, expr3) -> (
        let expr1 = interp context expr1 in
        let expr2 = interp context expr2 in
        match interp context expr3 with
        | Array exprList ->
            List.fold_left
              (fun acc e ->
                interp (M.add (y, t2) e (M.add (x, t1) acc context)) expr1)
              expr2 exprList
        | expr3 -> Reduce (x, t1, y, t2, expr1, expr2, expr3))
    | Scan (x, t1, y, t2, expr1, expr2, expr3) -> (
        let expr1 = interp context expr1 in
        let expr2 = interp context expr2 in
        match interp context expr3 with
        | Array exprList ->
            List.fold_left
              (fun (acc, l) e ->
                let tmp =
                  interp (M.add (y, t2) e (M.add (x, t1) acc context)) expr1
                in
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
        match
          (interp context expr1, interp context expr2, interp context expr3)
        with
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
                  (List.rev_map
                     (fun e ->
                       match e with
                       | Tuple [ e1; e2; e3 ] -> (e1, e2, e3)
                       | _ -> failwith "")
                     exprList)
              in
              Tuple [ Array exprList1; Array exprList2; Array exprList3 ]
            else Unzip3 (Array exprList)
        | exprList -> Unzip3 exprList)
    | Array exprList -> Array (List.map (interp context) exprList)
  in
  interp (M.of_list context) expr

(** {2 Traverse} *)
module Traverse (S : Strategy.S) = struct
  open S

  let rec map :
      type a. (a ast -> a ast Rewriter.output) -> a ast -> a ast Rewriter.output
      =
   fun f expr ->
    return expr >>= f >>= function
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
    | Map2 (x, t1, y, t2, expr1, expr2, expr3) -> (
        applyl (map f) [ expr1; expr2; expr3 ] >|= fun l ->
        match l with
        | [ e1; e2; e3 ] -> Map2 (x, t1, y, t2, e1, e2, e3)
        | _ -> assert false)
    | Map3 (x, t1, y, t2, z, t3, expr1, expr2, expr3, expr4) -> (
        applyl (map f) [ expr1; expr2; expr3; expr4 ] >|= fun l ->
        match l with
        | [ e1; e2; e3; e4 ] -> Map3 (x, t1, y, t2, z, t3, e1, e2, e3, e4)
        | _ -> assert false)
    | Reduce (x, t1, y, t2, expr1, expr2, expr3) -> (
        applyl (map f) [ expr1; expr2; expr3 ] >|= fun l ->
        match l with
        | [ e1; e2; e3 ] -> Reduce (x, t1, y, t2, e1, e2, e3)
        | _ -> assert false)
    | Scan (x, t1, y, t2, expr1, expr2, expr3) -> (
        applyl (map f) [ expr1; expr2; expr3 ] >|= fun l ->
        match l with
        | [ e1; e2; e3 ] -> Scan (x, t1, y, t2, e1, e2, e3)
        | _ -> assert false)
    | Zip (expr1, expr2) ->
        apply2 (map f) expr1 expr2 >|= fun (expr1, expr2) -> Zip (expr1, expr2)
    | Zip3 (expr1, expr2, expr3) -> (
        applyl (map f) [ expr1; expr2; expr3 ] >|= fun l ->
        match l with [ e1; e2; e3 ] -> Zip3 (e1, e2, e3) | _ -> assert false)
    | Unzip expr -> map f expr >|= fun expr -> Unzip expr
    | Unzip3 expr -> map f expr >|= fun expr -> Unzip3 expr
    | Fold (x, t1, y, t2, expr1, expr2, expr3) -> (
        applyl (map f) [ expr1; expr2; expr3 ] >|= fun l ->
        match l with
        | [ e1; e2; e3 ] -> Fold (x, t1, y, t2, e1, e2, e3)
        | _ -> assert false)
    | Array exprList -> applyl (map f) exprList >|= fun l -> Array l
end

module type Algebra = sig
  type 'a ret

  val var : Var.t -> 'a Type.t -> 'a ret

  val const : float -> 'a ret

  val apply1 : Op.op1 -> 'a ret -> 'a ret

  val apply2 : Op.op2 -> 'a ret -> 'a ret -> 'a ret

  val clet : Var.t -> 'a Type.t -> 'a ret -> 'a ret -> 'a ret

  val cfun : (Var.t * target Type.t) list -> target ret -> target ret

  val app : target ret -> target ret list -> target ret

  val tuple : target ret tuple -> target ret

  val ncase : target ret -> (Var.t * target Type.t) list -> target ret -> target ret

  val map : Var.t -> 'a Type.t -> 'a ret -> 'a ret -> 'a ret

  val map2 :
    Var.t ->
    target Type.t ->
    Var.t ->
    target Type.t ->
    target ret ->
    target ret ->
    target ret ->
    target ret

  val map3 :
    Var.t ->
    target Type.t ->
    Var.t ->
    target Type.t ->
    Var.t ->
    target Type.t ->
    target ret ->
    target ret ->
    target ret ->
    target ret ->
    target ret

  val reduce :
    Var.t ->
    'a Type.t ->
    Var.t ->
    'a Type.t ->
    'a ret ->
    'a ret ->
    'a ret ->
    'a ret

  val scan :
    Var.t ->
    'a Type.t ->
    Var.t ->
    'a Type.t ->
    'a ret ->
    'a ret ->
    'a ret ->
    'a ret

  val zip : target ret -> target ret -> target ret

  val unzip : target ret -> target ret

  val zip3 : target ret -> target ret -> target ret -> target ret

  val unzip3 : target ret -> target ret

  val fold :
    Var.t ->
    'a Type.t ->
    Var.t ->
    'a Type.t ->
    'a ret ->
    'a ret ->
    'a ret ->
    'a ret

  val array : 'a ret list -> 'a ret
end

module Catamorphism (A : Algebra) = struct
  let rec run : type a. a ast -> a A.ret = function
    | Var (a, t) -> A.var a t
    | Const c -> A.const c
    | Apply1 (op, expr) -> A.apply1 op (run expr)
    | Apply2 (op, expr1, expr2) -> A.apply2 op (run expr1) (run expr2)
    | Let (x, t, expr1, expr2) -> A.clet x t (run expr1) (run expr2)
    | Fun (vars, expr) -> A.cfun vars (run expr)
    | App (expr, exprs) -> A.app (run expr) (List.map run exprs)
    | Tuple exprs -> A.tuple (List.map run exprs)
    | NCase (expr1, vars, expr2) -> A.ncase (run expr1) vars (run expr2)
    | Map (x, t, expr1, expr2) -> A.map x t (run expr1) (run expr2)
    | Map2 (x, t1, y, t2, expr1, expr2, expr3) ->
        A.map2 x t1 y t2 (run expr1) (run expr2) (run expr3)
    | Map3 (x, t1, y, t2, z, t3, expr1, expr2, expr3, expr4) ->
        A.map3 x t1 y t2 z t3 (run expr1) (run expr2) (run expr3) (run expr4)
    | Reduce (x, t1, y, t2, expr1, expr2, expr3) ->
        A.reduce x t1 y t2 (run expr1) (run expr2) (run expr3)
    | Scan (x, t1, y, t2, expr1, expr2, expr3) ->
        A.scan x t1 y t2 (run expr1) (run expr2) (run expr3)
    | Zip (expr1, expr2) -> A.zip (run expr1) (run expr2)
    | Zip3 (expr1, expr2, expr3) -> A.zip3 (run expr1) (run expr2) (run expr3)
    | Unzip expr -> A.unzip (run expr)
    | Unzip3 expr -> A.unzip3 (run expr)
    | Fold (x, t1, y, t2, expr1, expr2, expr3) ->
        A.fold x t1 y t2 (run expr1) (run expr2) (run expr3)
    | Array exprList -> A.array (List.map run exprList)
end

type ('a, 'b) algebra =
  < var : Var.t -> 'a Type.t -> 'b
  ; const : float -> 'b
  ; apply1 : Op.op1 -> 'b -> 'b
  ; apply2 : Op.op2 -> 'b -> 'b -> 'b
  ; alet : Var.t -> 'a Type.t -> 'b -> 'b -> 'b
  ; afun : (Var.t * 'a Type.t) list -> 'b -> 'b
  ; app : 'b -> 'b list -> 'b
  ; tuple : 'b tuple -> 'b
  ; nCase : 'b -> (Var.t * 'a Type.t) list -> 'b -> 'b
  ; map : Var.t -> 'a Type.t -> 'b -> 'b -> 'b
  ; map2 : Var.t -> 'a Type.t -> Var.t -> 'a Type.t -> 'b -> 'b -> 'b -> 'b
  ; map3 :
      Var.t ->
      'a Type.t ->
      Var.t ->
      'a Type.t ->
      Var.t ->
      'a Type.t ->
      'b ->
      'b ->
      'b ->
      'b ->
      'b
  ; reduce : Var.t -> 'a Type.t -> Var.t -> 'a Type.t -> 'b -> 'b -> 'b -> 'b
  ; scan : Var.t -> 'a Type.t -> Var.t -> 'a Type.t -> 'b -> 'b -> 'b -> 'b
  ; zip : 'b -> 'b -> 'b
  ; unzip : 'b -> 'b
  ; zip3 : 'b -> 'b -> 'b -> 'b
  ; unzip3 : 'b -> 'b
  ; fold : Var.t -> 'a Type.t -> Var.t -> 'a Type.t -> 'b -> 'b -> 'b -> 'b
  ; array : 'b list -> 'b >

let catamorphism : type a. (a, 'b) algebra -> a ast -> 'b =
 fun algebra ->
  let rec run : a ast -> 'b = function
    | Var (a, t) -> algebra#var a t
    | Const c -> algebra#const c
    | Apply1 (op, expr) -> algebra#apply1 op (run expr)
    | Apply2 (op, expr1, expr2) -> algebra#apply2 op (run expr1) (run expr2)
    | Let (x, t, expr1, expr2) -> algebra#alet x t (run expr1) (run expr2)
    | Fun (vars, expr) -> algebra#afun vars (run expr)
    | App (expr, exprs) -> algebra#app (run expr) (List.map run exprs)
    | Tuple exprs -> algebra#tuple (List.map run exprs)
    | NCase (expr1, vars, expr2) -> algebra#nCase (run expr1) vars (run expr2)
    | Map (x, t, expr1, expr2) -> algebra#map x t (run expr1) (run expr2)
    | Map2 (x, t1, y, t2, expr1, expr2, expr3) ->
        algebra#map2 x t1 y t2 (run expr1) (run expr2) (run expr3)
    | Map3 (x, t1, y, t2, z, t3, expr1, expr2, expr3, expr4) ->
        algebra#map3 x t1 y t2 z t3 (run expr1) (run expr2) (run expr3)
          (run expr4)
    | Reduce (x, t1, y, t2, expr1, expr2, expr3) ->
        algebra#reduce x t1 y t2 (run expr1) (run expr2) (run expr3)
    | Scan (x, t1, y, t2, expr1, expr2, expr3) ->
        algebra#scan x t1 y t2 (run expr1) (run expr2) (run expr3)
    | Zip (expr1, expr2) -> algebra#zip (run expr1) (run expr2)
    | Zip3 (expr1, expr2, expr3) ->
        algebra#zip3 (run expr1) (run expr2) (run expr3)
    | Unzip expr -> algebra#unzip (run expr)
    | Unzip3 expr -> algebra#unzip3 (run expr)
    | Fold (x, t1, y, t2, expr1, expr2, expr3) ->
        algebra#fold x t1 y t2 (run expr1) (run expr2) (run expr3)
    | Array exprList -> algebra#array (List.map run exprList)
  in
  run
