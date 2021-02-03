open Containers
open Syntax
open Source

module TypeGen = struct
  let real = Type.Real

  let _prod x y = Type.Prod (x, y)

  let gen depth =
    QCheck.Gen.(
      sized_size (int_bound depth)
      @@ fix (fun _self n ->
             match n with
             | 0 -> return real
             | _n ->
                 frequency
                   [
                     (*(2, map2 prod (self (n / 2)) (self (n / 2)));*)
                     (1, return real);
                   ]))
end

let var x t = Var (x, t)

let const x = Const x

let apply1 op exp = Apply1 (op, exp)

let apply2 op exp1 exp2 = Apply2 (op, exp1, exp2)

let clet v t exp1 exp2 = Let (v, t, exp1, exp2)

let carray l = Array l

let dist_to_type (targetTy : Type.t) (ty : Type.t) =
  match (targetTy, ty) with Type.Real, Type.Real -> Some 0 | _ -> None

let _random_closest_type targetTy tyList =
  let open QCheck.Gen in
  List.mapi
    (fun i ty ->
      match dist_to_type targetTy ty with
      | None -> None
      | Some d -> Some (ty, i, d))
    tyList
  |> CCList.keep_some
  |> function
  | [] -> None
  | (_, _, d) :: tl as l ->
      let d_min = List.fold_left (fun x (_, _, d) -> min x d) d tl in
      Some (generate1 (oneofl (List.filter (fun (_, _, d) -> d = d_min) l)))

let rec complet_to_type _context n (targetTy : Type.t) (term : t) (ty : Type.t)
    =
  if Type.equal targetTy ty then Some term
  else if n <= 0 then None
  else match (targetTy, ty) with Type.Real, Type.Real -> Some term | _ -> None

and get_from_context context n targetTy =
  List.filter_map
    (fun (v, t) ->
      match dist_to_type targetTy t with
      | None -> None
      | Some d -> Some (v, t, d))
    context
  |> function
  | [] -> None
  | (_, _, d) :: t as l -> (
      let d_min = List.fold_left (fun x (_, _, d) -> min x d) d t in
      match List.filter (fun (_, _, d) -> d = d_min) l with
      | [] -> None
      | l ->
          let v, t, _ = QCheck.Gen.(generate1 (oneofl l)) in
          complet_to_type context n targetTy (var v t) t)

and gen context (n : int) targetTy =
  QCheck.Gen.(
    sized_size (return n) @@ fun i ->
    fix
      (fun self (n, context, targetTy) ->
        if n <= 0 then
          match targetTy with
          | Type.Real -> map const (float_bound_exclusive 1.)
          | Type.Prod (_x1, _x2) -> failwith "Prod: not implemented"
          | Type.Array (n, t) -> map carray (list_repeat n (gen context 0 t))
        else
          let let_gen =
            let newVar = Var.fresh () in
            let varType = generate1 (TypeGen.gen (n / 10)) in
            let newContext = (newVar, varType) :: context in
            map2
              (fun expr1 expr2 -> clet newVar varType expr1 expr2)
              (self (n / 4, context, varType))
              (self (3 * n / 4, newContext, targetTy))
          in
          let gen_list = [ let_gen ] in
          let gen_list =
            match get_from_context context n targetTy with
            | None -> gen_list
            | Some term -> return term :: gen_list
          in
          match targetTy with
          | Type.Real ->
              oneof
                (map2 apply1 OperatorGen.gen1 (self (n - 1, context, Type.Real))
                :: map3 apply2 OperatorGen.gen2
                     (self (n / 2, context, Type.Real))
                     (self (n / 2, context, Type.Real))
                :: map const (float_bound_exclusive 1.)
                :: gen_list)
          | _ -> oneof gen_list)
      (i, context, targetTy))

let rec shrink expr =
  let open QCheck.Iter in
  match expr with
  | Var (_, _) | Const _ -> empty
  | Apply1 (op, expr) ->
      return expr
      <+> (shrink expr >|= apply1 op)
      <+> (OperatorGen.shrink1 op >|= fun op -> apply1 op expr)
  | Apply2 (op, expr1, expr2) ->
      of_list [ expr1; expr2 ]
      <+> (shrink expr1 >|= fun expr -> apply2 op expr expr2)
      <+> (shrink expr2 >|= fun expr -> apply2 op expr1 expr)
  | Let (x, t, expr1, expr2) ->
      shrink expr1
      >|= (fun expr -> clet x t expr expr2)
      <+> (shrink expr2 >|= fun expr -> clet x t expr1 expr)
  | _ -> empty (* TODO *)
