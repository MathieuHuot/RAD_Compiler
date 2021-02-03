open Containers
open Syntax
open Target

module TypeGen = struct
  let real = Type.Real

  let arrow t1 t2 = Type.Arrow (t1, t2)

  let nprod l = Type.NProd l

  let gen depth =
    QCheck.Gen.(
      sized_size (int_bound depth)
      @@ fix (fun self n ->
             match n with
             | 0 -> return real
             | n ->
                 frequency
                   [
                     ( 2,
                       map2 arrow
                         (list_size (int_bound 20) (self (min (n / 20) 2)))
                         (self (n / 2)) );
                     ( 2,
                       int_range 0 20 >>= fun i ->
                       map nprod (list_repeat i (self (n / max 2 i))) );
                     (1, return real);
                   ]))
end

let var x t = Var (x, t)

let const x = Const x

let apply1 op exp = Apply1 (op, exp)

let apply2 op exp1 exp2 = Apply2 (op, exp1, exp2)

let clet v t exp1 exp2 = Let (v, t, exp1, exp2)

let func l exp = Fun (l, exp)

let app exp l = App (exp, l)

let tuple l = Tuple l

let ncase exp1 l exp2 = NCase (exp1, l, exp2)

let rec dist_to_type (targetTy : Type.t) (ty : Type.t) =
  match (targetTy, ty) with
  | Type.Real, Type.Real -> Some 0
  | Type.Real, Arrow (l, ty) ->
      CCOpt.(dist_to_type targetTy ty >|= ( + ) (List.length l))
  | Arrow (_, _), Type.Real -> None
  | Arrow (l1, t1), Arrow (l2, t2) ->
      CCOpt.(
        dist_to_type t1 t2 >>= fun d ->
        List.map
          (fun t ->
            match List.filter_map (dist_to_type t) l2 with
            | [] -> None
            | h :: t -> Some (List.fold_left min h t))
          l1
        |> sequence_l
        >|= fun l -> List.fold_left ( + ) d l)
  | NProd l1, NProd l2 ->
      CCOpt.(
        List.map
          (fun t ->
            match List.filter_map (dist_to_type t) l2 with
            | [] -> None
            | h :: t -> Some (List.fold_left min h t))
          l1
        |> sequence_l
        >|= fun l -> List.fold_left ( + ) 0 l)
  | NProd l, _ ->
      CCOpt.(
        List.map (fun t -> dist_to_type t ty) l
        |> sequence_l >|= List.fold_left ( + ) 1)
  | _, NProd l -> (
      match List.filter_map (dist_to_type targetTy) l with
      | [] -> None
      | h :: t -> Some (1 + List.fold_left min h t))

let random_closest_type targetTy tyList =
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

let rec complet_to_type context n (targetTy : Type.t) (term : t) (ty : Type.t) =
  if Type.equal targetTy ty then Some term
  else if n <= 0 then None
  else
    match (targetTy, ty) with
    | Type.Real, Type.Real -> Some term
    | Type.Real, Arrow (l, ty) ->
        complet_to_type context
          (n - List.length l)
          targetTy
          (App
             ( term,
               List.map
                 (fun t ->
                   QCheck.Gen.generate1 (gen context (n - List.length l) t))
                 l ))
          ty
    | NProd targetList, NProd termList ->
        CCOpt.(
          List.map
            (fun t ->
              match random_closest_type t termList with
              | None -> None
              | Some x -> Some (t, x))
            targetList
          |> sequence_l
          >>= fun l ->
          let newVar = List.map (fun t -> (Var.fresh (), t)) termList in
          List.map
            (fun (targetTy, (_, i, _)) ->
              let v, t = CCList.get_at_idx_exn i newVar in
              complet_to_type context
                (n - List.length targetList)
                targetTy (var v t) t)
            l
          |> sequence_l
          >|= fun l -> NCase (term, newVar, Tuple l))
    | _, NProd typeList ->
        CCOpt.(
          random_closest_type targetTy typeList >>= fun (t, i, _) ->
          let newVar = List.map (fun t -> (Var.fresh (), t)) typeList in
          complet_to_type context (n - 1) targetTy
            (NCase
               ( term,
                 newVar,
                 let v, ty = CCList.get_at_idx_exn i newVar in
                 var v ty ))
            t)
    | Arrow (_, _), Type.Real -> None
    | Arrow (_l1, _t1), Arrow (_l2, _t2) -> None
    | NProd l, _ ->
        CCOpt.(
          List.map
            (fun t ->
              complet_to_type context (n / max 2 (List.length l)) t term ty)
            l
          |> sequence_l
          >|= fun l -> Tuple l)

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
          complet_to_type context n targetTy (Var (v, t)) t)

and gen context (n : int) targetTy =
  QCheck.Gen.(
    sized_size (return n) @@ fun i ->
    fix
      (fun self (n, context, targetTy) ->
        if n <= 0 then
          match targetTy with
          | Type.Real -> map const (float_bound_exclusive 1.)
          | Arrow (tyList, retType) ->
              let argsList = List.map (fun tv -> (Var.fresh (), tv)) tyList in
              let newContext = argsList @ context in
              map
                (fun expr -> func argsList expr)
                (self (n / 2, newContext, retType))
          | NProd tyList ->
              map tuple
                (flatten_l
                   (List.map
                      (fun t ->
                        self (n / max (List.length tyList) 1, context, t))
                      tyList))
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
          let fun_gen =
            list_size (int_bound n) (TypeGen.gen n) >>= fun l ->
            let l = List.map (fun t -> (Var.fresh (), t)) l in
            let newContext = l @ context in
            map2
              (fun args expr -> App (Fun (l, expr), args))
              (flatten_l
              @@ List.map
                   (fun (_, t) -> self (n / max 2 (List.length l), context, t))
                   l)
              (self (n / max 2 (List.length l), newContext, targetTy))
          in
          let ncase_gen =
            list_size (int_bound n) (TypeGen.gen n) >>= fun tyList ->
            let l = List.map (fun t -> (Var.fresh (), t)) tyList in
            let newContext = l @ context in
            map2
              (fun tuple expr -> NCase (tuple, l, expr))
              (self (n / max 2 (List.length l), context, NProd tyList))
              (self (n / max 2 (List.length l), newContext, targetTy))
          in
          let gen_list = [ let_gen; fun_gen; ncase_gen ] in
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
      return (subst x t expr1 expr2)
      <+> (shrink expr1 >|= fun expr -> clet x t expr expr2)
      <+> (shrink expr2 >|= fun expr -> clet x t expr1 expr)
  | Fun (vars, expr) -> shrink expr >|= fun expr -> func vars expr
  | App (expr, exprs) ->
      (match expr with
      | Fun (varList, expr) ->
          if CCList.compare_lengths varList exprs = 0 then
            return (simSubst (List.combine varList exprs) expr)
          else empty
      | _ -> empty)
      <+> (shrink expr >|= fun expr -> app expr exprs)
      <+> (QCheck.Shrink.list_elems shrink exprs >|= fun exprs -> app expr exprs)
  | Tuple exprs -> QCheck.Shrink.list_elems shrink exprs >|= tuple
  | NCase (expr1, vars, expr2) ->
      (match expr1 with
      | Tuple l ->
          if CCList.compare_lengths l vars = 0 then
            return (simSubst (List.combine vars l) expr2)
          else empty
      | _ -> empty)
      <+> (shrink expr1 >|= fun expr -> ncase expr vars expr2)
      <+> (shrink expr2 >|= fun expr -> ncase expr1 vars expr)
