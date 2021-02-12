module M = CCMap.Make (struct
  type t = Var.t * Target.Type.t

  let compare =
    CCPair.compare (CCPair.compare CCString.compare CCInt.compare) compare
end)

let default_strategy n expr =
  if n = 1 then true
  else
    match expr with
    | Target.Var _ -> true
    | Const _ -> true
    | Tuple _ -> true
    | Array _ -> true
    | Fun _ -> true
    | _ -> false

let inline_expansion ?(strategy = default_strategy) (expr : Target.t) : Target.t
    =
  let rec aux m expr =
    match expr with
    | Target.Var (v, t) ->
        ( M.update (v, t) (function None -> None | Some x -> Some (x + 1)) m,
          expr )
    | Target.Const _ -> (m, expr)
    | Target.Apply1 (op, expr1) ->
        let m, expr1 = aux m expr1 in
        (m, Target.Apply1 (op, expr1))
    | Target.Apply2 (op, expr1, expr2) ->
        let m, expr1 = aux m expr1 in
        let m, expr2 = aux m expr2 in
        (m, Target.Apply2 (op, expr1, expr2))
    | Target.Let (x, t, expr1, expr2) ->
        let m1, expr1 = aux (M.map (fun _ -> 0) m) expr1 in
        let m, expr2 = aux (M.add (x, t) 0 m) expr2 in
        let m, expr =
          match M.find (x, t) m with
          | 0 -> (m, expr2)
          | n ->
              if strategy n expr1 then
                ( M.union (fun _ v v1 -> Some (v + (n * v1))) m m1,
                  Target.subst x t expr1 expr2 )
              else
                ( M.union (fun _ v v1 -> Some (v + v1)) m m1,
                  Target.Let (x, t, expr1, expr2) )
        in
        (M.remove (x, t) m, expr)
    | Target.Fun (varList, expr) ->
        let m, expr = aux m expr in
        (m, Target.Fun (varList, expr))
    | Target.App (Target.Fun (varList, expr1), exprList) ->
        let exprMapList =
          let new_m = M.map (fun _ -> 0) m in
          CCList.map2
            (fun expr m ->
              let m, expr = aux m expr in
              (m, expr))
            exprList
            (List.map (fun _ -> new_m) exprList)
        in
        let m, expr1 =
          aux (List.fold_left (fun m x -> M.add x 0 m) m varList) expr1
        in
        let m, expr =
          let m, expr1, varList, exprList =
            CCList.fold_right2
              (fun (x, t) (m1, expr) (m, expr1, varList, exprList) ->
                match M.find (x, t) m with
                | 0 -> (m, expr1, varList, exprList)
                | n ->
                    if strategy n expr1 then
                      ( M.union (fun _ v v1 -> Some (v + (n * v1))) m m1,
                        Target.subst x t expr expr1,
                        varList,
                        exprList )
                    else
                      ( M.union (fun _ v v1 -> Some (v + v1)) m m1,
                        expr1,
                        (x, t) :: varList,
                        expr :: exprList ))
              varList exprMapList (m, expr1, [], [])
          in
          ( m,
            if varList = [] then expr1
            else Target.App (Target.Fun (varList, expr1), exprList) )
        in
        (CCList.fold_left (fun m x -> M.remove x m) m varList, expr)
    | Target.App (expr, exprList) ->
        let m, exprList =
          CCList.fold_right
            (fun expr (m, l) ->
              let m, expr = aux m expr in
              (m, expr :: l))
            exprList (m, [])
        in
        let m, expr = aux m expr in
        (m, Target.App (expr, exprList))
    | Target.Tuple exprList ->
        let m, exprList =
          CCList.fold_right
            (fun expr (m, l) ->
              let m, expr = aux m expr in
              (m, expr :: l))
            exprList (m, [])
        in
        (m, Target.Tuple exprList)
    | Target.NCase (Target.Tuple exprList, varList, expr1) ->
        let exprMapList =
          let new_m = M.map (fun _ -> 0) m in
          CCList.map2
            (fun expr m ->
              let m, expr = aux m expr in
              (m, expr))
            exprList
            (List.map (fun _ -> new_m) exprList)
        in
        let m, expr1 =
          aux (List.fold_left (fun m x -> M.add x 0 m) m varList) expr1
        in
        let m, expr =
          let m, expr1, varList, exprList =
            CCList.fold_right2
              (fun (x, t) (m1, expr) (m, expr1, varList, exprList) ->
                match M.find (x, t) m with
                | 0 -> (m, expr1, varList, exprList)
                | n ->
                    if strategy n expr1 then
                      ( M.union (fun _ v v1 -> Some (v + (n * v1))) m m1,
                        Target.subst x t expr expr1,
                        varList,
                        exprList )
                    else
                      ( M.union (fun _ v v1 -> Some (v + v1)) m m1,
                        expr1,
                        (x, t) :: varList,
                        expr :: exprList ))
              varList exprMapList (m, expr1, [], [])
          in
          ( m,
            if varList = [] then expr1
            else Target.App (Target.Fun (varList, expr1), exprList) )
        in
        (CCList.fold_left (fun m x -> M.remove x m) m varList, expr)
    | Target.NCase (expr1, varList, expr2) ->
        let m, expr1 = aux m expr1 in
        let m, expr2 = aux m expr2 in
        (m, Target.NCase (expr1, varList, expr2))
    | Target.Map (x, t, expr1, expr2) ->
        let m, expr2 = aux m expr2 in
        let m, expr1 = aux m expr1 in
        (m, Target.Map (x, t, expr1, expr2))
    | Target.Map2 (x, tx, y, ty, expr1, expr2, expr3) ->
        let m, expr3 = aux m expr3 in
        let m, expr2 = aux m expr2 in
        let m, expr1 = aux m expr1 in
        (m, Target.Map2 (x, tx, y, ty, expr1, expr2, expr3))
    | Target.Map3 (x, tx, y, ty, z, tz, expr1, expr2, expr3, expr4) ->
        let m, expr4 = aux m expr4 in
        let m, expr3 = aux m expr3 in
        let m, expr2 = aux m expr2 in
        let m, expr1 = aux m expr1 in
        (m, Target.Map3 (x, tx, y, ty, z, tz, expr1, expr2, expr3, expr4))
    | Target.Reduce (x, tx, y, ty, expr1, expr2, expr3) ->
        let m, expr3 = aux m expr3 in
        let m, expr2 = aux m expr2 in
        let m, expr1 = aux m expr1 in
        (m, Target.Reduce (x, tx, y, ty, expr1, expr2, expr3))
    | Target.Scan (x, tx, y, ty, expr1, expr2, expr3) ->
        let m, expr3 = aux m expr3 in
        let m, expr2 = aux m expr2 in
        let m, expr1 = aux m expr1 in
        (m, Target.Scan (x, tx, y, ty, expr1, expr2, expr3))
    | Target.Zip (expr1, expr2) ->
        let m, expr2 = aux m expr2 in
        let m, expr1 = aux m expr1 in
        (m, Target.Zip (expr1, expr2))
    | Target.Unzip expr1 ->
        let m, expr1 = aux m expr1 in
        (m, Target.Unzip expr1)
    | Target.Zip3 (expr1, expr2, expr3) ->
        let m, expr3 = aux m expr3 in
        let m, expr2 = aux m expr2 in
        let m, expr1 = aux m expr1 in
        (m, Target.Zip3 (expr1, expr2, expr3))
    | Target.Unzip3 expr1 ->
        let m, expr1 = aux m expr1 in
        (m, Target.Unzip3 expr1)
    | Target.Fold (x, tx, y, ty, expr1, expr2, expr3) ->
        let m, expr3 = aux m expr3 in
        let m, expr2 = aux m expr2 in
        let m, expr1 = aux m expr1 in
        (m, Target.Fold (x, tx, y, ty, expr1, expr2, expr3))
    | Target.Array exprList ->
        let m, exprList =
          CCList.fold_right
            (fun expr (m, l) ->
              let m, expr = aux m expr in
              (m, expr :: l))
            exprList (m, [])
        in
        (m, Target.Array exprList)
  in
  snd (aux M.empty expr)
