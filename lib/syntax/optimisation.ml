(** Optimisation for all languages
    Thoses optimisations functions need to be applied with the Traverse module of each language
    Example:
    {[
      # module TR = Target.Traverse(Strategy.Repeat);;
      # TR.map T.constantPropagation
    ]}
*)

open Rewriter

module T = struct
  (** Optimisation for the target language *)

  let constantPropagation : Target.t -> Target.t output = function
    | Apply1 (op, Const c) ->
        (* op c *)
        Success (Const (Operators.interpretOp1 op c))
    | Apply2 (op, Const a, Const b) ->
        (* a op b *)
        Success (Const (Operators.interpretOp2 op a b))
    | expr -> Failure expr

  let simpleAlgebraicSimplifications : Target.t -> Target.t output = function
    | Apply2 (Plus, expr1, Apply1 (Minus, expr2)) ->
        (* expr1 + (- expr2) -> expr1 - expr2 *)
        Success (Apply2 (Minus, expr1, expr2))
    | Apply2 (Times, Const -1., expr) | Apply2 (Times, expr, Const -1.) ->
        (* (-1) * expr -> - expr *)
        (* expr * (-1) -> - expr *)
        Success (Apply1 (Minus, expr))
    | Apply1 (Minus, Apply1 (Minus, expr)) ->
        (* - (- expr) -> expr *)
        Success expr
    | Apply2 (Minus, expr1, Apply1 (Minus, expr2)) ->
        (* expr1 - (- expr2) -> expr1 + expr2 *)
        Success (Apply2 (Plus, expr1, expr2))
    | Let (x, ty, Const c, e) ->
        (* TODO: move this to inlining optimisation and generalise this to value inlining *)
        Success (Target.subst x ty (Const c) e)
    | Apply2 (Times, Apply1 (Minus, expr1), expr2)
    | Apply2 (Times, expr1, Apply1 (Minus, expr2)) ->
        (* (- expr1) * expr2 -> - (expr1 * expr2) *)
        (* expr1 * (- expr2) -> - (expr1 * expr2) *)
        Success (Apply1 (Minus, Apply2 (Times, expr1, expr2)))
    | Apply1 (Power n, Apply1 (Minus, expr)) ->
        (* (- expr)^n -> (-1)^n expr *)
        if n mod 2 = 0 then Success (Apply1 (Power n, expr))
        else Success (Apply1 (Minus, Apply1 (Power n, expr)))
    | Apply1 (Power n, Apply1 (Exp, expr)) ->
        (* (e^expr)^n -> e^(n * expr) *)
        Success (Apply1 (Exp, Apply2 (Times, Const (float_of_int n), expr)))
    | Apply2 (Times, expr, Const 1.) | Apply2 (Times, Const 1., expr) ->
        (* expr * 1 -> expr *)
        (* 1 * expr -> expr *)
        Success expr
    | Apply2 (Times, Apply1 (Exp, expr1), Apply1 (Exp, expr2)) ->
        (* e^expr1 * e^expr2 -> e^(expr1 + expr2) *)
        Success (Apply1 (Exp, Apply2 (Plus, expr1, expr2)))
    | Apply2 (Plus, Apply1 (Minus, expr1), expr2) ->
        (* (- expr1) + expr2 -> expr2 - expr1 *)
        Success (Apply2 (Minus, expr2, expr1))
    | expr -> Failure expr

  let zeroSimplification : Target.t -> Target.t output = function
    | Apply2 (Times, _, Const 0.) | Apply2 (Times, Const 0., _) ->
        (* e * 0 -> 0 *)
        (* 0 * e -> 0 *)
        Success (Const 0.)
    | Apply2 (Minus, expr, Const 0.)
    | Apply2 (Plus, expr, Const 0.)
    | Apply2 (Plus, Const 0., expr) ->
        (* expr - 0 -> expr*)
        (* expr + 0 -> expr*)
        (* 0 + expr -> expr*)
        Success expr
    | Apply2 (Minus, Const 0., expr) ->
        (* 0 - expr -> - expr *)
        Success (Apply1 (Minus, expr))
    | expr -> Failure expr

  let trigoSimplification : Target.t -> Target.t output = function
    | Apply1 (Sin, Apply1 (Minus, expr)) ->
        (* sin(-x) -> - sin (x) *)
        Success (Apply1 (Minus, Apply1 (Sin, expr)))
    | Apply1 (Cos, Apply1 (Minus, expr)) ->
        (* cos (-x) -> cos (x) *)
        Success (Apply1 (Cos, expr))
    | ( Apply2
          ( Plus,
            Apply1 (Power 2, Apply1 (Sin, expr1)),
            Apply1 (Power 2, Apply1 (Cos, expr2)) )
      | Apply2
          ( Plus,
            Apply1 (Power 2, Apply1 (Cos, expr1)),
            Apply1 (Power 2, Apply1 (Sin, expr2)) ) ) as expr ->
        if Target.equal expr1 expr2 then
          (* sin (x)² + cos (x)² -> 1 *)
          Success (Const 1.)
        else Failure expr
    | expr -> Failure expr

  let realFactorisation : Target.t -> Target.t output = function
    | Apply2 (Plus, Apply2 (Times, expr1, expr2), Apply2 (Times, expr3, expr4))
      as expr ->
        if expr1 = expr3 then
          (* e1 * e2 + e1 * e4 -> e1 * (e2 + e4) *)
          Success (Apply2 (Times, expr1, Apply2 (Plus, expr2, expr4)))
        else if expr2 = expr4 then
          (* e1 * e2 + e3 * e2 -> e2 * (e1 + e3) *)
          Success (Apply2 (Times, expr2, Apply2 (Plus, expr1, expr3)))
        else if expr1 = expr4 then
          (* e1 * e2 + e3 * e1 -> e1 * (e2 + e3) *)
          Success (Apply2 (Times, expr1, Apply2 (Plus, expr2, expr3)))
        else if expr2 = expr3 then
          (* e1 * e2 + e2 * e4 -> e2 * (e1 + e4) *)
          Success (Apply2 (Times, expr2, Apply2 (Plus, expr1, expr4)))
        else Failure expr
    | Apply2 (Plus, expr1, expr2) when Target.equal expr1 expr2 ->
        (* e1 + e1 -> 2 * e1 *)
        Success (Apply2 (Times, Const 2., expr1))
    | expr -> Failure expr

  let letCommutativity : Target.t -> Target.t output = function
    | Let (x, ty1, Let (y, ty2, expr1, expr2), expr3) ->
        (* let x:ty1 =
               let y:ty2 = expr1 in
               expr2
           in
           expr3 ->
           let y:ty2 = expr1 in
           let x:ty1 = expr2 in
           expr3 *)
        Success (Let (y, ty2, expr1, Let (x, ty1, expr2, expr3)))
    | NCase (NCase (expr1, varList1, expr2), varList2, expr3) ->
        Success (NCase (expr1, varList1, NCase (expr2, varList2, expr3)))
    | NCase (Let (x1, ty1, expr1, expr2), varList, expr3) ->
        Success (Let (x1, ty1, expr1, NCase (expr2, varList, expr3)))
    | Let (x, ty, NCase (expr1, varList, expr2), expr3) ->
        Success (NCase (expr1, varList, Let (x, ty, expr2, expr3)))
    | expr -> Failure expr

  (* TODO turn this into a inlinining optimisation *)
  let forwardSubstitution : Target.t -> Target.t output = function
    | Let (x, ty, (Const _ as expr), e) | Let (x, _, (Var (_, ty) as expr), e)
      ->
        Success (Target.subst x ty expr e)
    | NCase (Tuple exprList, varList, expr) as e ->
        if List.compare_lengths exprList varList <> 0 then
          failwith "ForwardSubstitution: tuple wrong number of arguments"
        else
          let context, rest =
            List.partition
              (fun (_, x) ->
                match x with
                | Target.Var _ | Target.Const _ -> true
                | _ -> false)
              (List.combine varList exprList)
          in
          if rest = [] then
            Success (Target.simSubst (List.combine varList exprList) expr)
          else if context <> [] then
            let varList1, exprList1 = List.split rest in
            Success
              (NCase (Tuple exprList1, varList1, Target.simSubst context expr))
          else Failure e
    | expr -> Failure expr

  (* TODO: unsafe, does not terminate
   * Use NCase to make convergent
   * [@ocaml.alert unsafe "Does not terminate"]*)

  (* MH: I think we keep the first one which is a simple case of subexpression elimination, and remove the second one *)
  let letSimplification : Target.t -> Target.t output = function
    (* let x=e1 in let y=e1 in e2 -> let x=e0 in let y=x in e2 *)
    | Let (x1, ty1, e0, Let (x2, ty2, e1, e2)) when Target.equal e0 e1 ->
        Success (Let (x1, ty1, e0, Let (x2, ty2, Var (x1, ty1), e2)))
    (* let x=e0 in let y=e1 in e2 -> let y=e1 in let x=e0 in e2 (x not a FV in e1) *)
    | Let (x1, ty1, e0, Let (x2, ty2, e1, e2))
      when not (Target.VarSet.mem x1 (Target.freeVar e1)) ->
        Success (Let (x2, ty2, e1, Let (x1, ty1, e0, e2)))
    | expr -> Failure expr

  let lambdaRemoval : Target.t -> Target.t output = function
    (* replaces inlined lambdas in (fun x1...xn.e)[e1...en] to
        let x1 = e1 in let x2 = e2 in ... in let xn = en in e
        for later optimisations like forward substitution *)
    | App (Fun (varList, expr), exprList) ->
        if not (List.length varList = List.length exprList) then
          failwith
            "LambdaRemoval: Function applied to wrong number of arguments"
        else Success (NCase (Tuple exprList, varList, expr))
    (* CBN evaluates a variable which has a function type *)
    (* TODO: why doing some sort of lazy evaluation for function ? *)
    (*MH: it's used crefully after rad, but integrated into the more efficient rad2. should be removed eventually *)
    | Let (x, ty, expr1, expr2) when Target.Type.isArrow ty ->
        Success (Target.subst x ty expr1 expr2)
    | NCase (Tuple exprList, varList, expr) as e ->
        if List.exists (fun (_, ty) -> Target.Type.isArrow ty) varList then
          let list = List.combine varList exprList in
          let arrowList, nonArrowList =
            List.partition (fun ((_, ty), _) -> Target.Type.isArrow ty) list
          in
          let var2, expr2 = List.split nonArrowList in
          Success (NCase (Tuple expr2, var2, Target.simSubst arrowList expr))
        else Failure e
    | expr -> Failure expr

  (* TODO: This is just a special case of inlining *)
  let deadVarElim : Target.t -> Target.t output =
   fun expr ->
    (* TODO: change the use of unusedVar *)
    let unusedVar = Target.listUnusedVar expr in
    match expr with
    | Let (x, ty, _, expr) when List.mem (x, ty) unusedVar -> Success expr
    | NCase (_, varList, expr)
      when List.for_all (fun y -> List.mem y unusedVar) varList ->
        Success expr
    | NCase (Tuple exprList, varList, expr) ->
        let list = List.combine exprList varList in
        (* remove each expr bound to an unused var *)
        let b = ref false in
        let filteredList =
          List.filter
            (fun (_, y) ->
              if not (List.mem y unusedVar) then true
              else (
                b := true;
                false))
            list
        in
        let filtExpr, filtVar = List.split filteredList in
        if !b then Success (NCase (Tuple filtExpr, filtVar, expr))
        else Failure (NCase (Tuple filtExpr, filtVar, expr))
    | expr -> Failure expr

    (* TODO: see if useful *)
    (* could also remove Let altogether and just keep NCase *)
  let oneCaseRemoval : Target.t -> Target.t output = function
    | NCase (Tuple [ expr1 ], [ (x, ty) ], expr2) ->
        Success (Let (x, ty, expr1, expr2))
    | expr -> Failure expr

  let loop_fusion : Target.t -> Target.t output = function
  | Map (y, ty2, expr2, Map (x, ty1, expr1, expr3)) -> Success (Map(x, ty1, Let(y, ty2, expr2, expr1), expr3))
  | Map(z, ty3, expr4, Map2(x, ty1, y, ty2, expr1, expr2, expr3)) -> Success (Map2(x, ty1, y, ty2, Let(z, ty3, expr1, expr4), expr2, expr3))
  | Map(y, ty, expr5, Map3(x1, ty1, x2, ty2, x3, ty3, expr1, expr2, expr3, expr4)) -> Success (Map3(x1, ty1, x2, ty2, x3, ty3, Let(y, ty, expr1, expr5), expr2, expr3, expr4))
  | Map2(x1, ty1, x2, ty2, expr1, Map(z1, ty11, expr11, expr12), Map(z2, ty22, expr21, expr22)) -> 
    Success (Map2(z1, ty11, z2, ty22, NCase(Tuple([expr11; expr21]), [(x1, ty1); (x2, ty2)], expr1) , expr12, expr22))
  | Map3(x1, ty1, x2, ty2, x3, ty3, expr1, Map(z1, ty11, expr11, expr12), Map(z2, ty22, expr21, expr22), Map(z3, ty33, expr31, expr32)) -> 
      Success (Map3(z1, ty11, z2, ty22, z3, ty33, NCase(Tuple([expr11; expr21; expr31]), [(x1, ty1); (x2, ty2); (x3, ty3)], expr1) , expr12, expr22, expr32)) 
  | Fold(x, ty1, y, ty2, expr1, expr2, Map(z, ty3, expr3, expr4)) -> Success (Fold(x, ty1, z, ty3, Let(y, ty2, expr3, expr1), expr2, expr4))
  | Reduce(x, ty1, y, ty2, expr1, expr2, Map(z, ty3, expr3, expr4)) -> Success (Reduce(x, ty1, z, ty3, Let(y, ty2, expr3, expr1), expr2, expr4))
  | Scan(x, ty1, y, ty2, expr1, expr2, Map(z, ty3, expr3, expr4)) ->  Success (Scan(x, ty1, z, ty3, Let(y, ty2, expr3, expr1), expr2, expr4))
  | Map(x, NProd([ty1; ty2]), expr1, Zip(expr2, expr3)) -> let y1, y2 = Var.fresh(), Var.fresh() in
    Success (Map2(y1, ty1, y2, ty2, Target.subst x (NProd([ty1; ty2])) (Tuple([Var(y1, ty1); Var(y2, ty2)])) expr1, expr2, expr3))
  | Map(x, NProd([ty1; ty2; ty3]), expr1, Zip3(expr2, expr3, expr4)) -> let y1, y2, y3 = Var.fresh(), Var.fresh(), Var.fresh() in
    Success (Map3(y1, ty1, y2, ty2, y3, ty3, Target.subst x (NProd([ty1; ty2; ty3])) (Tuple([Var(y1, ty1); Var(y2, ty2); Var(y3, ty3)])) expr1, expr2, expr3, expr4))
  | expr -> Failure expr

  let rec truncate lis n = match n with
  | 0 -> lis
  | n -> begin match lis with 
        | [] -> []
        | e::lis -> e::(truncate lis (n-1))
        end  

  (* let loop_removal : Target.t -> Target.t output = function
  | Get(n, Map(x, ty, expr1, expr2)) -> Success(Let(x, ty, Get(n, expr2), expr1))
  | Get(n, Array(exprList)) -> Success (List.nth exprList n)
  | Get(n, Map2(x, ty1, y, ty2, expr1, expr2, expr3)) ->  Success (NCase(Get(n, Zip(expr2, expr3)), [(x, ty1); (y, ty2)], expr1))
  | Get(n, Map3(x, ty1, y, ty2, z, ty3, expr1, expr2, expr3, expr4)) ->  Success (NCase(Get(n, Zip3(expr2, expr3, expr4)), [(x, ty1); (y, ty2); (z, ty3)], expr1))
  | Get(n, Scan(x, ty1, y, ty2, expr1, expr2, Array(exprList))) -> Success (Fold(x, ty1, y, ty2, expr1, expr2, Array(truncate exprList n)))
  | Get(n, Fold(x, ty1, y, ty2, expr1, expr2, Array(exprList))) -> Success (Fold(x, ty1, y, ty2, expr1, expr2, Array(truncate exprList n)))
  | Get(n, Reduce(x, ty1, y, ty2, expr1, expr2, Array(exprList))) -> Success (Reduce(x, ty1, y, ty2, expr1, expr2, Array(truncate exprList n)))
  | Get(n, Zip(expr1, expr2)) -> Success (Tuple([Get(n, expr1); Get(n, expr2)]))
  | Get(n, Zip3(expr1, expr2, expr3)) -> Success (Tuple([Get(n, expr1); Get(n, expr2);  Get(n, expr3)]))
  | NCase(Unzip(expr), [(x1, _); (y1, _)], Tuple([Get(n, Var(x2, _)); Get(m, Var(y2, _))])) 
    when Var.equal x1 x2 && Var.equal y1 y2 && n=m -> Success (Get(n, expr))
  | NCase(Unzip3(expr), [(x1, _); (y1, _); (z1, _)], Tuple([Get(n, Var(x2, _)); Get(m, Var(y2, _)); Get(p, Var(z2, _))])) 
    when Var.equal x1 x2 && Var.equal y1 y2 && Var.equal z1 z2 && n=m && m=p -> Success (Get(n, expr)) 
  | expr -> Failure expr *)

  let array_simplification : Target.t -> Target.t output = function
  | Unzip(Zip(expr1, expr2)) -> Success (Tuple([expr1; expr2]))
  | Unzip3(Zip3(expr1, expr2, expr3)) -> Success (Tuple([expr1; expr2; expr3]))
  | expr -> Failure expr

  let algebraicSimplifications : Target.t -> Target.t output = function
  | Apply1(Power(2), Apply1(Sqrt, expr)) -> Success expr
  | Apply1(Cos, Apply1(Acos, expr)) -> Success expr 
  | Apply1(Sin, Apply1(Asin, expr)) -> Success expr
  | Apply1(Log, Apply1(Exp, expr)) -> Success expr
  | Apply1(Exp, Apply1(Log, expr)) -> Success expr
  | Apply2(Div, Apply1(Sin, expr1), Apply1(Cos, expr2)) 
    when Target.equal expr1 expr2 -> Success (Apply1(Tan, expr1))
  | Apply2(Div, Apply1(Sinh, expr1), Apply1(Cosh, expr2)) 
    when Target.equal expr1 expr2 -> Success (Apply1(Tanh, expr1))
  | Apply1(Log, Apply2(Div, expr1, expr2)) -> Success (Apply2(Minus, Apply1(Log, expr1), Apply1(Log, expr2)))
  | Apply1(Log10, Apply2(Div, expr1, expr2)) -> Success (Apply2(Minus, Apply1(Log10, expr1), Apply1(Log10, expr2)))
  | Apply1(Log, Apply2(Times, expr1, expr2)) -> Success (Apply2(Plus, Apply1(Log, expr1), Apply1(Log, expr2)))
  | Apply1(Log10, Apply2(Times, expr1, expr2)) -> Success (Apply2(Plus, Apply1(Log10, expr1), Apply1(Log10, expr2)))
  | Apply1(Log, Apply1(Sqrt, expr)) -> Success (Apply2(Times, Const 0.5, Apply1(Log, expr)))
  | Apply1(Log, Apply1(Power(n), expr)) -> Success (Apply2(Times, Const (float_of_int n), Apply1(Log, expr)))
  | Apply1(Log10, Apply1(Sqrt, expr)) -> Success (Apply2(Times, Const 0.5, Apply1(Log10, expr)))
  | Apply1(Log10, Apply1(Power(n), expr)) -> Success (Apply2(Times, Const (float_of_int n), Apply1(Log10, expr)))
  | Apply1(Power(n), Apply1(Power(m), expr)) -> Success (Apply1(Power(n*m), expr))
  | Apply2(Times, expr1, expr2) when Target.equal expr1 expr2 -> Success (Apply1(Power(2), expr1))
  | Apply1(Power(1), expr) -> Success expr
  | Apply1(Power(0), _expr) -> Success (Const 1.)
  | Apply2(Times, Apply1(Power(n1), expr1), Apply1(Power(n2), expr2)) 
    when Target.equal expr1 expr2 -> Success ( Apply1(Power(n1+n2), expr2))
  | expr -> Failure expr

  let exact_opti_list =
    [
      (lambdaRemoval, "LR");
      (forwardSubstitution, "FS");
      (letCommutativity, "LC");
      (realFactorisation, "RF");
      (trigoSimplification, "TS");
      (zeroSimplification, "ZS");
      (simpleAlgebraicSimplifications, "SAS");
      (constantPropagation, "CP");
      (deadVarElim, "DVE");
    ]

  let opti_list =
    (letSimplification, "LS") :: exact_opti_list

  let fullOpti expr =
    let module RT = Target.Traverse (Strategy.Repeat) in
    let open Rewriter in
    RT.map
      (constantPropagation >> simpleAlgebraicSimplifications
     >> zeroSimplification >> trigoSimplification >> realFactorisation
     >> letCommutativity >> lambdaRemoval >> deadVarElim)
      expr
    |> get
end

module S = struct
  (** Optimisation for the source language *)
end
