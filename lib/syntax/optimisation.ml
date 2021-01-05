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
        (* TODO: move this to inlining optimisation *)
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
        (* exrp * 1 -> expr *)
        (* 1 * exrp -> expr *)
        Success expr
    | Apply2 (Times, Apply1 (Exp, expr1), Apply1 (Exp, expr2)) ->
        (* e^expr1 * e^expr2 -> e^(expr1 + expr2) *)
        Success (Apply1 (Exp, Apply2 (Plus, expr1, expr2)))
    | Apply2 (Plus, Apply1 (Minus, expr1), expr2) ->
        (* (- epxr1) + expr2 -> expr2 - expr1 *)
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
          (* e1 * e2 + e3 * e2 -> (e1 + e3) * e2 *)
          Success (Apply2 (Times, Apply2 (Plus, expr1, expr3), expr2))
        else Failure expr
          (* TODO: add more cases if operators are commutative *)
    | Apply2 (Plus, expr1, expr2) when Target.equal expr1 expr2 ->
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
        (* TODO: with this transformation will loose the information that y does not
           appear in expr3 *)
        Success (Let (y, ty2, expr1, Let (x, ty1, expr2, expr3)))
    | NCase (NCase (expr1, varList1, expr2), varList2, expr3) ->
        Success (NCase (expr1, varList1, NCase (expr2, varList2, expr3)))
    | NCase (Let (x1, ty1, expr1, expr2), varList, expr3) ->
        Success (Let (x1, ty1, expr1, NCase (expr2, varList, expr3)))
    | Let (x, ty, NCase (expr1, varList, expr2), expr3) ->
        Success (NCase (expr1, varList, Let (x, ty, expr2, expr3)))
    | expr -> Failure expr
end

module S = struct
  (** Optimisation for the source language *)
end
