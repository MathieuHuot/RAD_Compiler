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
    | Target.Apply1 (op, Const c) ->
        (* op c *)
        Success (Const (Operators.interpretOp1 op c))
    | Target.Apply2 (op, Const a, Const b) ->
        (* a op b *)
        Success (Const (Operators.interpretOp2 op a b))
    | expr -> Failure expr

  let simpleAlgebraicSimplifications : Target.t -> Target.t output = function
    | Target.Apply2 (Plus, expr1, Target.Apply1 (Minus, expr2)) ->
        (* expr1 + (- expr2) -> expr1 - expr2 *)
        Success (Target.Apply2 (Minus, expr1, expr2))
    | Target.Apply2 (Times, Target.Const -1., expr)
    | Target.Apply2 (Times, expr, Target.Const -1.) ->
        (* (-1) * expr -> - expr *)
        (* expr * (-1) -> - expr *)
        Success (Target.Apply1 (Minus, expr))
    | Target.Apply1 (Minus, Target.Apply1 (Minus, expr)) ->
        (* - (- expr) -> expr *)
        Success expr
    | Target.Apply2 (Minus, expr1, Target.Apply1 (Minus, expr2)) ->
        (* expr1 - (- expr2) -> expr1 + expr2 *)
        Success (Target.Apply2 (Plus, expr1, expr2))
    | Target.Let (x, ty, Target.Const c, e) ->
        (* TODO: move this to inlining optimisation *)
        Success (Target.subst x ty (Target.Const c) e)
    | Target.Apply2 (Times, Target.Apply1 (Minus, expr1), expr2)
    | Target.Apply2 (Times, expr1, Target.Apply1 (Minus, expr2)) ->
        (* (- expr1) * expr2 -> - (expr1 * expr2) *)
        (* expr1 * (- expr2) -> - (expr1 * expr2) *)
        Success (Target.Apply1 (Minus, Target.Apply2 (Times, expr1, expr2)))
    | Target.Apply1 (Power n, Target.Apply1 (Minus, expr)) ->
        (* (- expr)^n -> (-1)^n expr *)
        if n mod 2 = 0 then Success (Target.Apply1 (Power n, expr))
        else Success (Target.Apply1 (Minus, Target.Apply1 (Power n, expr)))
    | Target.Apply1 (Power n, Target.Apply1 (Exp, expr)) ->
        (* (e^expr)^n -> e^(n * expr) *)
        Success
          (Target.Apply1
             (Exp, Target.Apply2 (Times, Target.Const (float_of_int n), expr)))
    | Target.Apply2 (Times, expr, Target.Const 1.)
    | Target.Apply2 (Times, Target.Const 1., expr) ->
        (* exrp * 1 -> expr *)
        (* 1 * exrp -> expr *)
        Success expr
    | Target.Apply2
        (Times, Target.Apply1 (Exp, expr1), Target.Apply1 (Exp, expr2)) ->
          (* e^expr1 * e^expr2 -> e^(expr1 + expr2) *)
        Success (Target.Apply1 (Exp, Target.Apply2 (Plus, expr1, expr2)))
    | Target.Apply2 (Plus, Target.Apply1 (Minus, expr1), expr2) ->
        (* (- epxr1) + expr2 -> expr2 - expr1 *)
        Success (Target.Apply2 (Minus, expr2, expr1))
    | expr -> Failure expr
end

module S = struct
  (** Optimisation for the source language *)
end
