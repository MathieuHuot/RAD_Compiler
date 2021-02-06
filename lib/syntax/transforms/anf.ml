(* Module for A-Normal Form *)
(* Also module for a weak-version of ANF: only assumes that operators are only applied to variables *)
open Syntax

module type Anf = sig
type ast
val isInWeakAnf: ast -> bool
val isInAnf: ast -> bool
val weakAnf: ast -> ast
val anf: ast -> ast
end

module SourceAnf: Anf with type ast = Syntax.Source.t = struct
open Syntax.Source
type ast = t

let isVar (expr : t) = match expr with
  | Var _ -> true
  | _     -> false

let isImmediate expr = match expr with
  | Const _                  -> true
  | Var _                    -> true
  | Apply1(_,expr1)          -> isVar expr1 
  | Apply2(_,expr1,expr2)    -> isVar expr1 && isVar expr2
  | _                        -> false

let rec isInAnf expr = match expr with
  | Let(_,_,expr1,expr2)  -> isImmediate expr1 && isInAnf expr2
  | _                     -> true

let rec isInWeakAnf expr = match expr with
  | Let(_,_,expr1,expr2)        -> isInWeakAnf expr1 && isInWeakAnf expr2
  | Apply1(_,_) | Apply2(_,_,_) -> isImmediate expr 
  | _                           -> true

(*TODO: finish. I think it needs the other kind of map as I want to recursively go into the term I just changed. 
          Unless again we use repeat to normalize. But need to use the map of strategies and not the basic map. *)
  let weakAnf expr = map (fun expr ->
    match expr with
    | Apply1(op, expr1)       -> if isImmediate expr then expr else 
        let n = Syntax.Var.fresh() in
        let ty = Type.Real in
        let newVar = Var(n,ty) in
        Let(n, ty, expr1, Apply1(op, newVar))
    | Apply2(op, expr1, expr2) -> if isImmediate expr then expr else
        let n = Syntax.Var.fresh() in
        let ty1 = Type.Real in
        let newVar1 = Var(n,ty1) in 
        let m = Syntax.Var.fresh() in 
        let ty2 = Type.Real in
        let newVar2 = Var(m,ty2) in 
        Let(n, ty1, expr1, Let(m, ty2, expr2, Apply2(op, newVar1, newVar2)))
    | expr -> expr) expr

(*TODO: same as above *)
let letCommutativity expr = map (fun expr ->
  match expr with
  | Let(x,ty1,Let(y,ty2,expr1,expr2),expr3)   -> Let(y,ty2, expr1,Let(x,ty1, expr2, expr3))
  | expr                                         -> expr) expr

let rec letNormalisation expr = 
  let expr2 = letCommutativity expr in 
  if equal expr expr2 then expr else
  letNormalisation expr2

let anf expr = 
  let expr1 = weakAnf expr in
  letNormalisation expr1
end

module TargetAnf: Anf with type ast = Syntax.Target.t = struct
  open Syntax.Target
  type ast = t

let isVar (expr : t) = match expr with
  | Var _ -> true
  | _     -> false

  (*TODO: this is where some catamorphism to generalise List.exists and List.for_all would be useful.*)
let rec isImmediate expr = match expr with
  | Const _                  -> true
  | Var _                    -> true
  | Apply1(_,expr1)          -> isVar expr1 
  | Apply2(_,expr1,expr2)    -> isVar expr1 && isVar expr2
  | Tuple(exprList)          -> List.for_all isImmediate exprList
  | _                        -> false

let rec isInAnf expr = match expr with
  | Let(_,_,expr1,expr2)        -> isImmediate expr1 && isInAnf expr2
  | NCase(expr1,_,expr2)        -> isImmediate expr1 && isInAnf expr2
  | Apply1(_,_) | Apply2(_,_,_) -> isImmediate expr  
  | Fun(_,expr)                 -> isInAnf expr
  | App(_,_)                    -> false
  | Tuple(exprList)             -> List.for_all isInAnf exprList
  | _                           -> true

let rec isInWeakAnf expr = match expr with
  | Let(_,_,expr1,expr2) -> isInWeakAnf expr1 && isInWeakAnf expr2
  | Apply1(_,_)          -> isImmediate expr 
  | Apply2(_,_,_)        -> isImmediate expr
  | Tuple(exprList)      -> List.for_all isInWeakAnf exprList
  | Fun(_,expr)          -> isInWeakAnf expr
  | App(expr,exprList)   -> isInWeakAnf expr && List.for_all isInWeakAnf exprList
  | NCase(expr1,_,expr2) -> isInWeakAnf expr1 && isInWeakAnf expr2
  | _                    -> true

  (*TODO: same as above*)
  let weakAnf expr = map (fun expr ->
    match expr with
    | Apply1(op, expr1)       -> if isImmediate expr then expr else 
        let n = Syntax.Var.fresh() in
        let ty = Type.Real in
        let newVar = Var(n,ty) in
        Let(n, ty, expr1, Apply1(op, newVar))
    | Apply2(op, expr1, expr2) -> if isImmediate expr then expr else
        let n = Syntax.Var.fresh() in
        let ty1 = Type.Real in
        let newVar1 = Var(n,ty1) in 
        let m = Syntax.Var.fresh() in 
        let ty2 = Type.Real in
        let newVar2 = Var(m,ty2) in 
        Let(n, ty1, expr1, Let(m, ty2, expr2, Apply2(op, newVar1, newVar2)))
    | expr -> expr) expr

module RT = Target.Traverse(Strategy.Repeat)
let letCommutativity expr = RT.map Optimisation.T.letCommutativity expr

let anf expr =
  let expr1 = weakAnf expr in
  Rewriter.get (letCommutativity expr1)
end
