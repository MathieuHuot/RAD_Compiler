module type Anf = sig
type ast
val weakAnf: ast -> ast
val anf: ast -> ast
val isInWeakAnf: ast -> bool
val isInAnf: ast -> bool
end

module SourceAnf: Anf with type ast = Syntax.SourceLanguage.sourceSyn = struct
open Syntax.SourceLanguage
type ast = sourceSyn

let isVar (expr : sourceSyn) = match expr with
  | Var _ -> true
  | _     -> false

let isImmediate expr = match expr with
  | Const _                  -> true
  | Var _                    -> true
  | Apply1(_,expr1)          -> isVar expr1 
  | Apply2(_,expr1,expr2)    -> isVar expr1 && isVar expr2
  | _                        -> failwith "wrong expression format"

let rec isInAnf expr = match expr with
  | Let(_,_,expr1,expr2)  -> isImmediate expr1 && isInAnf expr2
  | _                     -> true

let rec isInWeakAnf expr = match expr with
  | Let(_,_,expr1,expr2) -> isInWeakAnf expr1 && isInWeakAnf expr2
  | Apply1(_,_)          -> isImmediate expr 
  | Apply2(_,_,_)        -> isImmediate expr
  | _                    -> true

let rec weakAnf expr = match expr with
  | Const _                -> expr
  | Var _                  -> expr
  | Apply1(op,expr1)       -> if isImmediate expr then expr else 
      let exprAnf = weakAnf expr1 in
      let n = Syntax.Vars.fresh() in
      let ty = Real in
      let newVar = Var(n,ty) in
      Let(n,ty,exprAnf,Apply1(op,newVar))
  | Apply2(op,expr1,expr2) -> if isImmediate expr then expr else
      let expr1Anf = weakAnf expr1 in 
      let expr2Anf = weakAnf expr2 in 
      let n = Syntax.Vars.fresh() in
      let ty1 = Real in
      let newVar1 = Var(n,ty1) in 
      let m = Syntax.Vars.fresh() in 
      let ty2 = Real in
      let newVar2 = Var(m,ty2) in 
      Let(n,ty1,expr1Anf,Let(m,ty2,expr2Anf,Apply2(op,newVar1, newVar2)))
  | Let(x,ty,expr1,expr2)  -> Let(x,ty, weakAnf expr1, weakAnf expr2)

let rec letCommutativity expr = match expr with
  | Let(x,ty1,Let(y,ty2,expr1,expr2),expr3)   -> Let(y,ty2,letCommutativity expr1,Let(x,ty1,letCommutativity expr2,letCommutativity expr3))
  | Let(x,ty,expr1,expr2)                     -> Let(x,ty,letCommutativity expr1,letCommutativity expr2)
  | Apply1(op,expr)                           -> Apply1(op,letCommutativity expr)
  | Apply2(op,expr1,expr2)                    -> Apply2(op,letCommutativity expr1,letCommutativity expr2)
  | _                                         -> expr

let rec letNormalisation expr = 
  let expr2 = letCommutativity expr in 
  if equalTerms expr expr2 then expr else
  letNormalisation expr2

let anf expr = 
  let expr1 = weakAnf expr in
  letNormalisation expr1
end



module TargetAnf: Anf with type ast = Syntax.TargetLanguage.targetSyn = struct
  open Syntax.TargetLanguage
  type ast = targetSyn

let isVar (expr : targetSyn) = match expr with
  | Var _ -> true
  | _     -> false

let isImmediate expr = match expr with
  | Const _                  -> true
  | Var _                    -> true
  | Apply1(_,expr1)          -> isVar expr1 
  | Apply2(_,expr1,expr2)    -> isVar expr1 && isVar expr2
  | _                        -> failwith "wrong expression format"

let rec isInAnf expr = match expr with
  | Let(_,_,expr1,expr2)  -> isImmediate expr1 && isInAnf expr2
  | _                     -> true

let rec isInWeakAnf expr = match expr with
  | Let(_,_,expr1,expr2) -> isInWeakAnf expr1 && isInWeakAnf expr2
  | Apply1(_,_)          -> isImmediate expr 
  | Apply2(_,_,_)        -> isImmediate expr
  | Case(expr1,_,_,_,_,expr2) 
                         -> isInWeakAnf expr1 && isInWeakAnf expr2
  | Pair(expr1,expr2)    -> isInWeakAnf expr1 && isInWeakAnf expr2
  | Tuple(exprList)      -> List.for_all isInWeakAnf exprList
  | Fun(_,expr)          -> isInWeakAnf expr
  | App(expr,exprList)   -> isInWeakAnf expr && List.for_all isInWeakAnf exprList
  | _                    -> true

let rec weakAnf expr = match expr with
  | Const _                -> expr
  | Var _                  -> expr
  | Apply1(op,expr1)       -> if isImmediate expr then expr else 
      let exprAnf = weakAnf expr1 in
      let n = Syntax.Vars.fresh() in
      let ty = Real in
      let newVar = Var(n,ty) in
      Let(n,ty,exprAnf,Apply1(op,newVar))
  | Apply2(op,expr1,expr2) -> if isImmediate expr then expr else
      let expr1Anf = weakAnf expr1 in 
      let expr2Anf = weakAnf expr2 in 
      let n = Syntax.Vars.fresh() in
      let ty1 = Real in
      let newVar1 = Var(n,ty1) in 
      let m = Syntax.Vars.fresh() in 
      let ty2 = Real in
      let newVar2 = Var(m,ty2) in 
      Let(n,ty1,expr1Anf,Let(m,ty2,expr2Anf,Apply2(op,newVar1, newVar2)))
  | Let(x,ty,expr1,expr2)  -> Let(x,ty, weakAnf expr1, weakAnf expr2)
  | Pair(expr1,expr2)      -> Pair(weakAnf expr1,weakAnf expr2)
  | Case(expr1,x1,ty1,x2,ty2,expr2) 
                           -> Case(weakAnf expr1,x1,ty1,x2,ty2,weakAnf expr2)
  | Tuple(exprList)        -> Tuple(List.map weakAnf exprList)
  | Fun(varList,expr)      -> Fun(varList,weakAnf expr)
  | App(expr,exprList)     -> App(weakAnf expr, List.map weakAnf exprList)

(* rule 22,23,24 correspond to the rules for let commutativity *)
let letCommutativity expr = Rewrite.Catamorphisms.TargetCata.catamorphism [22;23;24] expr

let rec letNormalisation expr = 
  let expr2 = letCommutativity expr in 
  if equalTerms expr expr2 then expr else
  letNormalisation expr2

let anf expr = 
  let expr1 = weakAnf expr in
  letNormalisation expr1
end