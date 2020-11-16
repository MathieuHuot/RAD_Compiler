open Syntax.SourceLanguage
open Syntax.Operators
open Syntax.TargetLanguage
open Syntax.Vars

let rec forwardADType (ty : sourceType) : targetType = match ty with
| Real          -> Prod(Real,Real)
| Prod(ty1,ty2) -> Prod(forwardADType ty1,forwardADType ty2)

let rec dsubst (var1,var2) expr = match expr with
| Pair(Var(x,ty1),Var(_,ty2))     -> if equal x var1 then Pair(Var(x,ty1),Var(var2,ty2)) else expr
| Apply1(op,expr)                 -> Apply1(op,dsubst  (var1,var2) expr)
| Apply2(op,expr1,expr2)          -> Apply2(op,dsubst  (var1,var2) expr1,dsubst (var1,var2) expr2)
| Let(y,ty,expr1,expr2)           -> if equal var1 y || equal var2 y
  then failwith "trying to substitute a bound variable"
  else Let(y,ty,dsubst (var1,var2) expr1, dsubst (var1,var2) expr2)
| Pair(expr1,expr2)               -> Pair(dsubst (var1,var2) expr1,dsubst (var1,var2) expr2)
| Fun(y,ty,expr)                  -> if equal var1 y || equal var2 y
  then failwith "trying to substitute a bound variable"
  else Fun(y,ty,dsubst (var1,var2) expr)
| App(expr1,expr2)                -> App(dsubst (var1,var2) expr1,dsubst (var1,var2) expr2)
| Case(expr1,y1,ty1,y2,ty2,expr2) -> if equal var1 y1 || equal var1 y2 ||  equal var2 y1 ||  equal var2 y2
  then failwith "trying to substitute a bound variable"
  else Case(dsubst (var1,var2) expr1,y1,ty1,y2,ty2,dsubst (var1,var2) expr2)
| _ -> expr

(* Simple forward AD transformation. does not assume ANF *)
let rec forwardAD (expr : synSource) : synTarget = match expr with
| Const c               -> Pair(Const c, Const 0.)
| Var(x,ty)             -> Pair(Var(x,sourceToTargetType ty), Var(Syntax.Vars.fresh(),sourceToTargetType ty))
| Apply1(op,expr)       ->  let yPrimal = Syntax.Vars.fresh() in
                            let tyPrimal = Real in
                            let yTangent = Syntax.Vars.fresh() in
                            let tyTangent = Real in 
                            let exprD = forwardAD expr in
                            let dop y = match op with
                              | Cos   -> Apply1(Minus,Apply1(Sin,y))
                              | Sin   -> Apply1(Cos,y)
                              | Exp   -> Apply1(Exp,y)
                              | Minus -> Const (-1.)
                            in 
                            let primal = Apply1(op,Var(yPrimal,tyPrimal)) in
                            let tangent = Apply2(Times,
                              dop(Var(yPrimal,tyPrimal)),
                              Var(yTangent,tyTangent))  in 
                            Case(exprD,yPrimal,tyPrimal,yTangent,tyTangent,
                            Pair(primal,tangent))
| Apply2(op,expr1,expr2)->  let y1Primal = Syntax.Vars.fresh() in
                            let ty1Primal = Real in
                            let y1VarP = Var(y1Primal,ty1Primal) in
                            let y1Tangent = Syntax.Vars.fresh() in
                            let ty1Tangent = Real in
                            let y2Primal = Syntax.Vars.fresh() in
                            let ty2Primal = Real in
                            let y2VarP = Var(y2Primal,ty2Primal) in
                            let y2Tangent = Syntax.Vars.fresh() in
                            let ty2Tangent = Real in
                            let expr1D = forwardAD expr1 in
                            let expr2D = forwardAD expr2 in
                            let d1op _ y2 = match op with
                              | Plus  -> Const(1.)
                              | Times -> y2
                              | Minus -> Const(1.)
                            in 
                            let d2op y1 _ = match op with
                            | Plus  -> Const(1.)
                            | Times -> y1
                            | Minus -> Const(-1.)
                            in 
                            let primal = Apply2(op,y1VarP,y2VarP) in
                            let tangent = Apply2(Plus,
                              Apply2(Times,
                                d1op y1VarP y2VarP,
                                Var(y1Tangent,ty1Tangent)),
                              Apply2(Times,
                                d2op y1VarP y2VarP,
                                Var(y2Tangent,ty2Tangent))) in
                            Case(expr1D,y1Primal,ty1Primal,y1Tangent,ty1Tangent,
                            Case(expr2D,y2Primal,ty2Primal,y2Tangent,ty2Tangent,
                            Pair(primal,tangent)
                            ))
| Let(y,ty,expr1,expr2) ->  let expr1D = forwardAD expr1 in
                            let yPrimal = y in
                            let tyPrimal = sourceToTargetType ty in
                            let yTangent = Syntax.Vars.fresh() in
                            let tyTangent = sourceToTargetType ty in 
                            let expr2D = dsubst (yPrimal,yTangent) (forwardAD expr2) in
                            Case(expr1D,yPrimal,tyPrimal,yTangent,tyTangent,
                            expr2D)