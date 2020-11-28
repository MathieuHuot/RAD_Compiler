open Syntax.SourceLanguage
open Syntax.Operators
open Syntax.TargetLanguage
open Syntax.Vars

let rec forwardADType (ty : sourceType) : targetType = match ty with
| Real          -> Prod(Real,Real)
| Prod(ty1,ty2) -> Prod(forwardADType ty1,forwardADType ty2)

(* takes a primal var as input and return a pair of the primal variable and a new tangent variable *)
(* assumes that no variable from the initial term starts with d, in other words that the new returned variable is fresh *)
let dvar var : var * var = let str, i = var in var, ("d"^str,i) 

(* Simple forward AD transformation. does not assume any ANF *)
let rec forwardAD (expr : sourceSyn) : targetSyn = match expr with
| Const c               ->  Pair(Const c, Const 0.)
| Var(x,ty)             ->  let x,dx = dvar x in
                            Pair( Var(x,sourceToTargetType ty), 
                                  Var(dx,sourceToTargetType ty))
| Apply1(op,expr)       ->  let yPrimal = Syntax.Vars.fresh() in
                            let tyPrimal = Real in
                            let yTangent = Syntax.Vars.fresh() in
                            let tyTangent = Real in 
                            let exprD = forwardAD expr in
                            let dop y = match op with
                              | Cos     -> Apply1(Minus,Apply1(Sin,y))
                              | Sin     -> Apply1(Cos,y)
                              | Exp     -> Apply1(Exp,y)
                              | Minus   -> Const (-1.)
                              | Power 0 -> Const(0.)
                              | Power n -> Apply2(Times, Const(float_of_int (n-1)),Apply1(Power(n-1),y))
                            in 
                            let primal = Apply1(op,Var(yPrimal,tyPrimal)) in
                            let tangent = Apply2(Times,
                                                  dop(Var(yPrimal,tyPrimal)),
                                                  Var(yTangent,tyTangent))  
                            in 
                            Case(exprD,
                                yPrimal,
                                tyPrimal,
                                yTangent,
                                tyTangent,
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
                                                          Var(y2Tangent,ty2Tangent))) 
                            in
                            Case(expr1D,
                                  y1Primal,
                                  ty1Primal,
                                  y1Tangent,
                                  ty1Tangent,
                                  Case(expr2D,
                                        y2Primal,
                                        ty2Primal,
                                        y2Tangent,
                                        ty2Tangent,
                                        Pair(primal,tangent)))
| Let(y,ty,expr1,expr2) ->  let expr1D = forwardAD expr1 in
                            let expr2D = forwardAD expr2 in
                            let yPrimal, yTangent = dvar y in
                            let tyPrimal = sourceToTargetType ty in
                            let tyTangent = tyPrimal in
                            Case(expr1D,
                                  yPrimal,
                                  tyPrimal,
                                  yTangent,
                                  tyTangent,
                                  expr2D)

let grad context expr = 
  let dexpr = forwardAD expr in
  List.map 
      (fun (x,_,_) -> List.fold_left 
      (fun acc (y,ty2,expr2) -> let y, dy = dvar y in
      let f z = if (equal x y) then subst dy ty2 (Const(1.)) z else subst dy ty2 (Const(0.)) z in
      f (subst y ty2 expr2 acc)) dexpr context) 
      context 