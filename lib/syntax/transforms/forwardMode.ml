open Syntax.SourceLanguage
open Syntax.Operators
open Syntax.TargetLanguage

let rec sourceToTargetType (ty : sourceType) : targetType = match ty with
| Real          -> Real
| Prod(ty1,ty2) -> Prod(sourceToTargetType ty1,sourceToTargetType ty2)

let rec forwardAD (expr : synSource) : synTarget = match expr with
| Const c               -> Pair(Const c, Const 0.)
| Var(x,ty)             -> Pair(Var(x,sourceToTargetType ty), Var(Syntax.Vars.fresh(),sourceToTargetType ty))
| Apply1(op,expr)       ->  let y = Syntax.Vars.fresh() in
                            let y1 = Syntax.Vars.fresh() in
                            let y2 = Syntax.Vars.fresh() in
                            let ty = Prod(Real,Real) in
                            let ty1 = Real in
                            let ty2 = Real in 
                            let exprD = forwardAD expr in
                            let dop = Cos in (* TODO *)
                            let dexpr = Apply1(dop,Var(y1,ty1)) in
                            Let(y,ty,exprD,Case(Var(y,ty),y1,ty1,y2,ty2, Pair(Apply1(op,Var(y1,ty1)),Apply2(Times,dexpr,Var(y2,ty)))))
| Apply2(op,expr1,expr2)->  failwith "TODO" 
| Let(x,ty,expr1,expr2) ->  failwith "TODO" 