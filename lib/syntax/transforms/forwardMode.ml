(* Classic forward mode differentiationas a source-code transformation using dual numbers *)
open Syntax
open Syntax.Source
open Syntax.Operators

let rec forwardADType (ty : Type.t) : Target.Type.t = match ty with
  | Real          -> Target.Type.NProd [Target.Type.Real; Target.Type.Real]
  | Prod(ty1,ty2) -> Target.Type.NProd [forwardADType ty1; forwardADType ty2]

(* takes a primal var as input and return a pair of the primal variable and a new tangent variable *)
(* assumes that no variable from the initial term starts with d, in other words that the new returned variable is fresh *)
let dvar var : Syntax.Var.t * Syntax.Var.t = let str, i = var in var, ("d"^str, i) 

(* Simple forward AD transformation. does not assume any ANF *)
let rec forwardAD (expr : t) : Target.t = match expr with
| Const c               ->  Target.Tuple [Target.Const c; Target.Const 0.]
| Var(x,ty)             ->  let x, dx = dvar x in
                            Target.Tuple [ Target.Var(x, Target.Type.from_source ty);
                                    Target.Var(dx,Target.Type.from_source ty)]
| Apply1(op,expr)       ->  let y, dy = dvar (Syntax.Var.fresh()) in
                            let ty = Target.Type.Real in
                            let exprD = forwardAD expr in
                            let primal = Target.Apply1(op, Target.Var(y,ty)) in
                            let tangent = Target.Apply2(Times, Target.dop op (Target.Var(y,ty)), Target.Var(dy,ty)) in 
                            Target.NCase(exprD, [(y, ty); (dy, ty)], Target.Tuple [primal; tangent])
| Apply2(op,expr1,expr2)->  let y1, dy1 = dvar (Syntax.Var.fresh()) in
                            let ty1 = Target.Type.Real in
                            let y2, dy2 = dvar (Syntax.Var.fresh()) in
                            let ty2 = Target.Type.Real in
                            let y1VarP = Target.Var(y1, ty1) in
                            let y2VarP = Target.Var(y2, ty2) in
                            let expr1D = forwardAD expr1 in
                            let expr2D = forwardAD expr2 in
                            let primal = Target.Apply2(op, y1VarP, y2VarP) in
                            let tangent = Target.Apply2(Plus,
                                                  Target.Apply2(Times, Target.d1op op y1VarP y2VarP, Target.Var(dy1, ty1)),
                                                  Target.Apply2(Times, Target.d2op op y1VarP y2VarP, Target.Var(dy2, ty2))) in
                            Target.NCase(expr1D, [(y1, ty1); (dy1, ty1)], Target.NCase(expr2D, [(y2, ty2); (dy2,ty2)], Target.Tuple [primal;tangent]))
| Let(y,ty,expr1,expr2) ->  let expr1D = forwardAD expr1 in
                            let expr2D = forwardAD expr2 in
                            let y, dy = dvar y in
                            let ty = Target.Type.from_source ty in
                            Target.NCase(expr1D, [(y, ty); (dy, ty)], expr2D)

let grad context expr = 
  let dexpr = forwardAD expr in
  List.map 
      (fun ((x,_),_) -> List.fold_left 
      (fun acc ((y,ty2),expr2) -> let y, dy = dvar y in
      let f z = if (Syntax.Var.equal x y) then Target.subst dy ty2 (Target.Const(1.)) z else Target.subst dy ty2 (Target.Const(0.)) z in
      f (Target.subst y ty2 expr2 acc)) dexpr context) 
      context 
