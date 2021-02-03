open Syntax
open Syntax.Source

let rec travserseType (ty: Type.t) f : Target.Type.t = match ty with
  | Real -> f Target.Type.Real
  | Prod(ty1, ty2) -> Target.Type.NProd [travserseType ty f; travserseType ty2 f]
  | Array(n, ty)   -> Target.Type.Array(n, travserseType ty f)

let rec travserse (expr : t) f1 f2 f3 f4 f5 : Target.t = match expr with
  | Const c                                    -> f1 c
  | Var(x,ty)                                  -> f2 x ty
  | Apply1(op,expr)                            -> f3 op (travserse expr f1 f2 f3 f4 f5)
  | Apply2(op,expr1,expr2)                     -> f4 op (travserse expr1 f1 f2 f3 f4 f5) (travserse expr2 f1 f2 f3 f4 f5)
  | Let(y,ty,expr1,expr2)                      -> Target.Let(y, f5 ty, travserse expr1 f1 f2 f3 f4 f5, travserse expr2 f1 f2 f3 f4 f5)
  | Map (x, ty, expr1, expr2)                  -> Target.Map(x, f5 ty, travserse expr1 f1 f2 f3 f4 f5, travserse expr2 f1 f2 f3 f4 f5)
  | Map2 (x, t1, y, t2, expr1, expr2, expr3)   -> Target.Map2 (x, f5 t1, y, f5 t2, travserse expr1 f1 f2 f3 f4 f5, travserse expr2 f1 f2 f3 f4 f5, travserse expr3 f1 f2 f3 f4 f5)
  | Reduce (x, t1, y, t2, expr1, expr2, expr3) -> Target.Reduce (x, f5 t1, y, f5 t2, travserse expr1 f1 f2 f3 f4 f5, travserse expr2 f1 f2 f3 f4 f5, travserse expr3 f1 f2 f3 f4 f5)
  | Scan (x, t1, y, t2, expr1, expr2, expr3)   -> Target.Scan (x, f5 t1, y, f5 t2, travserse expr1 f1 f2 f3 f4 f5, travserse expr2 f1 f2 f3 f4 f5, travserse expr3 f1 f2 f3 f4 f5)
  | Fold (x, t1, y, t2, expr1, expr2, expr3)   -> Target.Fold (x, f5 t1, y, f5 t2, travserse expr1 f1 f2 f3 f4 f5, travserse expr2 f1 f2 f3 f4 f5, travserse expr3 f1 f2 f3 f4 f5)
  | Get(n, expr)                               -> Target.Get(n, travserse expr f1 f2 f3 f4 f5)
  | Array (exprList)                           -> Target.Array(List.map (fun x -> travserse x f1 f2 f3 f4 f5) exprList)