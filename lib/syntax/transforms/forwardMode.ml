(* Classic forward mode differentiationas a source-code transformation using dual numbers *)
open Syntax
open Syntax.Source
open Syntax.Operators

type gradient_variables = (Syntax.Var.t * Type.t) Target.tuple

let rec forwardADType (ty : Type.t) : Target.Type.t = match ty with
  | Real           -> Target.Type.NProd [Target.Type.Real; Target.Type.Real]
  | Prod(ty1, ty2) -> Target.Type.NProd [forwardADType ty1; forwardADType ty2]

let unaryDop op expr = 
  let y, dy = Var.dvar (Syntax.Var.fresh()) in
  let ty = Target.Type.Real in
  let primal = Target.Apply1(op, Target.Var(y, ty)) in
  let tangent = Target.Apply2(Times, Target.dop op (Target.Var(y, ty)), Target.Var(dy, ty)) in 
  Target.NCase(expr, [(y, ty); (dy, ty)], Target.Tuple [primal; tangent])

let binaryDop op expr1 expr2 = 
  let y1, dy1 = Var.dvar (Syntax.Var.fresh()) in
  let ty = Target.Type.Real in
  let y2, dy2 = Var.dvar (Syntax.Var.fresh()) in
  let y1VarP = Target.Var(y1, ty) in
  let y2VarP = Target.Var(y2, ty) in
  let primal = Target.Apply2(op, y1VarP, y2VarP) in
  let tangent = Target.Apply2(Plus,
                        Target.Apply2(Times, Target.d1op op y1VarP y2VarP, Target.Var(dy1, ty)),
                        Target.Apply2(Times, Target.d2op op y1VarP y2VarP, Target.Var(dy2, ty))) in
  Target.NCase(expr1, [(y1, ty); (dy1, ty)], Target.NCase(expr2, [(y2, ty); (dy2, ty)], Target.Tuple [primal;tangent]))

(* Simple forward AD transformation. does not assume any ANF *)
let rec forwardAD (expr : t) : Target.t = match expr with
| Const c                                    -> Target.Tuple [Target.Const c; Target.Const 0.]
| Var(x,ty)                                  -> Var(x, forwardADType ty)
| Apply1(op,expr)                            -> unaryDop op (forwardAD expr)
| Apply2(op,expr1,expr2)                     -> binaryDop op (forwardAD expr1) (forwardAD expr2)
| Let(y,ty,expr1,expr2)                      -> Let(y, forwardADType ty, forwardAD expr1, forwardAD expr2)  

(**TODO: currently assumes every variable in grad_vars is of type Real. *)
(** given an expression of the form dexpr = forwardAD(expr), computes its partial derivative w.r.t. x:ty. Assumes fv is the list of free variables of dexpr *)
let partialDerivative x ty fv dexpr =
  List.fold_left (fun acc y -> if Syntax.Var.equal x y (* checks whether y = forwardAD(x) *)
                               then Target.subst y (forwardADType ty) (Target.Tuple [Var(y, Target.Type.from_source ty); Target.Const 1.]) acc (* if so, initialize its tangentpart at 1. *)
                               else Target.subst y (forwardADType ty) (Target.Tuple [Var(y, Target.Type.from_source ty); Target.Const 0.]) acc) (* otherwise at 0. *)
                 dexpr 
                 fv 

let grad grad_vars expr = 
  let dexpr = forwardAD expr in
  let fv = Target.VarSet.to_list (Target.freeVar dexpr) in
  List.map (fun (x, ty) -> partialDerivative x ty fv dexpr) grad_vars 