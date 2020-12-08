(* Prototype for Higher-Order Derivatives *)
(* See the paper A Geometric Theory of Higher-Order Automatic Differentiation for more information *)

open Syntax.Operators
open Syntax.TargetLanguage

(* Helpers *)

(* partial derivative of unary operator *)
let dop y (op: op1) = match op with
  | Cos     -> Apply1(Minus, Apply1(Sin, y))
  | Sin     -> Apply1(Cos, y)
  | Exp     -> Apply1(Exp, y)
  | Minus   -> Const (-1.)
  | Power 0 -> Const(0.)
  | Power n -> Apply2(Times, Const(float_of_int (n-1)), Apply1(Power(n-1), y))

(* first partial derivative of binary operator *)
let d1op _ y2 (op: op2) = match op with
  | Plus  -> Const(1.)
  | Times -> y2
  | Minus -> Const(1.)

(* second partial derivative of binary operator *)
let d2op y1 _ (op: op2) = match op with
  | Plus  -> Const(1.)
  | Times -> y1
  | Minus -> Const(-1.)

(* second derivative of binary operator *)
let dop22 x d1x d2x ddx (op: op1) = match op with
  | Cos     -> Apply2(Minus, Apply1(Minus, Apply2(Times, Apply1(Cos, x), Apply2(Times, d1x, d2x))), Apply2(Times,Apply1(Sin, x), ddx))
  | Sin     -> Apply2(Plus, Apply1(Minus, Apply2(Times, Apply1(Sin, x), Apply2(Times, d1x, d2x))), Apply2(Times, Apply1(Cos, x), ddx))
  | Exp     -> Apply2(Plus, Apply2(Times, Apply1(Exp, x), Apply2(Times, d1x, d2x)), Apply2(Times, Apply1(Exp, x), ddx))
  | Minus   -> Apply1(Minus, ddx)
  | Power 0 -> Const(0.)
  | Power 1 -> ddx
  | Power n -> Apply2(Plus,
                      Apply2(Times, Apply2(Times, Const(float_of_int(n*(n-1))), Apply1(Power(n-2),x)), Apply2(Times, d1x, d2x)),
                      Apply2(Times, Apply2(Times, Const(float_of_int n), Apply1(Power(n-1),x)), ddx))

let d2op22 x d1x d2x ddx y d1y d2y ddy (op: op2) = match op with
  | Plus  -> Apply2(Plus, ddx, ddy)
  | Minus -> Apply2(Minus, ddx, ddy)
  | Times -> Apply2(Plus,
                    Apply2(Plus, Apply2(Times, ddx, y), Apply2(Times, x, ddy)),
                    Apply2(Plus,
                            Apply2(Plus, Apply2(Times, d1x, d2x), Apply2(Times, d1x, d2y)),
                            Apply2(Plus, Apply2(Times, d1y, d2x), Apply2(Times, d1y, d2y))))

(* This method computes (1,2) velocities. *) 
module Jets12 = struct

open Syntax.SourceLanguage
open Syntax.Operators
open Syntax.TargetLanguage
open Syntax.Vars

let dvar2 var : var * var * var = let str,i = var in var,("d"^str,i),("d2"^str,i) 

(* second derivative of binary operator *)
let dop2 x dx d2x (op: op1) = match op with
  | Cos     -> Apply2(Minus, Apply1(Minus, Apply2(Times, Apply1(Cos, x), dx)), Apply2(Times, Apply1(Sin, x), d2x))
  | Sin     -> Apply2(Plus, Apply1(Minus, Apply2(Times, Apply1(Sin, x), dx)), Apply2(Times, Apply1(Cos, x), d2x))
  | Exp     -> Apply2(Plus, Apply2(Times, Apply1(Exp, x), dx), Apply2(Times, Apply1(Exp, x), d2x))
  | Minus   -> Apply1(Minus, d2x)
  | Power 0 -> Const(0.)
  | Power 1 -> d2x
  | Power n -> Apply2(Plus,
                      Apply2(Times, Apply2(Times, Const(float_of_int(n*(n-1))), Apply1(Power(n-2), x)), dx),
                      Apply2(Times, Apply2(Times, Const(float_of_int n), Apply1(Power(n-1), x)), d2x))
             
let d2op2 x dx d2x y dy d2y  (op: op2) = match op with
  | Plus  -> Apply2(Plus, d2x, d2y)
  | Minus -> Apply2(Minus, d2x, d2y)
  | Times -> Apply2(Plus, Apply2(Plus, Apply2(Times, d2x, y), Apply2(Times, x, d2y)), Apply2(Times, Const 2., Apply2(Times, dx, dy)))

let rec forwardAD12Type (ty : sourceType) : targetType = match ty with
  | Real          -> NProd([Real; Real; Real])
  | Prod(ty1,ty2) -> Prod(forwardAD12Type ty1, forwardAD12Type ty2)

let rec forward12AD (expr: sourceSyn) : targetSyn = match expr with
| Const c               ->  Tuple([Const c; Const 0.; Const 0.])
| Var(x,ty)             ->  let x, dx, d2x = dvar2 x in
                            let ty = sourceToTargetType ty in
                            Tuple([Var(x, ty); Var(dx, ty); Var(d2x, ty)])
| Apply1(op,expr)       ->  let y, dy, d2y = dvar2 (Syntax.Vars.fresh()) in
                            let ty = Real in
                            let exprD = forward12AD expr in
                            let e = Apply1(op, Var(y, ty)) in
                            let de = Apply2(Times, dop (Var(y, ty)) op, Var(dy, ty)) in 
                            let d2e = dop2 (Var(y, ty)) (Var(dy, ty)) (Var(d2y, ty)) op in
                            NCase(exprD, [(y, ty); (dy, ty); (d2y, ty)], Tuple([e; de; d2e]))
| Apply2(op,expr1,expr2)->  let x, dx, d2x = dvar2 (Syntax.Vars.fresh()) in
                            let y, dy, d2y = dvar2 (Syntax.Vars.fresh()) in
                            let ty = Real in
                            let expr1D = forward12AD expr1 in
                            let expr2D = forward12AD expr2 in
                            let e = Apply2(op, Var(x, ty), Var(y, ty)) in
                            let de = Apply2(Plus,
                                            Apply2(Times, d1op (Var(x, ty)) (Var(y, ty)) op, (Var(dx, ty))),
                                            Apply2(Times, d2op (Var(x, ty)) (Var(y, ty)) op, (Var(dy, ty)))) in
                            let d2e = d2op2 (Var(x, ty)) (Var(dx, ty)) (Var(d2x, ty)) (Var(y, ty)) (Var(dy, ty)) (Var(d2y, ty)) op in
                            NCase(expr1D, [(x, ty); (dx, ty); (d2x, ty)],
                            NCase(expr2D, [(y, ty); (dy, ty); (d2y, ty)], 
                            Tuple([e; de; d2e])))
| Let(y,ty,expr1,expr2) ->  let expr1D = forward12AD expr1 in
                            let expr2D = forward12AD expr2 in
                            let y, dy, d2y = dvar2 y in
                            let ty = sourceToTargetType ty in
                            NCase(expr1D, [(y, ty); (dy, ty); (d2y, ty)], expr2D)

(* Compute the list d2f/dx2 for all variables x from the context *)                           
let secondPartial context expr = 
  let dexpr = forward12AD expr in
  let optiDexpr = Rewrite.Optimisations.fullOpti dexpr in
  List.map 
      (fun (x,_,_) -> List.fold_left 
      (fun acc (y, ty2, expr2) -> let y, dy, d2y = dvar2 y in
      let f = if (equal x y) then subst dy ty2 (Const(1.)) else subst dy ty2 (Const(0.)) in
      f (subst d2y ty2 (Const 0.) (subst y ty2 expr2 acc))) optiDexpr context) 
      context

(* Compute the list d2f/dxi dxj for all xi,xj in the context *)
let mixedPartial context expr = 
  let n = List.length context in
  let arrayContext = Array.of_list (List.map (fun (x,_,_) -> x) context) in
  let dexpr = forward12AD expr in 
  let optiDexpr = Rewrite.Optimisations.fullOpti dexpr in
  let mixedDerivatives = Array.make_matrix n n (Const 0.) in
  for i=0 to (n-1) do
    for j=0 to (n-1) do
      mixedDerivatives.(i).(j) <- 
        List.fold_left 
          (fun acc (y,ty2,expr2) -> let y,dy,d2y = dvar2 y in
          let f = if (equal arrayContext.(i) y) || (equal arrayContext.(j) y) 
          then subst dy ty2 (Const(1.)) 
          else subst dy ty2 (Const(0.)) in
          f (subst d2y ty2 (Const 0.) (subst y ty2 expr2 acc))
          ) 
          optiDexpr 
          context
    done
  done; 
  mixedDerivatives
  
  (*TODO: currently not working and not optimized *)
  let hessian context expr = 
    let mixedDerivatives = mixedPartial context expr in
    let secondPartial = Array.of_list (secondPartial context expr) in
    let n = Array.length secondPartial in
    for i=0 to (n-1) do
      for j=0 to (n-1) do
        mixedDerivatives.(i).(j) <- 
          Rewrite.Optimisations.fullOpti 
          (Apply2(Minus, mixedDerivatives.(i).(j), 
                        Apply2(Plus, secondPartial.(i), secondPartial.(j)))
          )
      done
    done;
    mixedDerivatives
end

(* This method computes (2,2) velocities. *) 
module Jets22 = struct

open Syntax.SourceLanguage
open Syntax.Operators
open Syntax.TargetLanguage
open Syntax.Vars

let rec forwardAD22Type (ty : sourceType) : targetType = match ty with
  | Real          -> NProd([Real;Real;Real;Real])
  | Prod(ty1,ty2) -> Prod(forwardAD22Type ty1,forwardAD22Type ty2)

let dvar22 var : var * var * var * var = let str, i = var in var, ("d1"^str, i), ("d2"^str, i), ("dd"^str, i) 

let rec forward22AD (expr: sourceSyn) : targetSyn = match expr with
| Const c               ->  Tuple([Const c; Const 0.; Const 0.; Const 0.])
| Var(x,ty)             ->  let x, d1x, d2x, ddx = dvar22 x in
                            let ty = sourceToTargetType ty in
                            Tuple([Var(x, ty); Var(d1x, ty); Var(d2x, ty); Var(ddx, ty)])
| Apply1(op,expr)       ->  let y, d1y, d2y, ddy = dvar22 (Syntax.Vars.fresh()) in
                            let ty = Real in
                            let exprD = forward22AD expr in
                            let e = Apply1(op, Var(y, ty)) in
                            let d1e = Apply2(Times, dop (Var(y, ty)) op, Var(d1y, ty)) in
                            let d2e = Apply2(Times, dop (Var(y, ty)) op, Var(d2y, ty)) in  
                            let dde = dop22 (Var(y, ty)) (Var(d1y, ty)) (Var(d2y, ty)) (Var(ddy, ty)) op in
                            NCase(exprD,[(y, ty); (d1y, ty); (d2y, ty); (ddy, ty)], Tuple([e; d1e; d2e; dde]))
| Apply2(op,expr1,expr2)->  let x, d1x, d2x, ddx = dvar22 (Syntax.Vars.fresh()) in
                            let y, d1y, d2y, ddy = dvar22 (Syntax.Vars.fresh()) in
                            (* compared notation to the paper cited above *)
                            (* x is first index, y is second, d1 is for du, d2 for dv, dd for dudv *)
                            let ty = Real in
                            let expr1D = forward22AD expr1 in
                            let expr2D = forward22AD expr2 in
                            let e = Apply2(op, Var(x, ty), Var(y, ty)) in
                            let d1e = Apply2(Plus,
                                            Apply2(Times, d1op (Var(x, ty)) (Var(y, ty)) op, (Var(d1x, ty))),
                                            Apply2(Times, d2op (Var(x, ty)) (Var(y, ty)) op, (Var(d1y, ty)))) in
                            let d2e = Apply2(Plus,
                                            Apply2(Times, d1op (Var(x, ty)) (Var(y, ty)) op, (Var(d2x, ty))),
                                            Apply2(Times, d2op (Var(x, ty)) (Var(y, ty)) op, (Var(d2y, ty)))) in                
                            let dde = d2op22 (Var(x, ty)) (Var(d1x, ty)) (Var(d2x, ty)) (Var(ddx, ty)) 
                                             (Var(y, ty)) (Var(d1y, ty)) (Var(d2y, ty)) (Var(ddy, ty)) 
                                             op in
                            NCase(expr1D, [(x, ty); (d1x, ty); (d2x, ty);  (ddx, ty)],
                            NCase(expr2D, [(y, ty); (d1y, ty); (d2y, ty);  (ddy, ty)], 
                            Tuple([e; d1e; d2e; dde])))
| Let(y,ty,expr1,expr2) ->  let expr1D = forward22AD expr1 in
                            let expr2D = forward22AD expr2 in
                            let y, d1y, d2y, ddy = dvar22 y in
                            let ty = sourceToTargetType ty in
                            NCase(expr1D, [(y, ty); (d1y, ty); (d2y, ty);  (ddy, ty)], expr2D)  
end

module Jets33 = struct

open Syntax.SourceLanguage
open Syntax.Operators
open Syntax.TargetLanguage
open Syntax.Vars

let rec forwardAD33Type (ty : sourceType) : targetType = match ty with
  | Real          -> NProd([Real; Real; Real; Real; Real; Real; Real; Real])
  | Prod(ty1,ty2) -> Prod(forwardAD33Type ty1,forwardAD33Type ty2)

let dvar33 var : var * var * var * var * var * var * var * var = 
  let str, i = var in var, 
                      ("d1"^str, i), ("d2"^str, i), ("d3"^str, i), 
                      ("dd1"^str, i),  ("dd2"^str, i),  ("dd3"^str, i),  
                      ("ddd"^str, i)

(* third derivative of unary operator *) 
let dop33 x d1x d2x ddx (op: op1) = match op with
  | Cos     -> Apply2(Minus, Apply1(Minus, Apply2(Times, Apply1(Cos, x), Apply2(Times, d1x, d2x))), Apply2(Times,Apply1(Sin, x), ddx))
  | Sin     -> Apply2(Plus, Apply1(Minus, Apply2(Times, Apply1(Sin, x), Apply2(Times, d1x, d2x))), Apply2(Times, Apply1(Cos, x), ddx))
  | Exp     -> Apply2(Plus, Apply2(Times, Apply1(Exp, x), Apply2(Times, d1x, d2x)), Apply2(Times, Apply1(Exp, x), ddx))
  | Minus   -> Apply1(Minus, ddx)
  | Power 0 -> Const(0.)
  | Power 1 -> ddx
  | Power n -> Apply2(Plus,
                      Apply2(Times, Apply2(Times, Const(float_of_int(n*(n-1))), Apply1(Power(n-2),x)), Apply2(Times, d1x, d2x)),
                      Apply2(Times, Apply2(Times, Const(float_of_int n), Apply1(Power(n-1),x)), ddx))

(* third derivative of binary operator *)                     
let d2op33 x d1x d2x d3x dd1x dd2x dd3x dddx y d1y d2y d3y dd1y dd2y dd3y dddy (op: op2) = match op with
  | Plus  -> Apply2(Plus, dddx, dddy)
  | Minus -> Apply2(Minus, dddx, dddy)
  | Times -> Apply2(Plus,
                    Apply2(Plus, Apply2(Times, dddx, y), Apply2(Times, x, dddy)),
                    Apply2(Plus,
                            Apply2(Plus, 
                                    Apply2(Plus, Apply2(Plus, Apply2(Times, d2x, dd3x), Apply2(Times, d1x, dd2x)), Apply2(Times, d3x, dd1x)), 
                                    Apply2(Plus, Apply2(Plus, Apply2(Times, d2x, dd3y), Apply2(Times, d1x, dd2y)), Apply2(Times, d3x, dd1y))),
                            Apply2(Plus, 
                                    Apply2(Plus, Apply2(Plus, Apply2(Times, d2y, dd3x), Apply2(Times, d1y, dd2x)), Apply2(Times, d3y, dd1x)), 
                                    Apply2(Plus, Apply2(Plus, Apply2(Times, d2y, dd3y), Apply2(Times, d1y, dd2y)), Apply2(Times, d3y, dd1y)))))

let rec forward33AD (expr: sourceSyn) : targetSyn = match expr with
| Const c               ->  Tuple([Const c; Const 0.; Const 0.; Const 0.; Const 0.; Const 0.; Const 0.; Const 0.])
| Var(x,ty)             ->  let x, d1x, d2x, d3x, dd1x, dd2x, dd3x, dddx = dvar33 x in
                            let ty = sourceToTargetType ty in
                            Tuple([Var(x, ty); Var(d1x, ty); Var(d2x, ty); Var(d3x, ty); Var(dd1x, ty); Var(dd2x, ty); Var(dd3x, ty); Var(dddx, ty);])
| Apply1(op,expr)       ->  let y, d1y, d2y, d3y, dd1y, dd2y, dd3y, dddy = dvar33 (Syntax.Vars.fresh()) in
                            let ty = Real in
                            let exprD = forward33AD expr in
                            let e = Apply1(op, Var(y, ty)) in
                            let d1e = Apply2(Times, dop (Var(y, ty)) op, Var(d1y, ty)) in
                            let d2e = Apply2(Times, dop (Var(y, ty)) op, Var(d2y, ty)) in
                            let d3e = Apply2(Times, dop (Var(y, ty)) op, Var(d3y, ty)) in   
                            let dd1e = dop22 (Var(y, ty)) (Var(d2y, ty)) (Var(d1y, ty)) (Var(dd1y, ty)) op in
                            let dd2e = dop22 (Var(y, ty)) (Var(d2y, ty)) (Var(d3y, ty)) (Var(dd2y, ty)) op in
                            let dd3e = dop22 (Var(y, ty)) (Var(d1y, ty)) (Var(d3y, ty)) (Var(dd3y, ty)) op in
                            let ddde = dop33 (Var(y, ty)) (Var(d1y, ty)) (Var(d2y, ty)) (Var(dddy, ty)) op in
                            NCase(exprD, 
                                  [(y, ty); (d1y, ty); (d2y, ty); (d3y, ty); (dd1y, ty); (dd2y, ty); (dd3y, ty);  (dddy, ty)],  
                                  Tuple([e; d1e; d2e; d3e; dd1e; dd2e; dd3e; ddde]))
| Apply2(op,expr1,expr2)->  let x, d1x, d2x, d3x, dd1x, dd2x, dd3x, dddx = dvar33 (Syntax.Vars.fresh()) in
                            let y, d1y, d2y, d3y, dd1y, dd2y, dd3y, dddy = dvar33 (Syntax.Vars.fresh()) in
                            let ty = Real in
                            let expr1D = forward33AD expr1 in
                            let expr2D = forward33AD expr2 in
                            let e = Apply2(op, Var(x, ty), Var(y, ty)) in
                            let d1e = Apply2(Plus,
                                            Apply2(Times, d1op (Var(x, ty)) (Var(y, ty)) op, (Var(d1x, ty))),
                                            Apply2(Times, d2op (Var(x, ty)) (Var(y, ty)) op, (Var(d1y, ty)))) in
                            let d2e = Apply2(Plus,
                                            Apply2(Times, d1op (Var(x, ty)) (Var(y, ty)) op, (Var(d2x, ty))),
                                            Apply2(Times, d2op (Var(x, ty)) (Var(y, ty)) op, (Var(d2y, ty)))) in
                            let d3e = Apply2(Plus,
                                            Apply2(Times, d1op (Var(x, ty)) (Var(y, ty)) op, (Var(d3x, ty))),
                                            Apply2(Times, d2op (Var(x, ty)) (Var(y, ty)) op, (Var(d3y, ty)))) in                  
                            let dd1e = d2op22 (Var(x, ty)) (Var(d1x, ty)) (Var(d2x, ty)) (Var(dd1x, ty)) 
                                              (Var(y, ty)) (Var(d1y, ty)) (Var(d2y, ty)) (Var(dd1y, ty)) 
                                              op in
                            let dd2e = d2op22 (Var(x, ty)) (Var(d1x, ty)) (Var(d2x, ty)) (Var(dd2x, ty)) 
                                              (Var(y, ty)) (Var(d1y, ty)) (Var(d2y, ty)) (Var(dd2y, ty)) 
                                              op in
                            let dd3e = d2op22 (Var(x, ty)) (Var(d1x, ty)) (Var(d2x, ty)) (Var(dd3x, ty)) 
                                              (Var(y, ty)) (Var(d1y, ty)) (Var(d2y, ty)) (Var(dd3y, ty)) 
                                              op in
                            let ddde = d2op33 (Var(x, ty)) (Var(d1x, ty)) (Var(d2x, ty)) (Var(d3x, ty)) (Var(dd1x, ty)) (Var(dd2x, ty)) (Var(dd3x, ty)) (Var(dddx, ty))
                                              (Var(y, ty)) (Var(d1y, ty)) (Var(d2y, ty)) (Var(d3y, ty)) (Var(dd1y, ty)) (Var(dd2y, ty)) (Var(dd3y, ty)) (Var(dddy, ty))
                                              op in            
                            NCase(expr1D, [(x, ty); (d1x, ty); (d2x, ty); (d3x, ty); (dd1x, ty); (dd2x, ty); (dd3x, ty);  (dddx, ty)],
                            NCase(expr2D, [(y, ty); (d1y, ty); (d2y, ty); (d3y, ty); (dd1y, ty); (dd2y, ty); (dd3y, ty);  (dddy, ty)], 
                            Tuple([e; d1e; d2e; d3e; dd1e; dd2e; dd3e; ddde])))
| Let(y,ty,expr1,expr2) ->  let expr1D = forward33AD expr1 in
                            let expr2D = forward33AD expr2 in
                            let y, d1y, d2y, d3y, dd1y, dd2y, dd3y, dddy = dvar33 y in
                            let ty = sourceToTargetType ty in
                            NCase(expr1D, [(y, ty); (d1y, ty); (d2y, ty); (d3y, ty); (dd1y, ty); (dd2y, ty); (dd3y, ty);  (dddy, ty)], expr2D)  
end