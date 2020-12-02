(* Prototype for Higher-Order Derivatives *)

(* This method computes (1,2) velocities. *) 
(* See the paper A Geometric Theory of Higher-Order Automatic Differentiation for more information *)
module SecondOrderForward = struct

open Syntax.SourceLanguage
open Syntax.Operators
open Syntax.TargetLanguage
open Syntax.Vars

let rec forwardAD2Type (ty : sourceType) : targetType = match ty with
  | Real          -> NProd([Real;Real;Real])
  | Prod(ty1,ty2) -> Prod(forwardAD2Type ty1,forwardAD2Type ty2)

let dvar2 var : var * var * var = let str,i = var in var,("d"^str,i),("d2"^str,i) 

let dop y (op: op1) = match op with
| Cos     -> Apply1(Minus,Apply1(Sin,y))
| Sin     -> Apply1(Cos,y)
| Exp     -> Apply1(Exp,y)
| Minus   -> Const (-1.)
| Power 0 -> Const(0.)
| Power n -> Apply2(Times, Const(float_of_int (n-1)),Apply1(Power(n-1),y))

let dop2 x dx d2x (op: op1) = match op with
 | Cos     -> Apply2(Minus, Apply1(Minus,Apply2(Times,Apply1(Cos,x),dx)), Apply2(Times,Apply1(Sin,x),d2x))
 | Sin     -> Apply2(Plus, Apply1(Minus,Apply2(Times,Apply1(Sin,x),dx)), Apply2(Times,Apply1(Cos,x),d2x))
 | Exp     -> Apply2(Plus, Apply2(Times,Apply1(Exp,x),dx), Apply2(Times,Apply1(Exp,x),d2x))
 | Minus   -> Apply1(Minus,d2x)
 | Power 0 -> Const(0.)
 | Power 1 -> d2x
 | Power n -> Apply2(Plus,
                    Apply2(Times,Apply2(Times,Const(float_of_int(n*(n-1))),Apply1(Power(n-2),x)),dx),
                    Apply2(Times,Apply2(Times,Const(float_of_int n),Apply1(Power(n-1),x)),d2x))

let d1op _ y2 (op: op2) = match op with
| Plus  -> Const(1.)
| Times -> y2
| Minus -> Const(1.)

let d2op y1 _ (op: op2) = match op with
| Plus  -> Const(1.)
| Times -> y1
| Minus -> Const(-1.)

let d2op2 x dx d2x y dy d2y  (op: op2) = match op with
| Plus  -> Apply2(Plus,d2x,d2y)
| Minus -> Apply2(Minus,d2x,d2y)
| Times -> Apply2(Plus,Apply2(Plus,Apply2(Times,d2x,y),Apply2(Times,x,d2y)),Apply2(Times,Const 2.,Apply2(Times,dx,dy)))

let rec forward2AD (expr : sourceSyn) : targetSyn = match expr with
| Const c               ->  Pair(Const c, Const 0.)
| Var(x,ty)             ->  let x,dx,d2x = dvar2 x in
                            let ty = sourceToTargetType ty in
                            Tuple([Var(x,ty);Var(dx,ty);Var(d2x,ty)])
| Apply1(op,expr)       ->  let y,dy,d2y = dvar2 (Syntax.Vars.fresh()) in
                            let ty = Real in
                            let exprD = forward2AD expr in
                            let e = Apply1(op,Var(y,ty)) in
                            let de = Apply2(Times, dop (Var(y,ty)) op, Var(dy,ty)) in 
                            let d2e = dop2 (Var(y,ty)) (Var(dy,ty)) (Var(d2y,ty)) op in
                            NCase(exprD,[(y,ty);(dy,ty);(d2y,ty)],Tuple([e;de;d2e]))
| Apply2(op,expr1,expr2)->  let x,dx,d2x = dvar2 (Syntax.Vars.fresh()) in
                            let y,dy,d2y = dvar2 (Syntax.Vars.fresh()) in
                            let ty = Real in
                            let expr1D = forward2AD expr1 in
                            let expr2D = forward2AD expr2 in
                            let e = Apply2(op,Var(x,ty),Var(y,ty)) in
                            let de = Apply2(Plus,
                                            Apply2(Times, d1op (Var(x,ty)) (Var(y,ty)) op, (Var(dx,ty))),
                                            Apply2(Times, d2op (Var(x,ty)) (Var(y,ty)) op, (Var(dy,ty)))) in
                            let d2e = d2op2 (Var(x,ty)) (Var(dx,ty)) (Var(d2x,ty)) (Var(y,ty)) (Var(dy,ty)) (Var(d2y,ty)) op in
                            NCase(expr1D,[(x,ty);(dx,ty);(d2x,ty)],
                            NCase(expr2D,[(y,ty);(dy,ty);(d2y,ty)],Tuple([e;de;d2e])))
| Let(y,ty,expr1,expr2) ->  let expr1D = forward2AD expr1 in
                            let expr2D = forward2AD expr2 in
                            let y, dy, d2y = dvar2 y in
                            let ty = sourceToTargetType ty in
                            NCase(expr1D,[(y,ty);(dy,ty);(d2y,ty)],expr2D)

(* Compute the list d2f/dx2 for all variables x from the context *)                           
let secondPartial context expr = 
  let dexpr = forward2AD expr in
  let optiDexpr = Rewrite.Optimisations.fullOpti dexpr in
  List.map 
      (fun (x,_,_) -> List.fold_left 
      (fun acc (y,ty2,expr2) -> let y,dy,d2y = dvar2 y in
      let f = if (equal x y) then subst dy ty2 (Const(1.)) else subst dy ty2 (Const(0.)) in
      f (subst d2y ty2 (Const 0.) (subst y ty2 expr2 acc))) optiDexpr context) 
      context

(* Compute the list d2f/dxi dxj for all xi,xj in the context *)
let mixedPartial context expr = 
  let n = List.length context in
  let arrayContext = Array.of_list (List.map (fun (x,_,_) -> x) context) in
  let dexpr = forward2AD expr in 
  let optiDexpr = Rewrite.Optimisations.fullOpti dexpr in
  let mixedDerivatives = Array.make_matrix n n (Const 0.) in
  for i=0 to (n-1) do
    for j=0 to (n-1) do
      mixedDerivatives.(i).(j) <- List.fold_left 
      (fun acc (y,ty2,expr2) -> let y,dy,d2y = dvar2 y in
      let f = if (equal arrayContext.(i) y) || (equal arrayContext.(j) y) then subst dy ty2 (Const(1.)) else subst dy ty2 (Const(0.)) in
      f (subst d2y ty2 (Const 0.) (subst y ty2 expr2 acc))) optiDexpr context
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
        mixedDerivatives.(i).(j) <- Rewrite.Optimisations.fullOpti (Apply2(Minus,mixedDerivatives.(i).(j),Apply2(Plus,secondPartial.(i),secondPartial.(j))))
      done
    done;
    mixedDerivatives
end


(* To compute v^T H u *)
(* module ThirdOrderForward = struct

end

(* To compute Hessian *)
module SecondOrderReverse = struct

end

(* Third order partial derivatives *)
module ThirdOrderReverse = struct

end *)