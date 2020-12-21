(* Prototype for Higher-Order Derivatives *)
(* See the paper A Geometric Theory of Higher-Order Automatic Differentiation for more information *)

open Syntax
open Operators
open Target

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

open Source
open Target

let dvar2 var : Var.t * Var.t * Var.t = let str,i = var in var,("d"^str,i),("d2"^str,i) 

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

let rec forwardAD12Type (ty : sourceType) : Type.t = match ty with
  | Real          -> NProd([Real; Real; Real])
  | Prod(ty1,ty2) -> NProd [forwardAD12Type ty1; forwardAD12Type ty2]

let rec forward12AD (expr: sourceSyn) : targetSyn = match expr with
| Const c               ->  Tuple([Const c; Const 0.; Const 0.])
| Var(x,ty)             ->  let x, dx, d2x = dvar2 x in
                            let ty = Type.sourceToTarget ty in
                            Tuple([Var(x, ty); Var(dx, ty); Var(d2x, ty)])
| Apply1(op,expr)       ->  let y, dy, d2y = dvar2 (Var.fresh()) in
                            let ty = Type.Real in
                            let exprD = forward12AD expr in
                            let e = Apply1(op, Var(y, ty)) in
                            let de = Apply2(Times, dop (Var(y, ty)) op, Var(dy, ty)) in 
                            let d2e = dop2 (Var(y, ty)) (Var(dy, ty)) (Var(d2y, ty)) op in
                            NCase(exprD, [(y, ty); (dy, ty); (d2y, ty)], Tuple([e; de; d2e]))
| Apply2(op,expr1,expr2)->  let x, dx, d2x = dvar2 (Var.fresh()) in
                            let y, dy, d2y = dvar2 (Var.fresh()) in
                            let ty = Type.Real in
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
                            let ty = Type.sourceToTarget ty in
                            NCase(expr1D, [(y, ty); (dy, ty); (d2y, ty)], expr2D)

(* Compute the list d2f/dx2 for all variables x from the context *)                           
let secondPartial context expr = 
  let dexpr = forward12AD expr in
  let optiDexpr = Rewrite.Optimisations.fullOpti dexpr in
  List.map 
      (fun (x,_,_) -> List.fold_left 
      (fun acc (y, ty2, expr2) -> let y, dy, d2y = dvar2 y in
      let f = if (Var.equal x y) then subst dy ty2 (Const(1.)) else subst dy ty2 (Const(0.)) in
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
          let f = if (Var.equal arrayContext.(i) y) || (Var.equal arrayContext.(j) y) 
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

open Source
open Operators
open Target

let rec forwardAD22Type (ty : sourceType) : Type.t = match ty with
  | Real          -> NProd([Real;Real;Real;Real])
  | Prod(ty1,ty2) -> NProd [forwardAD22Type ty1;forwardAD22Type ty2]

let dvar22 var : Var.t * Var.t * Var.t * Var.t = let str, i = var in var, ("d1"^str, i), ("d2"^str, i), ("dd"^str, i) 

let rec forward22AD (expr: sourceSyn) : targetSyn = match expr with
| Const c               ->  Tuple([Const c; Const 0.; Const 0.; Const 0.])
| Var(x,ty)             ->  let x, d1x, d2x, ddx = dvar22 x in
                            let ty = Type.sourceToTarget ty in
                            Tuple([Var(x, ty); Var(d1x, ty); Var(d2x, ty); Var(ddx, ty)])
| Apply1(op,expr)       ->  let y, d1y, d2y, ddy = dvar22 (Var.fresh()) in
                            let ty = Type.Real in
                            let exprD = forward22AD expr in
                            let e = Apply1(op, Var(y, ty)) in
                            let d1e = Apply2(Times, dop (Var(y, ty)) op, Var(d1y, ty)) in
                            let d2e = Apply2(Times, dop (Var(y, ty)) op, Var(d2y, ty)) in  
                            let dde = dop22 (Var(y, ty)) (Var(d1y, ty)) (Var(d2y, ty)) (Var(ddy, ty)) op in
                            NCase(exprD,[(y, ty); (d1y, ty); (d2y, ty); (ddy, ty)], Tuple([e; d1e; d2e; dde]))
| Apply2(op,expr1,expr2)->  let x, d1x, d2x, ddx = dvar22 (Var.fresh()) in
                            let y, d1y, d2y, ddy = dvar22 (Var.fresh()) in
                            (* compared notation to the paper cited above *)
                            (* x is first index, y is second, d1 is for du, d2 for dv, dd for dudv *)
                            let ty = Type.Real in
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
                            let ty = Type.sourceToTarget ty in
                            NCase(expr1D, [(y, ty); (d1y, ty); (d2y, ty);  (ddy, ty)], expr2D)  
end


(* This method computes (3,3) velocities. *) 
module Jets33 = struct

open Source
open Operators
open Target

let rec forwardAD33Type (ty : sourceType) : Type.t = match ty with
  | Real          -> NProd([Real; Real; Real; Real; Real; Real; Real; Real])
  | Prod(ty1,ty2) -> NProd [forwardAD33Type ty1;forwardAD33Type ty2]

let dvar33 var : Var.t * Var.t * Var.t * Var.t * Var.t * Var.t * Var.t * Var.t = 
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
                            let ty = Type.sourceToTarget ty in
                            Tuple([Var(x, ty); Var(d1x, ty); Var(d2x, ty); Var(d3x, ty); Var(dd1x, ty); Var(dd2x, ty); Var(dd3x, ty); Var(dddx, ty);])
| Apply1(op,expr)       ->  let y, d1y, d2y, d3y, dd1y, dd2y, dd3y, dddy = dvar33 (Var.fresh()) in
                            let ty = Type.Real in
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
| Apply2(op,expr1,expr2)->  let x, d1x, d2x, d3x, dd1x, dd2x, dd3x, dddx = dvar33 (Var.fresh()) in
                            let y, d1y, d2y, d3y, dd1y, dd2y, dd3y, dddy = dvar33 (Var.fresh()) in
                            let ty = Type.Real in
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
                            let ty = Type.sourceToTarget ty in
                            NCase(expr1D, [(y, ty); (d1y, ty); (d2y, ty); (d3y, ty); (dd1y, ty); (dd2y, ty); (dd3y, ty);  (dddy, ty)], expr2D)  
end 


(* This method comptues (1,2)-covelocities. *)
(* It computes the whole hessian in one pass on a function Real^n -> Real *)
(* Similarly to reverse-mode computing the whole gradient in one pass *)
(* Reverse-mode can be seen as (1,1)-covelocities *)
(* Be Careful, this implementation is memory intensive !! It seems that an implementation of
   (1,2)-covelocities  cannot be easily turned to a "local" implementation, as opposed to the other approaches we've seen so far.
   This might be for deep theoretical reasons (again, see the paper by Betancourt). 
   The best way to compute the whole hessian of a functin real^n -> real might be to use mixed methods, implemented below. *)
module CoJets12 = struct
(*TODO: currently not implemented *)
open Syntax.Source
open Syntax.Operators
open Syntax.Target
open Anf

type context = (Syntax.Var.t * sourceType) tuple

let dvar var : Syntax.Var.t *  Syntax.Var.t = let str, i = var in (str, i), ("d"^str, i)

let getPos (x,ty) list = 
  let rec aux pos list = match list with
  | [] -> failwith "getPos: element not found"
  | (y,ty2)::tl -> if Syntax.Var.equal x y && Syntax.Source.equalTypes ty ty2 
                    then pos 
                    else aux (pos+1) tl
  in aux 0 list

let rec addToPos i list y = match i, list with
  | _,[]      -> failwith "addToPos: no element at this position in the list"
  | 0,x::tl   -> (Apply2(Plus, x, y))::tl
  | _,x::tl   -> x::(addToPos (i-1) tl y) 

let rec reverse12 (context: context) (cont : targetSyn)  (expr : sourceSyn) : targetSyn * targetSyn * context = match expr with
  | Const c                   -> begin
                                  match typeTarget cont with 
                                  | Result.Ok(Type.Arrow(tyList,_)) ->
                                  let newVar,newTy = (Syntax.Var.fresh(), Type.Real) in 
                                  let newVarList = List.map (fun ty -> Syntax.Var.fresh(), ty) tyList in                  
                                  let newContVarList =  List.append newVarList [(newVar,newTy)] in
                                  let newCont = Fun(newContVarList, App(cont, varToSyn newVarList)) in
                                  Tuple[Const c; newCont], newCont, context
                                  | _ -> failwith "rad: the continuation should be a function"
                                  end
  | Var(x, ty)                -> begin
                                  match typeTarget cont with 
                                  | Result.Ok(Arrow(tyList,_)) ->
                                  let new_var, new_ty = Syntax.Var.fresh(), Type.sourceToTarget ty in  
                                  let newVarList = List.map (fun ty -> Syntax.Var.fresh(), ty) tyList in                          
                                  let newContVarList = List.append newVarList [(new_var, new_ty)] in
                                  let pos_x = getPos (x,ty) context in
                                  let newCont = Fun(newContVarList, 
                                                    App(cont,
                                                        addToPos pos_x (varToSyn newVarList) (Var(new_var, new_ty) )
                                                        )
                                                    ) 
                                  in
                                  Tuple[Var(x, new_ty); newCont], newCont, context
                                  | _ -> failwith "rad: the continuation should be a function"
                                  end
  | Apply1(op, expr)          -> begin
                                  match typeTarget cont,expr with
                                  | Result.Ok(Arrow(tyList,_)), Var(x, ty) ->
                                  let new_ty = Type.sourceToTarget ty in
                                  let pos_x = getPos (x, ty) context in
                                  let new_var = Syntax.Var.fresh() in 
                                  let newVarList = (List.map (fun ty -> Syntax.Var.fresh(), ty) tyList)  in                         
                                  let newContVarList =  List.append newVarList [(new_var, new_ty)] in
                                  let dop y = begin match op with
                                    | Cos     -> Apply1(Minus,Apply1(Sin, y))
                                    | Sin     -> Apply1(Cos, y)
                                    | Exp     -> Apply1(Exp, y)
                                    | Minus   -> Const (-1.)
                                    | Power 0 -> Const(0.)
                                    | Power n -> Apply2(Times, Const(float_of_int (n-1)),Apply1(Power(n-1),y))
                                    end
                                  in
                                  let partialOp = fun z -> Apply2(Times, dop (Var(x, new_ty)), z) in
                                  let newCont = Fun(newContVarList, 
                                                    App(cont,
                                                        (Var (new_var, new_ty) |> partialOp |> addToPos pos_x (varToSyn newVarList))
                                                        )
                                                    ) 
                                  in
                                  Tuple[Apply1(op, Var(x,new_ty)); newCont], newCont, context
                                  | _,_ -> failwith "rad: the continuation should be a function"
                                  end
  | Apply2(op, expr1, expr2)  -> begin
                                  match typeTarget cont,expr1,expr2 with 
                                  | Result.Ok(Arrow(tyList,_)), Var(x1, ty1), Var(x2, ty2) ->
                                  let new_ty1 = Type.sourceToTarget ty1 in
                                  let pos_x1 = getPos (x1, ty1) context in
                                  let new_ty2 = Type.sourceToTarget ty2 in
                                  let pos_x2 = getPos (x2, ty2) context in
                                  let new_var = Syntax.Var.fresh() in 
                                  let newVarList = (List.map (fun ty -> Syntax.Var.fresh(), ty) tyList) in                         
                                  let newContVarList =  List.append newVarList [(new_var, Real)] in
                                  let d1op _ y2 = begin
                                    match op with
                                    | Plus  -> Const(1.)
                                    | Times -> y2
                                    | Minus -> Const(1.)
                                    end
                                  in 
                                  let d2op y1 _ = begin
                                    match op with
                                    | Plus  -> Const(1.)
                                    | Times -> y1
                                    | Minus -> Const(-1.)
                                    end
                                  in
                                  let partial1Op = fun z -> Apply2(Times, d1op (Var(x1, new_ty1)) (Var(x2, new_ty2)), z) in
                                  let partial2Op = fun z -> Apply2(Times, d2op (Var(x1, new_ty1)) (Var(x2, new_ty2)), z) in  
                                  let newCont = Fun(newContVarList, 
                                                    App(cont,
                                                         Var (new_var, Real) |> partial1Op |> addToPos pos_x1 
                                                        (Var (new_var, Real) |> partial2Op |> addToPos pos_x2 (varToSyn newVarList))
                                                        )
                                                    ) 
                                  in
                                  Tuple[Apply2(op, Var(x1, new_ty1), Var(x2, new_ty2)); newCont], newCont, context
                                  | _,_,_ -> failwith "rad: the continuation should be a function"
                                  end
  | Let(x, ty, expr1, expr2)  -> let dexpr1, cont, context = reverse12 context cont expr1 in  
                                 let _, newContVar = dvar x in
                                 match typeTarget cont with 
                                  | Result.Error s         -> failwith (Printf.sprintf "rad: continuation ill-typed: %s" s) 
                                  | Result.Ok(newContType) ->
                                 let newCont = Var(newContVar, newContType) in
                                 let newContext = context @ [(x,ty)] in
                                 let dexpr2, newNewCont, context = reverse12 newContext newCont expr2 in
                                 NCase(dexpr1, [(x, Type.sourceToTarget ty); (newContVar, newContType)], dexpr2), newNewCont, context

let semiNaiveReverseAD (context: context) (expr: sourceSyn) : targetSyn =
  let new_var_List = List.map (fun (_,ty) -> Syntax.Var.fresh(), Type.sourceToTarget ty) context in 
  let id_cont = Fun(new_var_List, Tuple(List.map (fun (x, ty) -> Var(x, ty)) new_var_List)) in
  expr |> SourceAnf.weakAnf |> reverse12 context id_cont |> fun (a,_,_) -> a

(* To actually compute the gradient of a term, we need to initialize tangent variables as in imperative reverse-mode.
    Every tangent variable is initialized at 0 except from the last one which is the returned variable and is initialized at 1 *)
let rec initialize_rad list = match list with
 | []     -> failwith "initialize_rad: the gradient of a closed term won't give you much!" 
 | _::[] -> [Const 1.] 
 | _::tl -> (Const 0.)::initialize_rad tl

let grad (context: context) (expr: sourceSyn) : targetSyn =
  let new_var_List = List.map (fun (_,ty) -> Syntax.Var.fresh(), Type.sourceToTarget ty) context in 
  let id_cont = Fun(new_var_List, Tuple(List.map (fun (x, ty) -> Var(x, ty)) new_var_List)) in
  let dexpr, cont, _ = reverse12 context id_cont (SourceAnf.weakAnf expr) in
  match typeTarget cont with
    | Result.Error s                   -> failwith (Printf.sprintf "grad: continuation ill-typed: %s" s)
    | Result.Ok(Arrow(tyList,_)) ->
    let sensitivities = initialize_rad tyList in
    begin 
    match typeTarget dexpr with
      | Result.Ok(NProd[ty1;ty2]) ->
      let x,dx= dvar (Syntax.Var.fresh()) in
      NCase(dexpr,[(x,ty1);(dx,ty2)],App(Var(dx,ty2),sensitivities))
    | _                   -> failwith "grad: should return a pair"
    end
    | _ -> failwith "grad: continuation should have a function type"
end

(* This method computes mixed mode differentiation. It computes the gradient of a diretional derivative in one pass. 
    That is something of the form Hv. This is probably the best method for evaluating the whole Hessian if needed, and a very efficient way 
    to compute a whole column of the hessian in linear time.
    It works by first pushing a velocity forward to get something of the form <Grad f, v>, and then computing the gradient of this in a reverse pass. *)
module MixedJets = struct
  open Syntax.Source
  open Syntax.Operators
  open Syntax.Target
  
  type context = (Syntax.Var.t * sourceType) tuple
  
  let dvar var : Syntax.Var.t * Syntax.Var.t * Syntax.Var.t = let str, i = var in (str, i), ("d"^str, i), ("D"^str,i) 
  
  let dop2 y (op: op1) = match op with
    | Cos     -> Apply1(Minus, Apply1(Sin, y))
    | Sin     -> Apply1(Cos, y)
    | Exp     -> Apply1(Exp, y)
    | Minus   -> Const (-1.)
    | Power 0 -> Const(0.)
    | Power n -> Apply2(Times, Const(float_of_int (n-1)), Apply1(Power(n-1), y))

  (* \partial^2 op / partial x1 partial x1 *)
  let d11op _ _ (op: op2) = match op with
    | Plus  -> Const 0.
    | Minus -> Const 0.
    | Times -> Const 0.

  (* partial^2 op / partial x1 partial x2 *)
  let d12op _ _ (op: op2) = match op with
    | Plus  -> Const 0.
    | Minus -> Const 0.
    | Times -> Const 1.
    
  (* partial^2 op / partial x2 partial x1 *) 
  let d21op _ _ (op: op2) = match op with
    | Plus  -> Const 0.
    | Minus -> Const 0.
    | Times -> Const 1.

  (* partial^2 op / partial x2 partial x2 *)  
  let d22op _ _ (op: op2) = match op with
    | Plus  -> Const 0.
    | Minus -> Const 0.
    | Times -> Const 0.

  let getPos (x,ty) list = 
    let rec aux pos list = match list with
    | [] -> failwith "getPos: element not found"
    | (y,ty2)::tl -> if Syntax.Var.equal x y && Syntax.Source.equalTypes ty ty2 
                      then pos 
                      else aux (pos+1) tl
    in aux 0 list
  
  let rec addToPos i y list = match i, list with
    | _,[]      -> failwith "addToPos: no element at this position in the list"
    | 0,x::tl   -> (Apply2(Plus, x, y))::tl
    | _,x::tl   -> x::(addToPos (i-1) y tl) 
  
  let rec reverse12 (context: context) (cont : targetSyn)  (expr : sourceSyn) : targetSyn * targetSyn * context = match expr with
    | Const c                   -> begin
                                    match typeTarget cont with 
                                    | Result.Ok(Type.Arrow(tyList,_)) ->
                                    let newVar1, newTy1 = (Syntax.Var.fresh(), Type.Real) in
                                    let newVar2, newTy2 = (Syntax.Var.fresh(), Type.Real) in
                                    let newVarList1 = List.map (fun ty -> Syntax.Var.fresh(), ty) tyList in
                                    let newVarList2 = List.map (fun ty -> Syntax.Var.fresh(), ty) tyList in
                                    let newVarList = newVarList1@newVarList2 in                   
                                    let newContVarList = newVarList1@[(newVar1,newTy1)]@newVarList2@[(newVar2,newTy2)] in
                                    let newCont = Fun(newContVarList, App(cont, varToSyn newVarList)) in
                                    Tuple[Const c; Const 0.; newCont], newCont, context
                                    | _ -> failwith "rad: the continuation should be a function"
                                    end
    | Var(x, ty)                -> begin
                                    match typeTarget cont with 
                                    | Result.Ok(Arrow(tyList,_)) ->
                                    let x, dx, _ = dvar x in
                                    let newVar1, newTy1 = (Syntax.Var.fresh(), Type.sourceToTarget ty) in
                                    let newVar2, newTy2 = (Syntax.Var.fresh(), Type.sourceToTarget ty) in
                                    let n = List.length tyList in
                                    let newVarList1 = List.map (fun ty -> Syntax.Var.fresh(), ty) tyList in
                                    let newVarList2 = List.map (fun ty -> Syntax.Var.fresh(), ty) tyList in
                                    let newVarList = newVarList1@newVarList2 in                    
                                    let newContVarList = newVarList1@[(newVar1,newTy1)]@newVarList2@[(newVar2,newTy2)] in
                                    let pos_x = getPos (x,ty) context in
                                    let newCont = Fun(newContVarList, 
                                                      App(cont,
                                                          addToPos (pos_x+n) (Var(newVar2, newTy2))
                                                          (addToPos pos_x (Var(newVar1, newTy1)) (varToSyn newVarList)) 
                                                          )
                                                      ) 
                                    in
                                    Tuple[Var(x, newTy1); Var(dx, newTy1); newCont], newCont, context
                                    | _ -> failwith "rad: the continuation should be a function"
                                    end
    | Apply1(op, expr)          -> begin
                                    match typeTarget cont,expr with
                                    | Result.Ok(Arrow(tyList,_)), Var(x, ty) ->
                                    let x, dx, _ = dvar x in
                                    let newVar1, newTy1 = (Syntax.Var.fresh(), Type.sourceToTarget ty) in
                                    let newVar2, newTy2 = (Syntax.Var.fresh(), Type.sourceToTarget ty) in
                                    let n = List.length tyList in
                                    let newVarList1 = List.map (fun ty -> Syntax.Var.fresh(), ty) tyList in
                                    let newVarList2 = List.map (fun ty -> Syntax.Var.fresh(), ty) tyList in
                                    let newVarList = newVarList1@newVarList2 in  
                                    let pos_x = getPos (x, ty) context in                      
                                    let newContVarList = newVarList1@[(newVar1,newTy1)]@newVarList2@[(newVar2,newTy2)] in
                                    let partialOp = fun z -> Apply2(Times, dop (Var(x, newTy1)) op, z) in
                                    let partial2op = Apply2(Times, Apply2(Times, dop2 (Var(x,newTy1)) op, Var(newVar1, newTy1)), Var(dx, newTy1)) in
                                    let newCont = Fun(newContVarList, 
                                                      App(cont,
                                                           addToPos (pos_x+n) partial2op
                                                          (addToPos (pos_x+n) (partialOp (Var (newVar2, newTy2)))
                                                          (addToPos pos_x (partialOp (Var (newVar1, newTy1))) (varToSyn newVarList)))
                                                          )
                                                      )
                                    in
                                    let tangent = Apply2(Times, dop (Var(x, newTy1)) op, Var(dx, newTy1)) in 
                                    Tuple[Apply1(op, Var(x,newTy1)); tangent; newCont], newCont, context
                                    | _,_ -> failwith "rad: the continuation should be a function"
                                    end
    | Apply2(op, expr1, expr2)  -> begin
                                    match typeTarget cont,expr1,expr2 with 
                                    | Result.Ok(Arrow(tyList,_)), Var(x1, ty1), Var(x2, ty2) ->
                                    let x1, dx1, _ = dvar x1 in
                                    let x2, dx2, _ = dvar x2 in
                                    let newVar1, newTy1 = (Syntax.Var.fresh(), Type.sourceToTarget ty1) in
                                    let newVar2, newTy2 = (Syntax.Var.fresh(), Type.sourceToTarget ty1) in
                                    let n = List.length tyList in
                                    let newVarList1 = List.map (fun ty -> Syntax.Var.fresh(), ty) tyList in
                                    let newVarList2 = List.map (fun ty -> Syntax.Var.fresh(), ty) tyList in
                                    let newVarList = newVarList1@newVarList2 in  
                                    let newContVarList = newVarList1@[(newVar1,newTy1)]@newVarList2@[(newVar2,newTy2)] in
                                    let pos_x1 = getPos (x1, ty1) context in
                                    let pos_x2 = getPos (x2, ty2) context in
                                    let partial1Op = fun z -> Apply2(Times, d1op (Var(x1, newTy1)) (Var(x2, newTy2)) op, z) in
                                    let partial2Op = fun z -> Apply2(Times, d2op (Var(x1, newTy1)) (Var(x2, newTy2)) op, z) in 
                                    let secondPartialOp = fun dx -> fun z -> fun partial -> Apply2(Times,Apply2(Times,partial,dx),z) in
                                    let addFirstDerivatives =  varToSyn newVarList
                                                              |> addToPos (pos_x2) (partial2Op (Var (newVar1, Real)))
                                                              |> addToPos pos_x1  (partial1Op (Var(newVar1, Real)))
                                                              |> addToPos (pos_x2+n)  (partial2Op (Var(newVar2, Real)))
                                                              |> addToPos (pos_x1+n)  (partial1Op (Var(newVar2, Real)))
                                    in
                                    let addSecondDerivatives =  addFirstDerivatives 
                                                              |> addToPos (pos_x2+n) (secondPartialOp (Var(dx1,newTy1)) (Var(newVar1, Real)) (d11op (Var(x1,newTy1)) (Var(x2,newTy2)) op))
                                                              |> addToPos (pos_x2+n) (secondPartialOp (Var(dx2,newTy2)) (Var(newVar1, Real)) (d12op (Var(x1,newTy1)) (Var(x2,newTy2)) op))
                                                              |> addToPos (pos_x1+n) (secondPartialOp (Var(dx1,newTy1)) (Var(newVar1, Real)) (d21op (Var(x1,newTy1)) (Var(x2,newTy2)) op))
                                                              |> addToPos (pos_x1+n) (secondPartialOp (Var(dx2,newTy2)) (Var(newVar1, Real)) (d22op (Var(x1,newTy1)) (Var(x2,newTy2)) op))
                                    in
                                    let newCont = Fun(newContVarList, App(cont, addSecondDerivatives)) in
                                    let tangent = Apply2(Plus,
                                                          Apply2(Times, d1op (Var(x1, newTy1)) (Var(x2, newTy2)) op, Var(dx1, newTy1)),
                                                          Apply2(Times, d2op (Var(x1, newTy1)) (Var(x2, newTy2)) op, Var(dx2, newTy2)))  in
                                    Tuple[Apply2(op, Var(x1, newTy1), Var(x2, newTy2)); tangent ; newCont], newCont, context
                                    | _,_,_ -> failwith "rad: the continuation should be a function"
                                    end
    | Let(x, ty, expr1, expr2)  -> let dexpr1, cont, context = reverse12 context cont expr1 in  
                                   let x, dx, newContVar = dvar x in
                                   match typeTarget cont with 
                                    | Result.Error s         -> failwith (Printf.sprintf "rad: continuation ill-typed: %s" s) 
                                    | Result.Ok(newContType) ->
                                   let newCont = Var(newContVar, newContType) in
                                   let newContext = context @ [(x,ty)] in
                                   let dexpr2, newNewCont, context = reverse12 newContext newCont expr2 in
                                   NCase(dexpr1, [(x, Type.sourceToTarget ty); (dx, Type.sourceToTarget ty) ; (newContVar, newContType)], dexpr2), newNewCont, context
end  
