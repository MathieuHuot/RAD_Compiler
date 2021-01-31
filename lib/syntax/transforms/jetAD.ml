(* Prototype for Higher-Order Derivatives *)
(* See the paper A Geometric Theory of Higher-Order Automatic Differentiation for more information *)
open Syntax
open Operators

(* This method computes (1,2) velocities. *) 
module Jets12 = struct
open Source
(* TODO: might be wrong. *)
(* second derivative of binary operator *)
let dop2 x dx d2x (op: op1) = match op with
  | Cos     -> Target.Apply2(Minus, Target.Apply1(Minus, Target.Apply2(Times, Target.Apply1(Cos, x), dx)), Target.Apply2(Times, Target.Apply1(Sin, x), d2x))
  | Sin     -> Target.Apply2(Plus, Target.Apply1(Minus, Target.Apply2(Times, Target.Apply1(Sin, x), dx)), Target.Apply2(Times, Target.Apply1(Cos, x), d2x))
  | Exp     -> Target.Apply2(Plus, Target.Apply2(Times, Target.Apply1(Exp, x), dx), Target.Apply2(Times, Target.Apply1(Exp, x), d2x))
  | Minus   -> Target.Apply1(Minus, d2x)
  | Power 0 -> Target.Const(0.)
  | Power 1 -> d2x
  | Power n -> Target.Apply2(Plus,
                      Target.Apply2(Times, Target.Apply2(Times, Target.Const(float_of_int(n*(n-1))), Target.Apply1(Power(n-2), x)), dx),
                      Target.Apply2(Times, Target.Apply2(Times, Target.Const(float_of_int n), Target.Apply1(Power(n-1), x)), d2x))
             
let d2op2 x dx d2x y dy d2y  (op: op2) = match op with
  | Plus  -> Target.Apply2(Plus, d2x, d2y)
  | Minus -> Target.Apply2(Minus, d2x, d2y)
  | Times -> Target.Apply2(Plus, Target.Apply2(Plus, Target.Apply2(Times, d2x, y), Target.Apply2(Times, x, d2y)), Target.Apply2(Times, Target.Const 2., Target.Apply2(Times, dx, dy)))

let rec forwardAD12Type (ty : Type.t) : Target.Type.t = match ty with
  | Real          -> Target.Type.NProd([Target.Type.Real; Target.Type.Real; Target.Type.Real])
  | Prod(ty1,ty2) -> Target.Type.NProd [forwardAD12Type ty1; forwardAD12Type ty2]
  | Array(_, _)   -> failwith "TODO"

let rec forward12AD (expr: t) : Target.t = match expr with
| Const c               ->  Target.Tuple([Target.Const c; Target.Const 0.; Target.Const 0.])
| Var(x,ty)             ->  let x, dx, d2x = Var.dvar2 x in
                            let ty = Target.Type.from_source ty in
                            Target.Tuple([Target.Var(x, ty); Target.Var(dx, ty); Target.Var(d2x, ty)])
| Apply1(op,expr)       ->  let y, dy, d2y = Var.dvar2 (Var.fresh()) in
                            let ty = Target.Type.Real in
                            let exprD = forward12AD expr in
                            let e = Target.Apply1(op, Target.Var(y, ty)) in
                            let de = Target.Apply2(Times, Target.dop op (Target.Var(y, ty)), Target.Var(dy, ty)) in 
                            let d2e = dop2 (Target.Var(y, ty)) (Target.Var(dy, ty)) (Target.Var(d2y, ty)) op in
                            Target.NCase(exprD, [(y, ty); (dy, ty); (d2y, ty)], Target.Tuple([e; de; d2e]))
| Apply2(op,expr1,expr2)->  let x, dx, d2x = Var.dvar2 (Var.fresh()) in
                            let y, dy, d2y = Var.dvar2 (Var.fresh()) in
                            let ty = Target.Type.Real in
                            let expr1D = forward12AD expr1 in
                            let expr2D = forward12AD expr2 in
                            let e = Target.Apply2(op, Target.Var(x, ty), Target.Var(y, ty)) in
                            let de = Target.Apply2(Plus,
                                            Target.Apply2(Times, Target.d1op op (Target.Var(x, ty)) (Target.Var(y, ty)), (Target.Var(dx, ty))),
                                            Target.Apply2(Times, Target.d2op op (Target.Var(x, ty)) (Target.Var(y, ty)), (Target.Var(dy, ty)))) in
                            let d2e = d2op2 (Target.Var(x, ty)) (Target.Var(dx, ty)) (Target.Var(d2x, ty)) (Target.Var(y, ty)) (Target.Var(dy, ty)) (Target.Var(d2y, ty)) op in
                            Target.NCase(expr1D, [(x, ty); (dx, ty); (d2x, ty)],
                            Target.NCase(expr2D, [(y, ty); (dy, ty); (d2y, ty)], 
                            Target.Tuple([e; de; d2e])))
| Let(y,ty,expr1,expr2) ->  let expr1D = forward12AD expr1 in
                            let expr2D = forward12AD expr2 in
                            let y, dy, d2y = Var.dvar2 y in
                            let ty = Target.Type.from_source ty in
                            Target.NCase(expr1D, [(y, ty); (dy, ty); (d2y, ty)], expr2D)
| _ -> failwith "TODO"

(* Compute the list d2f/dx2 for all variables x from the context *)                           
let secondPartial context expr = 
  let dexpr = forward12AD expr in
  let optiDexpr = Optimisation.T.fullOpti dexpr in
  List.map 
      (fun (x,_,_) -> List.fold_left 
      (fun acc (y, ty2, expr2) -> let y, dy, d2y = Var.dvar2 y in
      let f = if (Var.equal x y) then Target.subst dy ty2 (Target.Const(1.)) else Target.subst dy ty2 (Target.Const(0.)) in
      f (Target.subst d2y ty2 (Target.Const 0.) (Target.subst y ty2 expr2 acc))) optiDexpr context) 
      context

(* Compute the list d2f/dxi dxj for all xi,xj in the context *)
let mixedPartial context expr = 
  let n = List.length context in
  let arrayContext = Array.of_list (List.map (fun (x,_,_) -> x) context) in
  let dexpr = forward12AD expr in 
  let optiDexpr = Optimisation.T.fullOpti dexpr in
  let mixedDerivatives = Array.make_matrix n n (Target.Const 0.) in
  for i=0 to (n-1) do
    for j=0 to (n-1) do
      mixedDerivatives.(i).(j) <- 
        List.fold_left 
          (fun acc (y,ty2,expr2) -> let y,dy,d2y = Var.dvar2 y in
          let f = if (Var.equal arrayContext.(i) y) || (Var.equal arrayContext.(j) y) 
          then Target.subst dy ty2 (Target.Const(1.)) 
          else Target.subst dy ty2 (Target.Const(0.)) in
          f (Target.subst d2y ty2 (Target.Const 0.) (Target.subst y ty2 expr2 acc))
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
          Optimisation.T.fullOpti 
          (Target.Apply2(Minus, mixedDerivatives.(i).(j), 
                        Target.Apply2(Plus, secondPartial.(i), secondPartial.(j)))
          )
      done
    done;
    mixedDerivatives
end

(* This method computes (2,2) velocities. *) 
module Jets22 = struct
open Source
open Operators

let rec forwardAD22Type (ty : Type.t) : Target.Type.t = match ty with
  | Real          -> Target.Type.NProd([Target.Type.Real;Target.Type.Real;Target.Type.Real;Target.Type.Real])
  | Prod(ty1,ty2) -> Target.Type.NProd [forwardAD22Type ty1;forwardAD22Type ty2]
  | Array(_, _)   -> failwith "TODO"

let rec forward22AD (expr: t) : Target.t = match expr with
| Const c               ->  Target.Tuple([Target.Const c; Target.Const 0.; Target.Const 0.; Target.Const 0.])
| Var(x,ty)             ->  let x, d1x, d2x, ddx = Var.dvar22 x in
                            let ty = Target.Type.from_source ty in
                            Target.Tuple([Target.Var(x, ty); Target.Var(d1x, ty); Target.Var(d2x, ty); Target.Var(ddx, ty)])
| Apply1(op,expr)       ->  let y, d1y, d2y, ddy = Var.dvar22 (Var.fresh()) in
                            let ty = Target.Type.Real in
                            let exprD = forward22AD expr in
                            let e = Target.Apply1(op, Target.Var(y, ty)) in
                            let d1e = Target.Apply2(Times, Target.dop op (Target.Var(y, ty)), Target.Var(d1y, ty)) in
                            let d2e = Target.Apply2(Times, Target.dop op (Target.Var(y, ty)), Target.Var(d2y, ty)) in  
                            let dde = Target.dop22 op (Target.Var(y, ty)) (Target.Var(d1y, ty)) (Target.Var(d2y, ty)) (Target.Var(ddy, ty)) in
                            Target.NCase(exprD,[(y, ty); (d1y, ty); (d2y, ty); (ddy, ty)], Target.Tuple([e; d1e; d2e; dde]))
| Apply2(op,expr1,expr2)->  let x, d1x, d2x, ddx = Var.dvar22 (Var.fresh()) in
                            let y, d1y, d2y, ddy = Var.dvar22 (Var.fresh()) in
                            (* comparing notation to the paper cited above *)
                            (* x is first index, y is second, d1 is for du, d2 for dv, dd for dudv *)
                            let ty = Target.Type.Real in
                            let expr1D = forward22AD expr1 in
                            let expr2D = forward22AD expr2 in
                            let e = Target.Apply2(op, Target.Var(x, ty), Target.Var(y, ty)) in
                            let d1e = Target.Apply2(Plus,
                                            Target.Apply2(Times, Target.d1op op (Target.Var(x, ty)) (Target.Var(y, ty)), (Target.Var(d1x, ty))),
                                            Target.Apply2(Times, Target.d2op op (Target.Var(x, ty)) (Target.Var(y, ty)), (Target.Var(d1y, ty)))) in
                            let d2e = Target.Apply2(Plus,
                                            Target.Apply2(Times, Target.d1op op (Target.Var(x, ty)) (Target.Var(y, ty)), (Target.Var(d2x, ty))),
                                            Target.Apply2(Times, Target.d2op op (Target.Var(x, ty)) (Target.Var(y, ty)), (Target.Var(d2y, ty)))) in                
                            let dde = Target.d2op22 op (Target.Var(x, ty)) (Target.Var(d1x, ty)) (Target.Var(d2x, ty)) (Target.Var(ddx, ty)) 
                                             (Target.Var(y, ty)) (Target.Var(d1y, ty)) (Target.Var(d2y, ty)) (Target.Var(ddy, ty)) in
                            Target.NCase(expr1D, [(x, ty); (d1x, ty); (d2x, ty);  (ddx, ty)],
                            Target.NCase(expr2D, [(y, ty); (d1y, ty); (d2y, ty);  (ddy, ty)], 
                            Target.Tuple([e; d1e; d2e; dde])))
| Let(y,ty,expr1,expr2) ->  let expr1D = forward22AD expr1 in
                            let expr2D = forward22AD expr2 in
                            let y, d1y, d2y, ddy = Var.dvar22 y in
                            let ty = Target.Type.from_source ty in
                            Target.NCase(expr1D, [(y, ty); (d1y, ty); (d2y, ty);  (ddy, ty)], expr2D)
| _ -> failwith "TODO"  
end

(* This method computes (3,3) velocities. *) 
module Jets33 = struct
open Source
open Operators

let rec forwardAD33Type (ty : Type.t) : Target.Type.t = match ty with
  | Real          -> Target.Type.NProd([Target.Type.Real; Target.Type.Real; Target.Type.Real; Target.Type.Real; Target.Type.Real; Target.Type.Real; Target.Type.Real; Target.Type.Real])
  | Prod(ty1,ty2) -> Target.Type.NProd [forwardAD33Type ty1;forwardAD33Type ty2]
  | Array(_, _)   -> failwith "TODO"

(* third derivative of unary operator *) 
let dop33 x d1x d2x ddx (op: op1) = match op with
  | Cos     -> Target.Apply2(Minus, Target.Apply1(Minus, Target.Apply2(Times, Target.Apply1(Cos, x), Target.Apply2(Times, d1x, d2x))), Target.Apply2(Times,Target.Apply1(Sin, x), ddx))
  | Sin     -> Target.Apply2(Plus, Target.Apply1(Minus, Target.Apply2(Times, Target.Apply1(Sin, x), Target.Apply2(Times, d1x, d2x))), Target.Apply2(Times, Target.Apply1(Cos, x), ddx))
  | Exp     -> Target.Apply2(Plus, Target.Apply2(Times, Target.Apply1(Exp, x), Target.Apply2(Times, d1x, d2x)), Target.Apply2(Times, Target.Apply1(Exp, x), ddx))
  | Minus   -> Target.Apply1(Minus, ddx)
  | Power 0 -> Target.Const(0.)
  | Power 1 -> ddx
  | Power n -> Target.Apply2(Plus,
                      Target.Apply2(Times, Target.Apply2(Times, Target.Const(float_of_int(n*(n-1))), Target.Apply1(Power(n-2),x)), Target.Apply2(Times, d1x, d2x)),
                      Target.Apply2(Times, Target.Apply2(Times, Target.Const(float_of_int n), Target.Apply1(Power(n-1),x)), ddx))

(* third derivative of binary operator *)                     
let d2op33 x d1x d2x d3x dd1x dd2x dd3x dddx y d1y d2y d3y dd1y dd2y dd3y dddy (op: op2) = match op with
  | Plus  -> Target.Apply2(Plus, dddx, dddy)
  | Minus -> Target.Apply2(Minus, dddx, dddy)
  | Times -> Target.Apply2(Plus,
                    Target.Apply2(Plus, Target.Apply2(Times, dddx, y), Target.Apply2(Times, x, dddy)),
                    Target.Apply2(Plus,
                            Target.Apply2(Plus, 
                                    Target.Apply2(Plus, Target.Apply2(Plus, Target.Apply2(Times, d2x, dd3x), Target.Apply2(Times, d1x, dd2x)), Target.Apply2(Times, d3x, dd1x)), 
                                    Target.Apply2(Plus, Target.Apply2(Plus, Target.Apply2(Times, d2x, dd3y), Target.Apply2(Times, d1x, dd2y)), Target.Apply2(Times, d3x, dd1y))),
                            Target.Apply2(Plus, 
                                    Target.Apply2(Plus, Target.Apply2(Plus, Target.Apply2(Times, d2y, dd3x), Target.Apply2(Times, d1y, dd2x)), Target.Apply2(Times, d3y, dd1x)), 
                                    Target.Apply2(Plus, Target.Apply2(Plus, Target.Apply2(Times, d2y, dd3y), Target.Apply2(Times, d1y, dd2y)), Target.Apply2(Times, d3y, dd1y)))))

let rec forward33AD (expr: t) : Target.t = match expr with
| Const c               ->  Target.Tuple([Target.Const c; Target.Const 0.; Target.Const 0.; Target.Const 0.; Target.Const 0.; Target.Const 0.; Target.Const 0.; Target.Const 0.])
| Var(x,ty)             ->  let x, d1x, d2x, d3x, dd1x, dd2x, dd3x, dddx = Var.dvar33 x in
                            let ty = Target.Type.from_source ty in
                            Target.Tuple([Target.Var(x, ty); Target.Var(d1x, ty); Target.Var(d2x, ty); Target.Var(d3x, ty); Target.Var(dd1x, ty); Target.Var(dd2x, ty); Target.Var(dd3x, ty); Target.Var(dddx, ty);])
| Apply1(op,expr)       ->  let y, d1y, d2y, d3y, dd1y, dd2y, dd3y, dddy = Var.dvar33 (Var.fresh()) in
                            let ty = Target.Type.Real in
                            let exprD = forward33AD expr in
                            let e = Target.Apply1(op, Target.Var(y, ty)) in
                            let d1e = Target.Apply2(Times, Target.dop op (Target.Var(y, ty)), Target.Var(d1y, ty)) in
                            let d2e = Target.Apply2(Times, Target.dop op (Target.Var(y, ty)), Target.Var(d2y, ty)) in
                            let d3e = Target.Apply2(Times, Target.dop op (Target.Var(y, ty)), Target.Var(d3y, ty)) in   
                            let dd1e = Target.dop22 op(Target.Var(y, ty)) (Target.Var(d2y, ty)) (Target.Var(d1y, ty)) (Target.Var(dd1y, ty)) in
                            let dd2e = Target.dop22 op(Target.Var(y, ty)) (Target.Var(d2y, ty)) (Target.Var(d3y, ty)) (Target.Var(dd2y, ty)) in
                            let dd3e = Target.dop22 op (Target.Var(y, ty)) (Target.Var(d1y, ty)) (Target.Var(d3y, ty)) (Target.Var(dd3y, ty)) in
                            let ddde = dop33 (Target.Var(y, ty)) (Target.Var(d1y, ty)) (Target.Var(d2y, ty)) (Target.Var(dddy, ty)) op in
                            Target.NCase(exprD, 
                                  [(y, ty); (d1y, ty); (d2y, ty); (d3y, ty); (dd1y, ty); (dd2y, ty); (dd3y, ty);  (dddy, ty)],  
                                  Target.Tuple([e; d1e; d2e; d3e; dd1e; dd2e; dd3e; ddde]))
| Apply2(op,expr1,expr2)->  let x, d1x, d2x, d3x, dd1x, dd2x, dd3x, dddx = Var.dvar33 (Var.fresh()) in
                            let y, d1y, d2y, d3y, dd1y, dd2y, dd3y, dddy = Var.dvar33 (Var.fresh()) in
                            let ty = Target.Type.Real in
                            let expr1D = forward33AD expr1 in
                            let expr2D = forward33AD expr2 in
                            let e = Target.Apply2(op, Target.Var(x, ty), Target.Var(y, ty)) in
                            let d1e = Target.Apply2(Plus,
                                            Target.Apply2(Times, Target.d1op op (Target.Var(x, ty)) (Target.Var(y, ty)), (Target.Var(d1x, ty))),
                                            Target.Apply2(Times, Target.d2op op (Target.Var(x, ty)) (Target.Var(y, ty)), (Target.Var(d1y, ty)))) in
                            let d2e = Target.Apply2(Plus,
                                            Target.Apply2(Times, Target.d1op op(Target.Var(x, ty)) (Target.Var(y, ty)), (Target.Var(d2x, ty))),
                                            Target.Apply2(Times, Target.d2op op (Target.Var(x, ty)) (Target.Var(y, ty)), (Target.Var(d2y, ty)))) in
                            let d3e = Target.Apply2(Plus,
                                            Target.Apply2(Times, Target.d1op op (Target.Var(x, ty)) (Target.Var(y, ty)), (Target.Var(d3x, ty))),
                                            Target.Apply2(Times, Target.d2op op (Target.Var(x, ty)) (Target.Var(y, ty)), (Target.Var(d3y, ty)))) in                  
                            let dd1e = Target.d2op22 op (Target.Var(x, ty)) (Target.Var(d1x, ty)) (Target.Var(d2x, ty)) (Target.Var(dd1x, ty)) 
                                              (Target.Var(y, ty)) (Target.Var(d1y, ty)) (Target.Var(d2y, ty)) (Target.Var(dd1y, ty)) 
                                              in
                            let dd2e = Target.d2op22 op (Target.Var(x, ty)) (Target.Var(d1x, ty)) (Target.Var(d2x, ty)) (Target.Var(dd2x, ty)) 
                                              (Target.Var(y, ty)) (Target.Var(d1y, ty)) (Target.Var(d2y, ty)) (Target.Var(dd2y, ty)) 
                                              in
                            let dd3e = Target.d2op22 op (Target.Var(x, ty)) (Target.Var(d1x, ty)) (Target.Var(d2x, ty)) (Target.Var(dd3x, ty)) 
                                              (Target.Var(y, ty)) (Target.Var(d1y, ty)) (Target.Var(d2y, ty)) (Target.Var(dd3y, ty)) 
                                              in
                            let ddde = d2op33 (Target.Var(x, ty)) (Target.Var(d1x, ty)) (Target.Var(d2x, ty)) (Target.Var(d3x, ty)) (Target.Var(dd1x, ty)) (Target.Var(dd2x, ty)) (Target.Var(dd3x, ty)) (Target.Var(dddx, ty))
                                              (Target.Var(y, ty)) (Target.Var(d1y, ty)) (Target.Var(d2y, ty)) (Target.Var(d3y, ty)) (Target.Var(dd1y, ty)) (Target.Var(dd2y, ty)) (Target.Var(dd3y, ty)) (Target.Var(dddy, ty))
                                              op in            
                            Target.NCase(expr1D, [(x, ty); (d1x, ty); (d2x, ty); (d3x, ty); (dd1x, ty); (dd2x, ty); (dd3x, ty);  (dddx, ty)],
                            Target.NCase(expr2D, [(y, ty); (d1y, ty); (d2y, ty); (d3y, ty); (dd1y, ty); (dd2y, ty); (dd3y, ty);  (dddy, ty)], 
                            Target.Tuple([e; d1e; d2e; d3e; dd1e; dd2e; dd3e; ddde])))
| Let(y,ty,expr1,expr2) ->  let expr1D = forward33AD expr1 in
                            let expr2D = forward33AD expr2 in
                            let y, d1y, d2y, d3y, dd1y, dd2y, dd3y, dddy = Var.dvar33 y in
                            let ty = Target.Type.from_source ty in
                            Target.NCase(expr1D, [(y, ty); (d1y, ty); (d2y, ty); (d3y, ty); (dd1y, ty); (dd2y, ty); (dd3y, ty);  (dddy, ty)], expr2D)
| _ -> failwith "TODO"  
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
open Anf

type context = (Syntax.Var.t * Type.t) Target.tuple

let dvar var : Syntax.Var.t *  Syntax.Var.t = let str, i = var in (str, i), ("d"^str, i)

let getPos (x,ty) list = 
  let rec aux pos list = match list with
  | [] -> failwith "getPos: element not found"
  | (y,ty2)::tl -> if Syntax.Var.equal x y && Syntax.Source.Type.equal ty ty2 
                    then pos 
                    else aux (pos+1) tl
  in aux 0 list

let rec addToPos i list y = match i, list with
  | _,[]      -> failwith "addToPos: no element at this position in the list"
  | 0,x::tl   -> (Target.Apply2(Plus, x, y))::tl
  | _,x::tl   -> x::(addToPos (i-1) tl y) 

let rec reverse12 (context: context) (cont : Target.t)  (expr : t) : Target.t * Target.t * context = match expr with
  | Const c                   -> begin
                                  match Target.inferType cont with 
                                  | Result.Ok(Target.Type.Arrow(tyList,_)) ->
                                  let newVar,newTy = (Syntax.Var.fresh(), Target.Type.Real) in 
                                  let newVarList = List.map (fun ty -> Syntax.Var.fresh(), ty) tyList in                  
                                  let newContVarList =  List.append newVarList [(newVar,newTy)] in
                                  let newCont = Target.Fun(newContVarList, Target.App(cont, Target.varToSyn newVarList)) in
                                  Target.Tuple[Target.Const c; newCont], newCont, context
                                  | _ -> failwith "rad: the continuation should be a function"
                                  end
  | Var(x, ty)                -> begin
                                  match Target.inferType cont with 
                                  | Result.Ok(Target.Type.Arrow(tyList,_)) ->
                                  let new_var, new_ty = Syntax.Var.fresh(), Target.Type.from_source ty in  
                                  let newVarList = List.map (fun ty -> Syntax.Var.fresh(), ty) tyList in                          
                                  let newContVarList = List.append newVarList [(new_var, new_ty)] in
                                  let pos_x = getPos (x,ty) context in
                                  let newCont = Target.Fun(newContVarList, 
                                                    Target.App(cont,
                                                        addToPos pos_x (Target.varToSyn newVarList) (Target.Var(new_var, new_ty) )
                                                        )
                                                    ) 
                                  in
                                  Target.Tuple[Target.Var(x, new_ty); newCont], newCont, context
                                  | _ -> failwith "rad: the continuation should be a function"
                                  end
  | Apply1(op, expr)          -> begin
                                  match Target.inferType cont,expr with
                                  | Result.Ok(Target.Type.Arrow(tyList,_)), Var(x, ty) ->
                                  let new_ty = Target.Type.from_source ty in
                                  let pos_x = getPos (x, ty) context in
                                  let new_var = Syntax.Var.fresh() in 
                                  let newVarList = (List.map (fun ty -> Syntax.Var.fresh(), ty) tyList)  in                         
                                  let newContVarList =  List.append newVarList [(new_var, new_ty)] in
                                  let partialOp = fun z -> Target.Apply2(Times, Target.dop op (Target.Var(x, new_ty)), z) in
                                  let newCont = Target.Fun(newContVarList, 
                                                    Target.App(cont,
                                                        (Target.Var (new_var, new_ty) |> partialOp |> addToPos pos_x (Target.varToSyn newVarList))
                                                        )
                                                    ) 
                                  in
                                  Target.Tuple[Target.Apply1(op, Target.Var(x,new_ty)); newCont], newCont, context
                                  | _,_ -> failwith "rad: the continuation should be a function"
                                  end
  | Apply2(op, expr1, expr2)  -> begin
                                  match Target.inferType cont,expr1,expr2 with 
                                  | Result.Ok(Target.Type.Arrow(tyList,_)), Var(x1, ty1), Var(x2, ty2) ->
                                  let new_ty1 = Target.Type.from_source ty1 in
                                  let pos_x1 = getPos (x1, ty1) context in
                                  let new_ty2 = Target.Type.from_source ty2 in
                                  let pos_x2 = getPos (x2, ty2) context in
                                  let new_var = Syntax.Var.fresh() in 
                                  let newVarList = (List.map (fun ty -> Syntax.Var.fresh(), ty) tyList) in                         
                                  let newContVarList =  List.append newVarList [(new_var, Target.Type.Real)] in
                                  let partial1Op = fun z -> Target.Apply2(Times, Target.d1op op (Target.Var(x1, new_ty1)) (Target.Var(x2, new_ty2)), z) in
                                  let partial2Op = fun z -> Target.Apply2(Times, Target.d2op op (Target.Var(x1, new_ty1)) (Target.Var(x2, new_ty2)), z) in  
                                  let newCont = Target.Fun(newContVarList, 
                                                    Target.App(cont,
                                                         Target.Var (new_var, Target.Type.Real) |> partial1Op |> addToPos pos_x1 
                                                        (Target.Var (new_var, Target.Type.Real) |> partial2Op |> addToPos pos_x2 (Target.varToSyn newVarList))
                                                        )
                                                    ) 
                                  in
                                  Target.Tuple[Target.Apply2(op, Target.Var(x1, new_ty1), Target.Var(x2, new_ty2)); newCont], newCont, context
                                  | _,_,_ -> failwith "rad: the continuation should be a function"
                                  end
  | Let(x, ty, expr1, expr2)  -> begin let dexpr1, cont, context = reverse12 context cont expr1 in  
                                 let _, newContVar = dvar x in
                                 match Target.inferType cont with 
                                  | Result.Error s         -> failwith (Printf.sprintf "rad: continuation ill-typed: %s" s) 
                                  | Result.Ok(newContType) ->
                                 let newCont = Target.Var(newContVar, newContType) in
                                 let newContext = context @ [(x,ty)] in
                                 let dexpr2, newNewCont, context = reverse12 newContext newCont expr2 in
                                 Target.NCase(dexpr1, [(x, Target.Type.from_source ty); (newContVar, newContType)], dexpr2), newNewCont, context end
| _ -> failwith "TODO"

let semiNaiveReverseAD (context: context) (expr: t) : Target.t =
  let new_var_List = List.map (fun (_,ty) -> Syntax.Var.fresh(), Target.Type.from_source ty) context in 
  let id_cont = Target.Fun(new_var_List, Target.Tuple(List.map (fun (x, ty) -> Target.Var(x, ty)) new_var_List)) in
  expr |> SourceAnf.weakAnf |> reverse12 context id_cont |> fun (a,_,_) -> a

(* To actually compute the gradient of a term, we need to initialize tangent variables as in imperative reverse-mode.
    Every tangent variable is initialized at 0 except from the last one which is the returned variable and is initialized at 1 *)
let rec initialize_rad list = match list with
 | []     -> failwith "initialize_rad: the gradient of a closed term won't give you much!" 
 | _::[] -> [Target.Const 1.] 
 | _::tl -> (Target.Const 0.)::initialize_rad tl

let grad (context: context) (expr: t) : Target.t =
  let new_var_List = List.map (fun (_,ty) -> Syntax.Var.fresh(), Target.Type.from_source ty) context in 
  let id_cont = Target.Fun(new_var_List, Target.Tuple(List.map (fun (x, ty) -> Target.Var(x, ty)) new_var_List)) in
  let dexpr, cont, _ = reverse12 context id_cont (SourceAnf.weakAnf expr) in
  match Target.inferType cont with
    | Result.Error s                   -> failwith (Printf.sprintf "grad: continuation ill-typed: %s" s)
    | Result.Ok(Target.Type.Arrow(tyList,_)) ->
    let sensitivities = initialize_rad tyList in
    begin 
    match Target.inferType dexpr with
      | Result.Ok(Target.Type.NProd[ty1;ty2]) ->
      let x,dx= dvar (Syntax.Var.fresh()) in
      Target.NCase(dexpr,[(x,ty1);(dx,ty2)],Target.App(Target.Var(dx,ty2),sensitivities))
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
  
  type context = (Syntax.Var.t * Type.t) Target.tuple
  
  let dvar var : Syntax.Var.t * Syntax.Var.t * Syntax.Var.t = let str, i = var in (str, i), ("d"^str, i), ("D"^str,i) 
  
  let getPos (x,ty) list = 
    let rec aux pos list = match list with
    | [] -> failwith "getPos: element not found"
    | (y,ty2)::tl -> if Syntax.Var.equal x y && Syntax.Source.Type.equal ty ty2 
                      then pos 
                      else aux (pos+1) tl
    in aux 0 list
  
  let rec addToPos i y list = match i, list with
    | _,[]      -> failwith "addToPos: no element at this position in the list"
    | 0,x::tl   -> (Target.Apply2(Plus, x, y))::tl
    | _,x::tl   -> x::(addToPos (i-1) y tl) 
  
  let rec reverse12 (context: context) (cont : Target.t)  (expr : t) : Target.t * Target.t * context = match expr with
    | Const c                   -> begin
                                    match Target.inferType cont with 
                                    | Result.Ok(Target.Type.Arrow(tyList,_)) ->
                                    let newVar1, newTy1 = (Syntax.Var.fresh(), Target.Type.Real) in
                                    let newVar2, newTy2 = (Syntax.Var.fresh(), Target.Type.Real) in
                                    let newVarList1 = List.map (fun ty -> Syntax.Var.fresh(), ty) tyList in
                                    let newVarList2 = List.map (fun ty -> Syntax.Var.fresh(), ty) tyList in
                                    let newVarList = newVarList1@newVarList2 in                   
                                    let newContVarList = newVarList1@[(newVar1,newTy1)]@newVarList2@[(newVar2,newTy2)] in
                                    let newCont = Target.Fun(newContVarList, Target.App(cont, Target.varToSyn newVarList)) in
                                    Target.Tuple[Target.Const c; Target.Const 0.; newCont], newCont, context
                                    | _ -> failwith "rad: the continuation should be a function"
                                    end
    | Var(x, ty)                -> begin
                                    match Target.inferType cont with 
                                    | Result.Ok(Target.Type.Arrow(tyList,_)) ->
                                    let x, dx, _ = dvar x in
                                    let newVar1, newTy1 = (Syntax.Var.fresh(), Target.Type.from_source ty) in
                                    let newVar2, newTy2 = (Syntax.Var.fresh(), Target.Type.from_source ty) in
                                    let n = List.length tyList in
                                    let newVarList1 = List.map (fun ty -> Syntax.Var.fresh(), ty) tyList in
                                    let newVarList2 = List.map (fun ty -> Syntax.Var.fresh(), ty) tyList in
                                    let newVarList = newVarList1@newVarList2 in                    
                                    let newContVarList = newVarList1@[(newVar1,newTy1)]@newVarList2@[(newVar2,newTy2)] in
                                    let pos_x = getPos (x,ty) context in
                                    let newCont = Target.Fun(newContVarList, 
                                                      Target.App(cont,
                                                          addToPos (pos_x+n) (Target.Var(newVar2, newTy2))
                                                          (addToPos pos_x (Target.Var(newVar1, newTy1)) (Target.varToSyn newVarList)) 
                                                          )
                                                      ) 
                                    in
                                    Target.Tuple[Target.Var(x, newTy1); Target.Var(dx, newTy1); newCont], newCont, context
                                    | _ -> failwith "rad: the continuation should be a function"
                                    end
    | Apply1(op, expr)          -> begin
                                    match Target.inferType cont,expr with
                                    | Result.Ok(Target.Type.Arrow(tyList,_)), Var(x, ty) ->
                                    let x, dx, _ = dvar x in
                                    let newVar1, newTy1 = (Syntax.Var.fresh(), Target.Type.from_source ty) in
                                    let newVar2, newTy2 = (Syntax.Var.fresh(), Target.Type.from_source ty) in
                                    let n = List.length tyList in
                                    let newVarList1 = List.map (fun ty -> Syntax.Var.fresh(), ty) tyList in
                                    let newVarList2 = List.map (fun ty -> Syntax.Var.fresh(), ty) tyList in
                                    let newVarList = newVarList1@newVarList2 in  
                                    let pos_x = getPos (x, ty) context in                      
                                    let newContVarList = newVarList1@[(newVar1,newTy1)]@newVarList2@[(newVar2,newTy2)] in
                                    let partialOp = fun z -> Target.Apply2(Times, Target.dop op (Target.Var(x, newTy1)), z) in
                                    let partial2op = Target.Apply2(Times, Target.Apply2(Times, Target.ddop op (Target.Var(x,newTy1)), Target.Var(newVar1, newTy1)), Target.Var(dx, newTy1)) in
                                    let newCont = Target.Fun(newContVarList, 
                                                      Target.App(cont,
                                                           addToPos (pos_x+n) partial2op
                                                          (addToPos (pos_x+n) (partialOp (Target.Var (newVar2, newTy2)))
                                                          (addToPos pos_x (partialOp (Target.Var (newVar1, newTy1))) (Target.varToSyn newVarList)))
                                                          )
                                                      )
                                    in
                                    let tangent = Target.Apply2(Times, Target.dop op (Target.Var(x, newTy1)), Target.Var(dx, newTy1)) in 
                                    Target.Tuple[Target.Apply1(op, Target.Var(x,newTy1)); tangent; newCont], newCont, context
                                    | _,_ -> failwith "rad: the continuation should be a function"
                                    end
    | Apply2(op, expr1, expr2)  -> begin
                                    match Target.inferType cont,expr1,expr2 with 
                                    | Result.Ok(Target.Type.Arrow(tyList,_)), Var(x1, ty1), Var(x2, ty2) ->
                                    let x1, dx1, _ = dvar x1 in
                                    let x2, dx2, _ = dvar x2 in
                                    let newVar1, newTy1 = (Syntax.Var.fresh(), Target.Type.from_source ty1) in
                                    let newVar2, newTy2 = (Syntax.Var.fresh(), Target.Type.from_source ty1) in
                                    let n = List.length tyList in
                                    let newVarList1 = List.map (fun ty -> Syntax.Var.fresh(), ty) tyList in
                                    let newVarList2 = List.map (fun ty -> Syntax.Var.fresh(), ty) tyList in
                                    let newVarList = newVarList1@newVarList2 in  
                                    let newContVarList = newVarList1@[(newVar1,newTy1)]@newVarList2@[(newVar2,newTy2)] in
                                    let pos_x1 = getPos (x1, ty1) context in
                                    let pos_x2 = getPos (x2, ty2) context in
                                    let partial1Op = fun z -> Target.Apply2(Times, Target.d1op op (Target.Var(x1, newTy1)) (Target.Var(x2, newTy2)), z) in
                                    let partial2Op = fun z -> Target.Apply2(Times, Target.d2op op (Target.Var(x1, newTy1)) (Target.Var(x2, newTy2)), z) in 
                                    let secondPartialOp = fun dx -> fun z -> fun partial -> Target.Apply2(Times,Target.Apply2(Times,partial,dx),z) in
                                    let addFirstDerivatives =  Target.varToSyn newVarList
                                                              |> addToPos (pos_x2) (partial2Op (Target.Var (newVar1, Target.Type.Real)))
                                                              |> addToPos pos_x1  (partial1Op (Target.Var(newVar1, Target.Type.Real)))
                                                              |> addToPos (pos_x2+n)  (partial2Op (Target.Var(newVar2, Target.Type.Real)))
                                                              |> addToPos (pos_x1+n)  (partial1Op (Target.Var(newVar2, Target.Type.Real)))
                                    in
                                    let addSecondDerivatives =  addFirstDerivatives 
                                                              |> addToPos (pos_x2+n) (secondPartialOp (Target.Var(dx1,newTy1)) (Target.Var(newVar1, Target.Type.Real)) (Target.d1d1op op (Target.Var(x1,newTy1)) (Target.Var(x2,newTy2))))
                                                              |> addToPos (pos_x2+n) (secondPartialOp (Target.Var(dx2,newTy2)) (Target.Var(newVar1, Target.Type.Real)) (Target.d1d2op op (Target.Var(x1,newTy1)) (Target.Var(x2,newTy2))))
                                                              |> addToPos (pos_x1+n) (secondPartialOp (Target.Var(dx1,newTy1)) (Target.Var(newVar1, Target.Type.Real)) (Target.d2d1op op (Target.Var(x1,newTy1)) (Target.Var(x2,newTy2))))
                                                              |> addToPos (pos_x1+n) (secondPartialOp (Target.Var(dx2,newTy2)) (Target.Var(newVar1, Target.Type.Real)) (Target.d2d2op op (Target.Var(x1,newTy1)) (Target.Var(x2,newTy2))))
                                    in
                                    let newCont = Target.Fun(newContVarList, Target.App(cont, addSecondDerivatives)) in
                                    let tangent = Target.Apply2(Plus,
                                                          Target.Apply2(Times, Target.d1op op (Target.Var(x1, newTy1)) (Target.Var(x2, newTy2)), Target.Var(dx1, newTy1)),
                                                          Target.Apply2(Times, Target.d2op op (Target.Var(x1, newTy1)) (Target.Var(x2, newTy2)), Target.Var(dx2, newTy2)))  in
                                    Target.Tuple[Target.Apply2(op, Target.Var(x1, newTy1), Target.Var(x2, newTy2)); tangent ; newCont], newCont, context
                                    | _,_,_ -> failwith "rad: the continuation should be a function"
                                    end
    | Let(x, ty, expr1, expr2)  -> begin let dexpr1, cont, context = reverse12 context cont expr1 in  
                                   let x, dx, newContVar = dvar x in
                                   match Target.inferType cont with 
                                    | Result.Error s         -> failwith (Printf.sprintf "rad: continuation ill-typed: %s" s) 
                                    | Result.Ok(newContType) ->
                                   let newCont = Target.Var(newContVar, newContType) in
                                   let newContext = context @ [(x,ty)] in
                                   let dexpr2, newNewCont, context = reverse12 newContext newCont expr2 in
                                   Target.NCase(dexpr1, [(x, Target.Type.from_source ty); (dx, Target.Type.from_source ty) ; (newContVar, newContType)], dexpr2), newNewCont, context end
    | _ -> failwith "TODO"
end
