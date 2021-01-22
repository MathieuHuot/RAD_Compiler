(* We compile our Target AST to Futhark source code. *)
(* Futhark is a nice purely functional array language for efficient code on CPU and GPU. *)
(* See https://futhark-lang.org/examples/values.html for more details. *)

open Syntax 
open Syntax.Target

(* For now, we will manage single and double precison floats. We might add more later *)
type precision = Single | Double

 (* What we want:
 Real               --> f32 or f64  dependingon whether precision is Single or Double
 NProd(tyList)      --> ([ty1],[ty2],...,[tyn])   where tyList=[ty1,...,tyn]
 Arrow(tyList,ty)   --> ([ty1] -> [ty2] -> ... -> [tyn] -> [ty])    where tyList = [ty1,...,tyn]

 Var((str,i),ty)    --> str^i : [ty]
 Const c            --> c
 Apply1( op ,e)     --> op [e]
 Apply2(op,e1,e2)   --> op [e1] [e2] 
 Let(x,ty,e1,e2)    --> let x : [ty] = [e1] in [e2]
 Fun(vars,e)        --> (\x1 -> \x2 -> \x3 -> ... \xn -> [e]) where vars=[x1,...,xn]
 App(e1,eList)      --> [e] [e1] ... [en]   where eList=[e1,...,en]  !! Be careful, it won't for higher-order functions without extra parentheses. 
 Tuple(eList)       --> ([e1],...,[en]) where eList=[e1,...,en]
 NCase(e1,vList,e2) --> let ([v1] : [ty1],...,[vn] : [tyn]) = [e1] in [e2]  where vList = [(v1,ty1),...,(vn,tyn)]
 *) 

(* This function takes a format and a floating precision, and an AST and compiles it to a Futhark program. *)
let rec toFuthark precision fmt = function
  | Var (v, _) -> Var.pp fmt v
  | Const c -> Format.pp_print_float fmt c
  | Apply1 (op, expr) -> Format.fprintf fmt "@[%a(@;<0 2>%a@,)@]" Operators.pp_op1 op (toFuthark precision) expr
  | Apply2 (op, expr1, expr2) ->
    if Operators.is_infix op then Format.fprintf fmt "@[(%a@ %a %a)@]" (toFuthark precision) expr1 Operators.pp_op2 op (toFuthark precision) expr2
    else Format.fprintf fmt "@[(%a %a %a)@]" (toFuthark precision) expr1 Operators.pp_op2 op (toFuthark precision) expr2
  | Let (x, _t, expr1, expr2) -> Format.fprintf fmt "@[<hv>let %a =@;<1 2>@[%a@]@ in@ %a@]" Var.pp x (toFuthark precision) expr1 (toFuthark precision) expr2
  | Fun (vars, expr) -> Format.fprintf fmt "@[λ%a.@;<1 2>%a@]" (CCList.pp (fun fmt (v,_) -> Var.pp fmt v)) vars (toFuthark precision) expr
  | App (expr, exprs) -> Format.fprintf fmt "@[(%a)[@;<0 2>@[%a@]]@]" (toFuthark precision) expr (CCList.pp (toFuthark precision)) exprs
  | Tuple exprs -> CCList.pp ~pp_start:(fun fmt () -> Format.fprintf fmt "@[{@;<0 2>@[") ~pp_stop:(fun fmt () -> Format.fprintf fmt "@]@ }@]") (toFuthark precision) fmt exprs
  | NCase (expr1, vars, expr2) -> Format.fprintf fmt "@[<hv>lets %a =@;<1 2>@[%a@]@ in@ %a@]" (CCList.pp ~pp_sep:(fun fmt () -> Format.pp_print_string fmt ",") (fun fmt (v,_) -> Var.pp fmt v)) vars (toFuthark precision) expr1 (toFuthark precision) expr2

let print precision expr = 
  CCIO.File.(remove_noerr (make "out.fut"));
  let file = Unix.openfile "out.fut" [Unix.O_WRONLY; Unix.O_CREAT] 0o644 in  
  let oc = Unix.out_channel_of_descr file in
  set_binary_mode_out oc false;
  let out = Format.formatter_of_out_channel oc in
  toFuthark precision out expr;;

print Double (Const 0.)  