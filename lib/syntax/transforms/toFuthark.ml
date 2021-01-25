(* We compile our Target AST to Futhark source code. *)
(* Futhark is a nice purely functional array language for efficient code on CPU and GPU. *)
(* See https://futhark-lang.org/examples/values.html for more details. *)

open Syntax 
open Syntax.Target

module Precision = struct
open Syntax.Target.Type
(* For now, we will manage single and double precison floats. We might add more later *)
type t = Single | Double

let toFuthark fmt precision = Format.fprintf fmt (match precision with | Single -> "f32" | Double -> "f64")

let rec typeToFuthark precision fmt = function
  | Real             -> toFuthark fmt precision
  | NProd(tyList)    -> Format.fprintf fmt "%a" (CCList.pp ~pp_sep:(fun fmt () -> Format.fprintf fmt "@, @ ") (typeToFuthark precision)) tyList
  | Arrow(tyList,ty) -> Format.fprintf fmt "%a@ ->@ (%a)" (CCList.pp ~pp_sep:(fun fmt () -> Format.fprintf fmt "@ ->@ ") (fun fmt -> Format.fprintf fmt "(%a)" pp)) tyList (typeToFuthark precision) ty
end

 (* What we want:
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

let print_float fmt fl = Format.pp_print_float fmt fl (* 2. is not valid float in futhark, but 2.0 is.*) 
let print_unary_op precision fmt op =  (* an operator like cos in futhark is f32.cos *)
  Format.pp_print_string fmt ((match precision with | Precision.Single -> "f32." |  Precision.Double -> "f64." )^Operators.to_string_op1 op)
let print_binary_op _ fmt op =  Operators.to_string_op2 op |> Format.pp_print_string fmt

(* This function takes a floating precision, a format and an AST and compiles it to a Futhark program. *)
let rec toFuthark precision fmt = function
  | Var (v, ty) -> Format.fprintf fmt "@%a : (%a)" Var.pp v (Precision.typeToFuthark precision) ty
  | Const c -> print_float fmt c 
  | Apply1 (op, expr) -> Format.fprintf fmt "@[%a(@;<0 2>%a@,)@]" (print_unary_op precision) op (toFuthark precision) expr 
  | Apply2 (op, expr1, expr2) -> 
    if Operators.is_infix op then Format.fprintf fmt "@[(%a@ %a %a)@]" (toFuthark precision) expr1 (print_binary_op precision) op (toFuthark precision) expr2
    else Format.fprintf fmt "@[(%a %a %a)@]" (toFuthark precision) expr1 (print_binary_op precision) op (toFuthark precision) expr2
  | Let (x, ty, expr1, expr2) -> Format.fprintf fmt "@[<hv>let %a =@;<1 2>@[%a@]@ in@ %a@]" (toFuthark precision) (Var(x, ty)) (toFuthark precision) expr1 (toFuthark precision) expr2
  | Fun (vars, expr) -> Format.fprintf fmt "@[λ%a.@;<1 2>%a@]" (CCList.pp (fun fmt (v,_) -> Var.pp fmt v)) vars (toFuthark precision) expr
  | App (expr, exprs) -> Format.fprintf fmt "@[(%a)[@;<0 2>@[%a@]]@]" (toFuthark precision) expr (CCList.pp (toFuthark precision)) exprs
  | Tuple exprs -> CCList.pp ~pp_start:(fun fmt () -> Format.fprintf fmt "@[(@;<0 2>@[") ~pp_stop:(fun fmt () -> Format.fprintf fmt "@]@)@]") (toFuthark precision) fmt exprs
  | NCase (expr1, vars, expr2) -> Format.fprintf fmt "@[<hv>let (%a) =@;<1 2>@[%a@]@ in@ %a@]" (CCList.pp ~pp_sep:(fun fmt () -> Format.pp_print_string fmt ",") (fun fmt (v,_) -> Var.pp fmt v)) vars (toFuthark precision) expr1 (toFuthark precision) expr2

let pp precision expr = 
  CCIO.File.(remove_noerr (make "out.fut"));
  let file = Unix.openfile "out.fut" [Unix.O_WRONLY; Unix.O_CREAT] 0o644 in  
  let oc = Unix.out_channel_of_descr file in
  set_binary_mode_out oc false;
  let out = Format.formatter_of_out_channel oc in
  toFuthark precision out expr;;  