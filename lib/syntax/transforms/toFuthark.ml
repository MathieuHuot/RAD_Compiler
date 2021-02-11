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
  | Array(n, ty)     -> Format.fprintf fmt "[%a]%a" Format.pp_print_int n (typeToFuthark precision) ty
end

(*2. is not valid float in futhark, but 2.0 is. current fix doesn't work for numbers represented with exposents *) 
let print_float fmt fl = 
  let s = string_of_float fl in
  if s.[String.length s - 1] = '.' then Format.fprintf fmt "%s0" s
  else Format.fprintf fmt "%s" s
let print_unary_op precision fmt op =  (* an operator like cos in futhark is f32.cos *)
  Format.pp_print_string fmt ((match precision with | Precision.Single -> "f32." |  Precision.Double -> "f64." )^Operators.to_string_op1 op)
let print_binary_op _ fmt op =  Operators.to_string_op2 op |> Format.pp_print_string fmt

(* This function takes a floating precision, a format and an AST and compiles it to a Futhark program. *)
let rec toFuthark precision fmt = function
  | Var (v, ty) -> Format.fprintf fmt "%a : (%a)" Var.pp v (Precision.typeToFuthark precision) ty
  | Const c -> print_float fmt c 
  | Apply1 (op, expr) -> Format.fprintf fmt "@[%a(@;<0 2>%a@,)@]" (print_unary_op precision) op (toFuthark precision) expr 
  | Apply2 (op, expr1, expr2) -> 
    if Operators.is_infix op then Format.fprintf fmt "@[(%a@ %a %a)@]" (toFuthark precision) expr1 (print_binary_op precision) op (toFuthark precision) expr2
    else Format.fprintf fmt "@[(%a %a %a)@]" (toFuthark precision) expr1 (print_binary_op precision) op (toFuthark precision) expr2
  | Let (x, ty, expr1, expr2) -> Format.fprintf fmt "@[<hv>let %a =@;<1 2>@[%a@]@ in@ %a@]" (toFuthark precision) (Var(x, ty)) (toFuthark precision) expr1 (toFuthark precision) expr2
  | Fun (vars, expr) -> Format.fprintf fmt "@[\\(%a) -> @;<1 2>%a@]" (CCList.pp ~pp_sep:(fun fmt () -> Format.pp_print_string fmt ",") (fun fmt (v,_) -> Var.pp fmt v)) vars (toFuthark precision) expr
  | App (expr, exprs) -> Format.fprintf fmt "@[(%a)[@;<0 2>@[%a@]]@]" (toFuthark precision) expr (CCList.pp (toFuthark precision)) exprs
  | Tuple exprs -> CCList.pp ~pp_start:(fun fmt () -> Format.fprintf fmt "@[(@,<0 2>@[") ~pp_stop:(fun fmt () -> Format.fprintf fmt "@]@)@]") (toFuthark precision) fmt exprs
  | NCase (expr1, vars, expr2) -> Format.fprintf fmt "@[<hv>let (%a) =@;<1 2>@[%a@]@ in@ %a@]" (CCList.pp ~pp_sep:(fun fmt () -> Format.pp_print_string fmt ",") (fun fmt (v,_) -> Var.pp fmt v)) vars (toFuthark precision) expr1 (toFuthark precision) expr2
  | Map (x, _t, expr1, expr2) -> Format.fprintf fmt "map (\\%a -> %a) %a" Var.pp x pp expr1 pp expr2
  | Map2 (x, _t1, y, _t2, expr1, expr2, expr3) -> Format.fprintf fmt "map2 (\\%a -> \\%a -> %a) (%a) (%a)" Var.pp x Var.pp y pp expr1 pp expr2  pp expr3
  | Map3 (x, _t1, y, _t2, z, _t3, expr1, expr2, expr3, expr4) -> Format.fprintf fmt "map3 (\\%a -> \\%a -> \\%a -> %a) (%a) (%a) (%a)" Var.pp x Var.pp y  Var.pp z pp expr1 pp expr2 pp expr3 pp expr4
  | Reduce (x, _t1, y, _t2, expr1, expr2, expr3) -> Format.fprintf fmt "reduce (\\%a -> \\%a -> %a) (%a) (%a)" Var.pp x Var.pp y pp expr1 pp expr2 pp expr3
  | Scan (x, _t1, y, _t2, expr1, expr2, expr3)  -> Format.fprintf fmt "scan (\\%a -> \\%a -> %a) (%a) (%a)" Var.pp x Var.pp y pp expr1 pp expr2 pp expr3
  | Zip(expr1, expr2) -> Format.fprintf fmt "zip %a %a" pp expr1 pp expr2
  | Zip3(expr1, expr2, expr3) -> Format.fprintf fmt "zip3 %a %a %a" pp expr1 pp expr2 pp expr3
  | Unzip(expr) -> Format.fprintf fmt "unzip %a " pp expr
  | Unzip3(expr) -> Format.fprintf fmt "unzip3 %a " pp expr 
  (* | Get(n, expr)      -> (* Be careful, produces a fresh variable. seems to be needed to adapt to Futhark *)
    let y = Var.fresh() in Format.fprintf fmt "@[<hv>let %a =@;<1 2>@[%a@]@ in@ %a[%a]@]" Var.pp y pp expr Var.pp y Format.pp_print_int n *)
  | Fold (x, _t1, y, _t2, expr1, expr2, expr3)  -> Format.fprintf fmt "loop %a=%a for %a in %a do %a" Var.pp x pp expr2  Var.pp y pp expr3 pp expr1
  | Array (exprList) -> CCList.pp ~pp_sep:(fun fmt () -> Format.fprintf fmt "@[(@,<0 2>@[") ~pp_stop:(fun fmt () -> Format.fprintf fmt "@]]@]") (toFuthark precision) fmt exprList

let pp precision expr = 
  CCIO.File.(remove_noerr (make "out.fut"));
  let file = Unix.openfile "out.fut" [Unix.O_WRONLY; Unix.O_CREAT] 0o644 in  
  let oc = Unix.out_channel_of_descr file in
  set_binary_mode_out oc false;
  let out = Format.formatter_of_out_channel oc in
  Format.fprintf out "%a@." (toFuthark precision) expr
