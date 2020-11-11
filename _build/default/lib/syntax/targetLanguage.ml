open Operators
open Vars

(* syntax *)
type synTarget = Var of var
            | Const of float 
            | Apply1 of op1 * synTarget 
            | Apply2 of op2 * synTarget * synTarget
            | Let of var * synTarget * synTarget
            | Pair of synTarget * synTarget
            | Fun of var * synTarget
            | App of synTarget * synTarget
            | Case of synTarget * var * var * synTarget