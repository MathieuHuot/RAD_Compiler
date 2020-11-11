open Operators
open Vars

(* syntax *)
type targetType = Real 
            | Prod of targetType * targetType

and synTarget = Var of var * targetType
            | Const of float 
            | Apply1 of op1 * synTarget 
            | Apply2 of op2 * synTarget * synTarget
            | Let of var * targetType * synTarget * synTarget
            | Pair of synTarget * synTarget
            | Fun of var * targetType * synTarget
            | App of synTarget * synTarget
            | Case of synTarget * var * targetType * var * targetType * synTarget