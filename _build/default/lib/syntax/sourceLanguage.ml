open Operators
open Vars

(* syntax *)
type synSource = Var of var
            | Const of float 
            | Apply1 of op1 * synSource 
            | Apply2 of op2 * synSource * synSource
            | Let of var * synSource * synSource

(* interpreter *)
(* let interpreterSource = function
| Const a -> a
| Apply1(op,a) -> 
    let actual_op = 
    match op with ->
    | COS -> cos
    | SIN -> sin
    in actual_op(interpreterSource a)
| Apply2(op,a,b) ->
    let actual_op = 
    match op with ->
    | PLUS -> +
    | TIMES -> *
    in actual_op(interpreterSource a, interpreterSource b)
|   *)