open Operators
open Vars


(* syntax *)
type syn2 = Var of var
            | Const of float 
            | Apply1 of op1 * syn2 
            | Apply2 of op2 * syn2 * syn2
            | Let of var * syn2 * syn2
            | Pair of syn2 * syn2
            | Fun of var * syn2
            | App of syn2 * syn2
            | Case of syn2 * var * var * syn2