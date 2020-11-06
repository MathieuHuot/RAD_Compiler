type op1 = COS  | SIN 
type op2 = PLUS | TIMES 
type var = Var of int
type syn1 = var
            | Const of float 
            | Apply1 of op1 * syn1 
            | Apply2 of op2 * syn1 * syn1
            | Let of var * syn1 * syn1

type syn2 = var
            | Const of float 
            | Apply1 of op1 * syn2 
            | Apply2 of op2 * syn2 * syn2
            | Let of var * syn2 * syn2
            | Pair of syn2 * syn2
            | Fun of var * syn2

let f () =  let x = (2+3) in x