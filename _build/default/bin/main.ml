type op1 = COS  | SIN 
type op2 = PLUS | TIMES 
type syn1 = Var of int 
            | Const of float 
            | Apply1 of op1 * syn1 
            | Apply2 of op2 * syn1 * syn1 

let f () =  let x = (2+3) in x

