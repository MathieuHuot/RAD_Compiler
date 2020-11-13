(* the following operators take real arguments and return reals *)

type op1 = Cos  | Sin | Exp | Minus
type op2 = Plus | Times | Minus

let interpreterOp1 op v = match op with
| Cos  -> cos(v)
| Sin  -> sin(v)
| Exp  -> exp(v)
| Minus-> -.v

let interpreterOp2 op val1 val2= match op with
| Plus  -> val1+.val2
| Times -> val1*.val2
| Minus -> val1-.val2