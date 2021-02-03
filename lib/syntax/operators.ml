(** Module defining the different operator in the language

The following operators take real arguments and return reals *)

type op1 = Cos  | Sin | Exp | Minus | Power of int
(** Unary operators *)

type op2 = Plus | Times | Minus
(**Binary operators *)

let is_infix _ = true

let equalOp1 op1 op2 = match op1,op2 with
  | Cos,Cos     -> true
  | Sin,Sin     -> true
  | Exp,Exp     -> true
  | Minus,Minus -> true
  | Power n, Power m -> n = m
  | _           -> false

let equalOp2 op1 op2 = match op1,op2 with
  | Plus,Plus   -> true
  | Times,Times -> true
  | Minus,Minus -> true
  | _           -> false

let interpretOp1 op v = match op with
    | Cos      -> cos(v)
    | Sin      -> sin(v)
    | Exp      -> exp(v)
    | Minus    -> -.v
    | Power(n) -> v ** float_of_int n

let interpretOp2 op val1 val2= match op with
    | Plus  -> val1+.val2
    | Times -> val1*.val2
    | Minus -> val1-.val2


let to_string_op1 = function
  | Cos -> "cos "
  | Sin -> "sin "
  | Exp -> "exp "
  | Minus -> "-"
  | Power n -> "^" ^ (string_of_int n)

let to_string_op2 = function
    | Plus  -> "+"
    | Times -> "*"
    | Minus -> "-"

let pp_op1 fmt op =
  to_string_op1 op |> Format.pp_print_string fmt

let pp_op2 fmt op =
  to_string_op2 op |> Format.pp_print_string fmt

module Parse = struct
  open CCParse

  let pOp1 =
    skip_white
    *> (try_ (string "cos")
       <|> try_ (string "sin")
       <|> try_ (string "exp")
       <|> try_ (string "-")
       <|> try_ (string "^"))
    <* skip_white
    >>= function
    | "cos" -> return Cos
    | "sin" -> return Sin
    | "exp" -> return Exp
    | "-" -> return (Minus : op1)
    | "^" -> U.int >|= fun n -> Power n
    | _ -> failwith "Not a operator"
end
