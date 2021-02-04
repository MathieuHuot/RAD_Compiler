(** Module defining the different operator in the language

The following operators take real arguments and return reals *)

(** Unary operators *)
type op1 = Cos  | Sin | Exp | Minus | Power of int | Acos | Asin | Tan | Atan | Cosh | Sinh | Tanh | Log | Log10 | Sqrt

(**Binary operators *)
type op2 = Plus | Times | Minus | Div 

let is_infix _ = true

let equalOp1 op1 op2 = match op1,op2 with
  | Cos,Cos     -> true
  | Sin,Sin     -> true
  | Exp,Exp     -> true
  | Minus,Minus -> true
  | Power n, Power m 
                -> n = m
  | Acos, Acos  -> true
  | Asin, Asin  -> true
  | Tan, Tan    -> true
  | Atan, Atan  -> true
  | Cosh, Cosh  -> true
  | Sinh, Sinh  -> true
  | Tanh, Tanh  -> true
  | Log, Log    -> true
  | Log10, Log10-> true
  | Sqrt, Sqrt  -> true
  | _           -> false

let equalOp2 op1 op2 = match op1,op2 with
  | Plus,Plus   -> true
  | Times,Times -> true
  | Minus,Minus -> true
  | Div, Div    -> true 
  | _           -> false

let interpretOp1 op v = match op with
    | Cos      -> cos(v)
    | Sin      -> sin(v)
    | Exp      -> exp(v)
    | Minus    -> -.v
    | Power(n) -> v ** float_of_int n
    | Acos     -> acos(v)
    | Asin     -> asin(v)
    | Tan      -> tan(v)
    | Atan     -> atan(v)
    | Cosh     -> cosh(v)
    | Sinh     -> sinh(v)
    | Tanh     -> tanh(v)
    | Log      -> log(v)
    | Log10    -> log10(v)
    | Sqrt     -> sqrt(v)

let interpretOp2 op val1 val2= match op with
    | Plus  -> val1+.val2
    | Times -> val1*.val2
    | Minus -> val1-.val2
    | Div   -> val1/.val2
 
let to_string_op1 = function
  | Cos     -> "cos "
  | Sin     -> "sin "
  | Exp     -> "exp "
  | Minus   -> "-"
  | Power n -> "^" ^ (string_of_int n)
  | Acos    -> "acos "
  | Asin    -> "asin " 
  | Tan     -> "tan "
  | Atan    -> "atan "
  | Cosh    -> "cosh "
  | Sinh    -> "sinh "
  | Tanh    -> "tanh "
  | Log     -> "log "
  | Log10   -> "log10 "
  | Sqrt    -> "sqrt "

let to_string_op2 = function
    | Plus  -> "+"
    | Times -> "*"
    | Minus -> "-"
    | Div   -> "/" 

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
       <|> try_ (string "acos")
       <|> try_ (string "asin")
       <|> try_ (string "tan")
       <|> try_ (string "atan")
       <|> try_ (string "cosh")
       <|> try_ (string "sinh")
       <|> try_ (string "tanh")
       <|> try_ (string "log")
       <|> try_ (string "log10")
       <|> try_ (string "sqrt"))
    <* skip_white
    >>= function
    | "cos" -> return Cos
    | "sin" -> return Sin
    | "exp" -> return Exp
    | "-" -> return (Minus : op1)
    | "^" -> U.int >|= fun n -> Power n
    | "acos" -> return Acos
    | "asin" -> return Asin
    | "tan"  -> return Tan
    | "atan" -> return Atan
    | "cosh" -> return Cosh
    | "sinh" -> return Sinh
    | "tanh" -> return Tanh
    | "log"  -> return Log
    | "log10" -> return Log10
    | "sqrt" -> return Sqrt
    | _ -> failwith "Not an operator"
end