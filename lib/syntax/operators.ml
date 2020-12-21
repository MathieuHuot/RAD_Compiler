(** Module defining the different operator in the language

The following operators take real arguments and return reals *)

type op1 = Cos  | Sin | Exp | Minus | Power of int
(** Unary operators *)

type op2 = Plus | Times | Minus
(**Binary operators *)

let is_infix _ = true

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
