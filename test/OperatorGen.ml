open Syntax
open Operators

let power n = Power n

let gen1 =
  QCheck.Gen.(
    oneof
      [
        return Cos;
        return Sin;
        return Exp;
        return (Minus : op1);
        map power (int_bound 5);
      ])

let gen2 = QCheck.Gen.(oneofl [ Plus; Times; (Minus : op2) ])

let shrink1 op =
  let open QCheck.Iter in
  match op with Power n -> QCheck.Shrink.int n >|= power | _ -> empty
