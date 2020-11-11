open Syntax.SourceLanguage
open Syntax.Operators
open Syntax.TargetLanguage

let rec forwardAD (expr:synSource) : synTarget = match expr with
| Const c               -> Pair(Const c, Const 0.)
| Var s                 -> Pair(Var s, Var (Syntax.Vars.fresh()))
| Apply1(op,expr)       ->  let y1 = Syntax.Vars.fresh() in
                            let y2 = Syntax.Vars.fresh() in  
                            let exprD = forwardAD expr in
                            failwith "TODO"
| Apply2(op,expr1,expr2)-> failwith "TODO" 
| Let(x,expr1,expr2)    -> failwith "TODO" 