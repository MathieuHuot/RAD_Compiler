open Syntax.SourceLanguage
open Syntax.TargetLanguage

let forwardAD (expr:synSource) : synTarget = match expr with
| Const c -> Pair(Const c, Const 0.)
| _ -> failwith "TODO"