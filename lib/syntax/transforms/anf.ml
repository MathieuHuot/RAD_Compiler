open Syntax.SourceLanguage

let isVar expr = match expr with
| Var _ -> true
| _     -> false

let isConst expr = 
match expr with
| Const _   -> true
| _         -> false

let isImmediate expr = match expr with
| Const _                  -> true
| Var _                    -> true
| Apply1(_,expr1)          -> isVar expr1 
| Apply2(_,expr1,expr2)    -> isVar expr1 && isVar expr2
| _                        -> failwith "wrong expression format"

let rec isInAnf expr = match expr with
| Let(_,expr1,expr2) -> isImmediate expr1 && isInAnf expr2
| _ -> true

let rec isInWeakAnf expr = match expr with
| Let(_,expr1,expr2) -> isInWeakAnf expr1 && isInWeakAnf expr2
| Apply1(_,_)   -> isImmediate expr 
| Apply2(_,_,_) -> isImmediate expr
| _ -> true

let rec weakAnf expr = match expr with
| Const c -> Const c
| Var x -> Var x
| Apply1(op,expr1) -> if isImmediate expr then expr else 
    let exprAnf = weakAnf expr1 in
    let n = Syntax.Vars.fresh() in
    let newVar = Var(n) in 
    Let(n,exprAnf,Apply1(op,newVar))
| Apply2(op,expr1,expr2) -> if isImmediate expr then expr else
    let expr1Anf = weakAnf expr1 in 
    let expr2Anf = weakAnf expr2 in 
    let n = Syntax.Vars.fresh() in
    let newVar1 = Var(n) in 
    let m = Syntax.Vars.fresh() in 
    let newVar2 = Var(m) in 
    Let(n,expr1Anf,Let(m,expr2Anf,Apply2(op,newVar1, newVar2)))
| Let(x,expr1,expr2) -> Let(x, weakAnf expr1, weakAnf expr2)

(* currently wrong *)
let rec anf expr = match expr with
| Const c -> Const c
| Var x -> Var x
| Apply1(op,expr1) -> if isImmediate expr then expr else 
    let exprAnf = anf expr1 in
    let n = Syntax.Vars.fresh() in
    let newVar = Var(n) in 
    Let(n,exprAnf,Apply1(op,newVar))
| Apply2(op,expr1,expr2) -> if isImmediate expr then expr else
    let expr1Anf = anf expr1 in 
    let expr2Anf = anf expr2 in 
    let n = Syntax.Vars.fresh() in
    let newVar1 = Var(n) in 
    let m = Syntax.Vars.fresh() in 
    let newVar2 = Var(m) in 
    Let(n,expr1Anf,Let(m,expr2Anf,Apply2(op,newVar1, newVar2)))
| Let(x,expr1,expr2) -> Let(x, anf expr1, anf expr2)