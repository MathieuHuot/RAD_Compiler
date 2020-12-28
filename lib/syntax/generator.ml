open Random
open Operators

type varSourceContext = (Var.t * Source.Type.t) list
type varTargetContext = (Var.t * Target.Type.t) list

(* Random terms generator for tests *)
let _ = Random.init 0
let randOp1Choice() = int 4 (* number of unary operators *)
let randOp2Choice() = int 3 (* number of binary operators *)
let sourceSynChoice() = int 5 (* number of term constructors for source language *)
let targetSynChoice() = int 9 (* number of term constructors for target language *)

let randConst() = float 100. (* uniform real number between 0 and 100, arbitrarily chosen *)

let randOp1() = match (randOp1Choice()) with
| 0 -> Cos
| 1 -> Sin
| 2 -> Exp
| _ -> Minus

let randOp2() = match (randOp2Choice()) with
| 0 -> Plus
| 1 -> Times
| _ -> Minus

let rec get_i i list = match list with
| [] -> failwith "randVar: empty list"
| x::list ->  if i=0 then x
              else get_i (i-1) list 

let randVar context = 
  let n = List.length(context) in
        begin
        self_init();        
        let i = int n in 
        get_i i context
        end

let sourceSynGen max_depth context : Source.t =
let rec syngen (context : varSourceContext) (depth : int) : Source.t * varSourceContext =
        if depth = max_depth then
        begin
        match (int 2) with
        | 0 ->  Const(randConst()), context
        | _ ->  begin
        match context with 
        | []    -> syngen context depth
        | _     -> 
        let x, ty = randVar(context) in 
        Var(x, ty), context
        end 
        end
        else begin
match (sourceSynChoice()) with
| 0 ->  Const(randConst()), context
| 1 ->  begin
        match context with 
        | []    -> syngen context depth
        | _     -> 
        let x, ty = randVar(context) in 
        Var(x, ty), context
        end
| 2 ->  let expr,_ = syngen context (depth+1) in 
        Apply1(randOp1(), expr), context
| 3 ->  let expr1,_ = syngen context (depth+1) in
        let expr2,_ = syngen context (depth+1) in
        Apply2(randOp2(), expr1, expr2), context
| _ ->  let x = Var.fresh() in
        let newcontext = (x, Source.Type.Real)::context in
        let expr1,_ = syngen context (depth+1) in
        let expr2,_ = syngen newcontext (depth+1)  in
        Let(x, Real, expr1, expr2), context
end
in 
let expr,_ = syngen context 0 in expr

(* experimental: can't generate from the whole syntax, for simple tests only *)
(* TODO: to generate from the whole syntax, I need to add types *)
let targetSynGen max_depth context : Target.t =
let rec syngen (context : varTargetContext) (depth : int) : Target.t * varTargetContext =
        if depth = max_depth then
        begin
        match (int 2) with
        | 0 ->  Const(randConst()), context
        | _ ->  begin
        match context with 
        | []    -> syngen context depth
        | _     -> 
        let x, ty = randVar(context) in 
        Var(x, ty), context
        end 
        end
        else begin
        match (targetSynChoice()) with
        | 0 | 4 | 6 ->  Const(randConst()), context
        | 1 | 7 ->  begin
                match context with 
                | []    -> syngen context depth
                | _     -> 
                let x, ty = randVar(context) in 
                Var(x, ty), context
                end
        | 2 ->  let expr,_ = syngen context (depth+1)in 
                Apply1(randOp1(), expr), context
        | 3 ->  let expr1,_ = syngen context (depth+1) in
                let expr2,_ = syngen context (depth+1) in
                Apply2(randOp2(), expr1, expr2), context     
        | _ ->  let x = Var.fresh() in
                let newcontext = (x, Target.Type.Real)::context in
                let expr1,_ = syngen context (depth+1) in
                let expr2,_ = syngen newcontext (depth+1) in
                Let(x, Real, expr1, expr2), context
        end
in 
let expr,_ = syngen context 0 in expr
