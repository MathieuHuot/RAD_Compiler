open Random
open Operators

type varSourceContext = (Vars.var * SourceLanguage.sourceType) list
type varTargetContext = (Vars.var * TargetLanguage.targetType) list

(* Random terms generator for tests *)

(* let flip p = float 1. < p
let coinFlip = flip(0.5) *)
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
| [] -> failwith "empty list"
| x::list ->  if i==0 then x 
              else get_i (i-1) list 

let randVar cont = 
  let n = List.length(cont) in
        begin
        self_init();        
        let i = int n in 
        get_i i cont
        end

(* be careful, might not terminate *)
let sourceSynGen max_depth : SourceLanguage.sourceSyn =
let rec syngen (cont : varSourceContext) (depth : int) : SourceLanguage.sourceSyn * varSourceContext =
        if depth == max_depth then
        begin
        match (int 2) with
        | 0 ->  Const(randConst()),cont
        | _ ->  begin
        match cont with 
        | []    -> syngen cont depth
        | _     -> 
        let x,ty = randVar(cont) in 
        Var(x,ty),cont
        end 
        end
        else begin
match (sourceSynChoice()) with
| 0 ->  Const(randConst()),cont
| 1 ->  begin
        match cont with 
        | []    -> syngen cont depth
        | _     -> 
        let x,ty = randVar(cont) in 
        Var(x,ty),cont
        end
| 2 ->  let expr,_ = syngen cont (depth+1) in 
        Apply1(randOp1(),expr),cont
| 3 ->  let expr1,_ = syngen cont (depth+1) in
        let expr2,_ = syngen cont (depth+1) in
        Apply2(randOp2(),expr1,expr2),cont
| _ ->  let x = Vars.fresh() in
        let newCont = (x,SourceLanguage.Real)::cont in
        let expr1,_ = syngen cont (depth+1) in
        let expr2,_ = syngen newCont (depth+1)  in
        Let(x,Real,expr1,expr2),cont
end
in 
let expr,_ = syngen [] 0 in expr

(* experimental: can't generate from the whole syntax, for simple tests only *)
let targetSynGen max_depth : TargetLanguage.targetSyn =
let rec syngen (cont : varTargetContext) (depth : int) : TargetLanguage.targetSyn * varTargetContext =
        if depth == max_depth then
        begin
        match (int 2) with
        | 0 ->  Const(randConst()),cont
        | _ ->  begin
        match cont with 
        | []    -> syngen cont depth
        | _     -> 
        let x,ty = randVar(cont) in 
        Var(x,ty),cont
        end 
        end
        else begin
        match (targetSynChoice()) with
        | 0 | 4 | 6 ->  Const(randConst()),cont
        | 1 | 7 ->  begin
                match cont with 
                | []    -> syngen cont depth
                | _     -> 
                let x,ty = randVar(cont) in 
                Var(x,ty),cont
                end
        | 2 ->  let expr,_ = syngen cont (depth+1)in 
                Apply1(randOp1(),expr),cont
        | 3 ->  let expr1,_ = syngen cont (depth+1) in
                let expr2,_ = syngen cont (depth+1) in
                Apply2(randOp2(),expr1,expr2),cont     
        | _ ->  let x = Vars.fresh() in
                let newCont = (x,TargetLanguage.Real)::cont in
                let expr1,_ = syngen cont (depth+1) in
                let expr2,_ = syngen newCont (depth+1) in
                Let(x,Real,expr1,expr2),cont
        end
in 
let expr,_ = syngen [] 0 in expr