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
let sourceSynGen () : SourceLanguage.sourceSyn =
let rec syngen (cont : varSourceContext) : SourceLanguage.sourceSyn * varSourceContext =
match (sourceSynChoice()) with
| 0 ->  Const(randConst()),cont
| 1 ->  begin
        match cont with 
        | []    -> syngen cont 
        | _     -> 
        let x,ty = randVar(cont) in 
        Var(x,ty),cont
        end
| 2 ->  let expr,_ = syngen(cont) in 
        Apply1(randOp1(),expr),cont
| 3 ->  let expr1,_ = syngen cont in
        let expr2,_ = syngen cont in
        Apply2(randOp2(),expr1,expr2),cont
| _ ->  let x = Vars.fresh() in
        let newCont = (x,SourceLanguage.Real)::cont in
        let expr1,_ = syngen cont in
        let expr2,_ = syngen newCont in
        Let(x,Real,expr1,expr2),cont
in 
let expr,_ = syngen [] in expr

(* experimental: can't generate from the whole syntax, for simple tests only *)
let targetSynGen () : TargetLanguage.targetSyn =
let rec syngen (cont : varTargetContext) : TargetLanguage.targetSyn * varTargetContext =
        match (targetSynChoice()) with
        | 0 | 4 | 6 ->  Const(randConst()),cont
        | 1 | 7 ->  begin
                match cont with 
                | []    -> syngen cont 
                | _     -> 
                let x,ty = randVar(cont) in 
                Var(x,ty),cont
                end
        | 2 ->  let expr,_ = syngen(cont) in 
                Apply1(randOp1(),expr),cont
        | 3 ->  let expr1,_ = syngen cont in
                let expr2,_ = syngen cont in
                Apply2(randOp2(),expr1,expr2),cont     
        | _ ->  let x = Vars.fresh() in
                let newCont = (x,TargetLanguage.Real)::cont in
                let expr1,_ = syngen cont in
                let expr2,_ = syngen newCont in
                Let(x,Real,expr1,expr2),cont
in 
let expr,_ = syngen [] in expr
