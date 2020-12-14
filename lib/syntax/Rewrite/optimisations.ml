(* Module for optimisations. Somewhat similar to generalized folds in Haskell *)
(* We have an abstract module traverse for traversal of ADT. *)
(* We instantiate it to our two main ADT: the source and target syntax. *)
(* Then, every optimisation is enclosed in a module, and is coded as a functor from *)
(* a traversal module. *)

(* The main optimisations performed are: *)
(* Constant Propagation *)
(* Simple Algebraic Simplifications *)
(* Let Commutativities *) 
(* Forward Subsitution *)
(* Common SubExpressions *)
(* Dead Code Elimination *)

  module type Traverse = sig
    type adt
    val traverse: adt -> adt Strategies.Strategy.strategy -> adt Strategies.Strategy.rewriteResult
  end
  
 module SourceTr : Traverse with type adt = Syntax.SourceLanguage.sourceSyn = struct
  open Syntax.SourceLanguage
  open Strategies.Strategy
  type adt = sourceSyn
  
  let traverse expr strat = 
    match expr with
    | Var _                                -> Failure strat
    | Const _                              -> Failure strat
    | Apply1(op, expr)                     -> begin 
                                              match strat expr with 
                                              | Success(s) -> Success(Apply1(op,s)) 
                                              | Failure _ -> Failure strat 
                                              end
    | Apply2(op, expr1, expr2)             -> begin 
                                              match strat expr1, strat expr2 with 
                                              | Success(s1), Success (s2) -> Success(Apply2(op,s1,s2))
                                              | Success(s1), Failure _    -> Success(Apply2(op,s1,expr2))
                                              | Failure _, Success (s2)   -> Success(Apply2(op,expr1,s2))
                                              | _                         -> Failure strat
                                              end
    | Let(x, ty, expr1, expr2)             -> begin 
                                              match strat expr1, strat expr2 with 
                                              | Success(s1), Success (s2) -> Success(Let(x,ty,s1,s2))
                                              | Success(s1), Failure _    -> Success(Let(x,ty,s1,expr2))
                                              | Failure _, Success (s2)   -> Success(Let(x,ty,expr1,s2))
                                              | _                         -> Failure strat
                                              end
  end

  module TargetTr : Traverse with type adt = Syntax.TargetLanguage.targetSyn = struct
  open Syntax.TargetLanguage
  open Strategies.Strategy
  type adt = targetSyn
  
  let traverse expr strat = 
    match expr with
    | Var _                                -> Failure strat
    | Const _                              -> Failure strat
    | Apply1(op, expr)                     -> begin 
                                              match strat expr with 
                                              | Success(s) -> Success(Apply1(op,s)) 
                                              | Failure _ -> Failure strat 
                                              end
    | Apply2(op, expr1, expr2)             -> begin 
                                              match strat expr1, strat expr2 with 
                                              | Success(s1), Success (s2) -> Success(Apply2(op,s1,s2))
                                              | Success(s1), Failure _    -> Success(Apply2(op,s1,expr2))
                                              | Failure _, Success (s2)   -> Success(Apply2(op,expr1,s2))
                                              | _                         -> Failure strat
                                              end
    | Let(x, ty, expr1, expr2)             -> begin 
                                              match strat expr1, strat expr2 with 
                                              | Success(s1), Success (s2) -> Success(Let(x,ty,s1,s2))
                                              | Success(s1), Failure _    -> Success(Let(x,ty,s1,expr2))
                                              | Failure _, Success (s2)   -> Success(Let(x,ty,expr1,s2))
                                              | _                         -> Failure strat
                                              end
    | Tuple(exprList)                      -> let sList = List.map strat exprList in
                                              (* If no success is found, failure *)
                                              if not(List.exists (fun x -> match x with Success _ -> true | _ -> false) sList)
                                              then Failure strat
                                              else
                                              (* Else success tuple with the successes replacing the original expressions *)
                                              Success(Tuple(
                                                List.rev (List.fold_left2 
                                                (fun acc expr s -> match s with | Success(s) -> s::acc | Failure _ -> expr::acc)
                                                [] exprList sList
                                                )))
    | App(expr, exprList)                  -> let sList = List.map strat (expr::exprList) in
                                              (* If no success is found, failure *)
                                              if not(List.exists (fun x -> match x with Success _ -> true | _ -> false) sList)
                                              then Failure strat
                                              else
                                              (* Else record list with the successes replacing the original expressions *)
                                              let newExprList = List.rev (List.fold_left2 
                                                                (fun acc expr s -> match s with | Success(s) -> s::acc | Failure _ -> expr::acc)
                                                                [] (expr::exprList) sList) in
                                              let newExpr, exprList = List.hd(newExprList), List.tl(newExprList) in
                                              Success(App(newExpr,exprList))
    | Fun(varList, expr)                   -> begin 
                                              match strat expr with 
                                              | Success(s) -> Success(Fun(varList,s)) 
                                              | Failure _ -> Failure strat 
                                              end
    | NCase(expr1, varList, expr2)         -> begin 
                                              match strat expr1, strat expr2 with 
                                              | Success(s1), Success (s2) -> Success(NCase(s1, varList, s2))
                                              | Success(s1), Failure _    -> Success(NCase(s1, varList, expr2))
                                              | Failure _, Success (s2)   -> Success(NCase(expr1, varList, s2))
                                              | _                         -> Failure strat
                                              end
  end

module type Optim = functor
  (Tr: sig 
    type adt = TargetTr.adt 
    val traverse : adt -> adt Strategies.Strategy.strategy -> adt Strategies.Strategy.rewriteResult
    end)
  -> sig val run : Tr.adt Strategies.Strategy.strategy end

module ConstantPropagation: Optim =  
functor (Tr: Traverse with type adt = Syntax.TargetLanguage.targetSyn) ->
struct
open Syntax.TargetLanguage
open Strategies.Strategy

let rec run expr = match expr with
  | Apply2(Plus,Const a,Const b)   -> Success(Const(a+.b))
  | Apply2(Times,Const a,Const b)  -> Success(Const(a*.b))
  | Apply1(Cos, Const c)           -> Success(Const(cos c))
  | Apply1(Sin, Const c)           -> Success(Const(sin c))
  | Apply1(Exp, Const c)           -> Success(Const(exp c))
  | Apply1(Power n, Const c)       -> Success(Const (c ** float_of_int n))
  | expr                           -> Tr.traverse expr run
end

module SimpleAlgebraicSimplifications: Optim = 
functor (Tr : Traverse with type adt = Syntax.TargetLanguage.targetSyn) ->
struct
open Syntax.TargetLanguage
open Strategies.Strategy

let rec run expr = match expr with
  | Apply2(Plus,expr1,Apply1(Minus,expr2)) 
      -> Success(Apply2(Minus,expr1,expr2))
  | Apply2(Times,Const(-1.),expr)  
      -> Success(Apply1(Minus,expr))
  | Apply1(Minus,Apply1(Minus,expr))
      -> Success(expr)
  | Apply1(Minus,Const c)          
      -> Success(Const(-.c))
  | Apply2(Minus,expr1,Apply1(Minus,expr2))
      -> Success(Apply2(Plus,expr1,expr2))
  | Let(x,ty,Const(c),e)          
      -> Success(subst x ty (Const(c)) e)
  | Apply2(Times,Apply1(Minus,expr1),expr2) 
      -> Success(Apply1(Minus,Apply2(Times,expr1,expr2)))
  | Apply2(Times,expr1,Apply1(Minus,expr2)) 
      -> Success(Apply1(Minus,Apply2(Times,expr1,expr2)))
  | Apply1(Power n, Apply1(Minus, expr))
      -> if n mod 2=0
      then Success(Apply1(Power n,expr))
      else Success(Apply1(Minus,Apply1(Power n,expr)))
  | Apply1(Power n,Apply1(Exp,expr))
      -> Success(Apply1(Exp,Apply2(Times,Const(float_of_int n),expr)))
  | Apply2(Times,expr,Const 1.)   
      -> Success(expr)
  | Apply2(Times,Const 1.,expr)   
      -> Success(expr)
  | Apply2(Times,Apply1(Exp,expr1),Apply1(Exp,expr2)) 
      -> Success(Apply1(Exp,Apply2(Plus,expr1,expr2)))
  | Apply2(Plus,Apply1(Minus,expr1),expr2) 
      -> Success(Apply2(Minus,expr2,expr1))
  | _ -> Tr.traverse expr run 
end 

module ZeroSimplification: Optim = 
functor (Tr : Traverse with type adt = Syntax.TargetLanguage.targetSyn) ->
struct
open Syntax.TargetLanguage
open Strategies.Strategy

let rec run expr = match expr with
  | Apply2(Times,_,Const 0.)      -> Success(Const 0.)
  | Apply2(Times,Const 0.,_)      -> Success(Const 0.)
  | Apply2(Plus,expr,Const 0.)    -> Success(expr)
  | Apply2(Plus,Const 0.,expr)    -> Success(expr)
  | Apply2(Minus,Const 0.,expr)   -> Success(Apply1(Minus, expr))
  | _                             -> Tr.traverse expr run 
end

module TrigoSimplification: Optim = 
functor (Tr : Traverse with type adt = Syntax.TargetLanguage.targetSyn) ->
struct
open Syntax.TargetLanguage
open Strategies.Strategy

let rec run expr = match expr with
  | Apply1(Sin,Apply1(Minus,expr)) -> Success(Apply1(Minus,Apply1(Sin,expr)))
  | Apply1(Cos,Apply1(Minus,expr)) -> Success(Apply1(Cos,expr))
  | Apply2(Plus,Apply1(Power 2,Apply1(Sin,expr1)),Apply1(Power 2,Apply1(Cos,expr2))) 
    when equalTerms expr1 expr2    -> Success(Const 1.) 
  | _                              -> Tr.traverse expr run 
end

module RealFactorisation: Optim = 
functor (Tr : Traverse with type adt = Syntax.TargetLanguage.targetSyn) ->
struct
open Syntax.TargetLanguage
open Strategies.Strategy

let rec run expr = match expr with
  | Apply2(Plus,Apply2(Times,expr1,expr2),Apply2(Times,expr3,expr4)) 
    when equalTerms expr1 expr3   -> Success(Apply2(Times,expr1,Apply2(Plus,expr2,expr4)))
  | Apply2(Plus,Apply2(Times,expr1,expr2),Apply2(Times,expr3,expr4)) 
    when equalTerms expr2 expr4   -> Success(Apply2(Times,Apply2(Plus,expr1,expr3),expr2))
  | Apply2(Plus,expr1,expr2) when equalTerms expr1 expr2 
                                  -> Success(Apply2(Times,Const 2.,expr1))
  | _                             -> Tr.traverse expr run 
end

module LetCommutativity: Optim = 
functor (Tr : Traverse with type adt = Syntax.TargetLanguage.targetSyn) ->
struct
open Syntax.TargetLanguage
open Strategies.Strategy

let rec run expr = match expr with
  | Let(x,ty1,Let(y,ty2,expr1,expr2),expr3)   
      -> Success(Let(y,ty2, expr1,Let(x,ty1, expr2, expr3)))
  | NCase(NCase(expr1,varList1,expr2),varList2,expr3)
      -> Success(NCase(expr1,varList1,NCase(expr2,varList2,expr3)))
  | NCase(Let(x1,ty1,expr1,expr2),varList,expr3)
      -> Success(Let(x1,ty1,expr1,NCase(expr2,varList,expr3)))
  | Let(x,ty,NCase(expr1,varList,expr2),expr3)
      -> Success(NCase(expr1,varList,Let(x,ty,expr2,expr3)))
  | _ -> Tr.traverse expr run 
  end

module ForwardSubstitution: Optim = 
functor (Tr : Traverse with type adt = Syntax.TargetLanguage.targetSyn) ->
struct
open Syntax.TargetLanguage
open Strategies.Strategy

let isVar expr = match expr with
  | Var(_) -> true
  | _      -> false

let isConst expr = match expr with
  | Const(_) -> true
  | _        -> false

let rec run expr = match expr with
  | Let(x,_,Var(y,ty),e)  -> Success(subst x ty (Var(y,ty)) e)
  | NCase(Tuple(exprList),varList,expr)
    when List.for_all (fun x -> isVar x || isConst x) exprList
                          -> Success(simSubst (List.combine varList exprList) expr)
  | NCase(Tuple(exprList),varList,expr)
    when List.exists (fun x -> isVar x || isConst x) exprList 
                          -> if List.length exprList<>List.length varList 
                             then failwith "ForwardSubstitution: tuple wrong number of arguments"
                             else
                             (* a candidate for forward substitution has been found in exprList *)
                             (* partition exprList and varList into two lists, one pair for which we can do forward subsitution *)
                             (* The latter is gathered into context and a simultaneous substitution is performed *)
                             let exprList1, varList1 = List.split (List.filter (fun (x,_) -> not(isVar x || isConst x)) (List.combine exprList varList)) in
                             let context = List.filter (fun (_,x) -> isVar x || isConst x) (List.combine varList exprList) in
                             Success(NCase(Tuple(exprList1),varList1, simSubst context expr))
  | _                     -> Tr.traverse expr run 
end

module LetSimplification: Optim = 
functor (Tr : Traverse with type adt = Syntax.TargetLanguage.targetSyn) ->
struct
open Syntax.TargetLanguage
open Strategies.Strategy

let rec run expr = match expr with
  (* let x=e1 in let y=e1 in e2 -> let x=e0 in let y=x in e2 *)
  | Let(x1,ty1,e0,Let(x2,ty2,e1,e2)) 
    when (equalTerms e0 e1) -> Success(Let(x1,ty1,e0,Let(x2,ty2,Var(x1,ty1),e2)))
  (* let x=e0 in let y=e1 in e2 -> let y=e1 in let x=e0 in e2 (x not a FV in e1) *)
  | Let(x1,ty1,e0,Let(x2,ty2,e1,e2)) when not(List.mem x1 (freeVars e1)) 
                            -> Success(Let(x2,ty2,e1,Let(x1,ty1,e0,e2)))
  | _                       -> Tr.traverse expr run 
end

module LambdaRemoval: Optim = 
functor (Tr : Traverse with type adt = Syntax.TargetLanguage.targetSyn) ->
struct
open Syntax.TargetLanguage
open Strategies.Strategy

let rec run expr = match expr with
  (* replaces inlined lambdas in (fun x1...xn.e)[e1...en] to 
      let x1 = e1 in let x2 = e2 in ... in let xn = en in e
      for later optimisations like forward substitution *)                               
  | App(Fun(varList,expr),exprList) 
                             -> if not(List.length varList = List.length exprList)
                                then failwith "LambdaRemoval: Function applied to wrong number of arguments" 
                                else Success(NCase(Tuple(exprList),varList,expr)) 
  (* CBN evaluates a variable which has a function type *)
  | Let(x,ty,expr1,expr2) 
    when isArrow ty          -> Success(subst x ty expr1 expr2)
  (* | NCase(Tuple(exprList),varList,expr) when List.exists (fun (_,ty) -> isArrow ty) varList 
                             -> let list = List.combine varList exprList in
                                let arrowList, nonArrowList = List.partition (fun ((_,ty),_) -> isArrow ty) list in
                                let var2, expr2 = List.split nonArrowList in
                                Success(NCase(Tuple(expr2),var2, simSubst arrowList expr)) *)
  | _                        -> Tr.traverse expr run 
end 

module DeadVarsElim: Optim =
functor (Tr : Traverse with type adt = Syntax.TargetLanguage.targetSyn) ->
struct
open Syntax.TargetLanguage
open Strategies.Strategy

(* dead code elimination of a list of unused variables *)
let run expr =
  let unusedVars = Analysis.listUnusedVars expr in
  let rec aux unusedVars expr =
    match expr with
    | Let(x, ty,_,expr) 
      when (List.mem (x,ty) unusedVars)    -> tryStrat (aux unusedVars) expr
    | NCase(_,varList, expr)
      when List.for_all (fun y -> List.mem y unusedVars) varList
                                           -> Success(expr)
    | NCase(Tuple(exprList),varList,expr)  -> let list = List.combine exprList varList in
                                              (* remove each expr bound to an unused var *) 
                                              let filteredList = List.filter (fun (_,y) -> List.mem y unusedVars) list in
                                              let filtExpr, filtVars = List.split filteredList in
                                              Success(NCase(Tuple(filtExpr), filtVars, expr))
    | _                                    -> Tr.traverse expr (aux unusedVars)
  in aux unusedVars expr
  end

module OneCaseRemoval: Optim =
functor (Tr : Traverse with type adt = Syntax.TargetLanguage.targetSyn) ->
struct
open Syntax.TargetLanguage
open Strategies.Strategy

let rec run expr = match expr with
  | Tuple(exprList) 
    when List.length exprList = 1  -> Success(List.hd exprList)
  | NCase(expr1, varList, expr2) 
    when List.length varList = 1   -> let x, ty = List.hd varList in 
                                      Success(Let(x, ty, expr1, expr2))
  | _                              -> Tr.traverse expr run 
end

module EvStrat : Strategies.EvalStrat with type adt = Syntax.TargetLanguage.targetSyn = struct
  open Strategies.Strategy
  open Syntax.TargetLanguage
  type adt = Syntax.TargetLanguage.targetSyn

  let all (strat: targetSyn strategy) : targetSyn strategy = fun expr -> TargetTr.traverse expr strat

  (* Won't be used for now *)
  let one (strat: targetSyn strategy) : targetSyn strategy  =  fun expr -> TargetTr.traverse expr strat

  (* Won't be used for now *)
  let some (strat: targetSyn strategy) : targetSyn strategy  =  fun expr -> TargetTr.traverse expr strat
end

module CTS = Strategies.CompleteTraversalStrat(EvStrat)
module DVE = DeadVarsElim(TargetTr)
module LR = LambdaRemoval(TargetTr)
module LS = LetSimplification(TargetTr)
module FS = ForwardSubstitution(TargetTr)
module LC = LetCommutativity(TargetTr)
module RF = RealFactorisation(TargetTr)
module TS = TrigoSimplification(TargetTr)
module ZS = ZeroSimplification(TargetTr)
module SAS = SimpleAlgebraicSimplifications(TargetTr)
module CP = ConstantPropagation(TargetTr)
module OCR = OneCaseRemoval(TargetTr)
open Strategies.Strategy

let fullOpti (expr: Syntax.TargetLanguage.targetSyn) = 
  run (
    let num_iter = 200 in 
    (iterate num_iter (tryStratList [FS.run; LR.run; OCR.run])   
    >> iterate num_iter (tryStratList [LS.run; LC.run; RF.run; TS.run; ZS.run; SAS.run; FS.run; LR.run; CP.run; DVE.run; OCR.run])) expr) 
