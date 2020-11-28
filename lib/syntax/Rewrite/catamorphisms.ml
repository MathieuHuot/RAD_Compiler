(* Module for optimisations. Somewhat similar to generalized folds in Haskell *)

module type Catamorphism = sig
  type adt (* a chosen syntax that needs rewriting, preferably given by an algebraic data type *)
  type pattern 
  val rule : adt -> pattern -> adt  (* tries to apply a pattern rewriting to an adt *)
  val catamorphism : pattern list -> adt -> adt (* applies the rule to each pattern from a chosen list to an adt *)
  val iterate : int -> pattern list -> adt -> adt (* iterate catamorphism a given number of times *)
  val normalize: pattern list -> adt -> adt (* iterate catamorphism until no rewriting changes the term anymore. Beware it might not temrinate in general *)
end 

module SourceCata : Catamorphism with type adt = Syntax.SourceLanguage.sourceSyn and type pattern = int = struct
  open Syntax.SourceLanguage

  type adt = sourceSyn
  type pattern = int

  let rule expr i = match i, expr with
  (* Constant propagation *) 
  | 0, Apply2(Plus,Const a,Const b)   -> Const(a+.b)
  | 1, Apply2(Times,Const a,Const b)  -> Const(a*.b)
  | 2, Apply1(Cos, Const c)           -> Const(cos c)
  | 3, Apply1(Sin, Const c)           -> Const(sin c)
  | 4, Apply1(Exp, Const c)           -> Const(exp c)
  | 5, Apply2(Plus,expr1,Apply1(Minus,expr2)) 
                                      -> Apply2(Minus,expr1,expr2)
  | 6, Apply2(Times,Const(-1.),expr)  -> Apply1(Minus,expr)
  | 7, Apply1(Minus,Apply1(Minus,expr))
                                      -> expr
  | 8, Apply1(Minus,Const c)          -> Const(-.c)
  | 9, Apply2(Minus,expr1,Apply1(Minus,expr2))
                                      -> Apply2(Plus,expr1,expr2)
  | 10, Let(x,ty,Const(c),e)          -> subst x ty (Const(c)) e
  (* 0 simplification *)
  | 11, Apply2(Times,_,Const 0.)      -> Const 0.
  | 12, Apply2(Times,Const 0.,_)      -> Const 0.
  | 13, Apply2(Plus,expr,Const 0.)    -> expr
  | 14, Apply2(Plus,Const 0.,expr)    -> expr
  (* 1 simplification *)
  | 15, Apply2(Times,expr,Const 1.)   -> expr
  | 16, Apply2(Times,Const 1.,expr)   -> expr
  (* Real factorisation *)
  | 17, Apply2(Plus,Apply2(Times,expr1,expr2),Apply2(Times,expr3,expr4)) 
    when equalTerms expr1 expr3       -> Apply2(Times,expr1,Apply2(Plus,expr2,expr4))
  | 18, Apply2(Plus,Apply2(Times,expr1,expr2),Apply2(Times,expr3,expr4)) 
    when equalTerms expr2 expr4       -> Apply2(Times,Apply2(Plus,expr1,expr3),expr2)
  | 19, Apply2(Plus,expr1,expr2) when equalTerms expr1 expr2 
                                      -> Apply2(Times,Const 2.,expr1)
  (* exp(a)exp(b) = exp(a+b) *)
  | 20, Apply2(Times,Apply1(Exp,expr1),Apply1(Exp,expr2)) 
                                      -> Apply1(Exp,Apply2(Plus,expr1,expr2))
  (* Let commutativity *)
  | 21, Let(x,ty1,Let(y,ty2,expr1,expr2),expr3)   
                                      -> Let(y,ty2, expr1,Let(x,ty1, expr2, expr3))
  (* Applies forward substitution: let x=y in e -> e[y/x] where y is a variable *)
  | 22, Let(x,_,Var(y,ty),e)          -> subst x ty (Var(y,ty)) e
  (* let x=e1 in let y=e1 in e2 -> let x=e0 in let y=x in e2 *)
  | 23, Let(x1,ty1,e0,Let(x2,ty2,e1,e2)) 
    when (equalTerms e0 e1)           -> Let(x1,ty1,e0,Let(x2,ty2,Var(x1,ty1),e2))
  (* let x=e0 in let y=e1 in e2 -> let y=e1 in let x=e0 in e2 (x not a FV in e1) *)
  | 24, Let(x1,ty1,e0,Let(x2,ty2,e1,e2)) when not(List.mem x1 (freeVars e1)) 
                                      -> Let(x2,ty2,e1,Let(x1,ty1,e0,e2))
  (* Default, do nothing *)
  | _,_                               -> expr

  let rec catamorphism list expr = 
    let aux expr = begin 
    match expr with
      | Var _                  -> expr
      | Const _                -> expr
      | Apply1(op,expr)        -> Apply1(op,catamorphism list expr)
      | Apply2(op,expr1,expr2) -> Apply2(op,catamorphism list expr1,catamorphism list expr2)
      | Let(x,ty,expr1,expr2)  -> Let(x,ty,catamorphism list expr1,catamorphism list expr2)
    end in 
    aux (List.fold_left rule expr list)

    let iterate n list expr = 
      let rec aux n expr = if n==0 then expr else aux (n-1) (catamorphism list expr) in 
      aux n expr

    let rec normalize list expr =
      let rewrittenExpr = catamorphism list expr in
      if equalTerms rewrittenExpr expr then expr
      else  normalize list rewrittenExpr
end

module TargetCata : Catamorphism with type adt = Syntax.TargetLanguage.targetSyn and type pattern = int = struct
  open Syntax.TargetLanguage

  type adt = targetSyn
  type pattern = int

  let isVar expr = match expr with
    | Var(_) -> true
    | _      -> false

  let isConst expr = match expr with
    | Const(_) -> true
    | _        -> false

  let rule expr i = match i, expr with
    (* Constant propagation *) 
    | 0, Apply2(Plus,Const a,Const b)   -> Const(a+.b)
    | 1, Apply2(Times,Const a,Const b)  -> Const(a*.b)
    | 2, Apply1(Cos, Const c)           -> Const(cos c)
    | 3, Apply1(Sin, Const c)           -> Const(sin c)
    | 4, Apply1(Exp, Const c)           -> Const(exp c)
    | 34, Apply1(Power n, Const c)      -> Const (c ** float_of_int n)
    (* Simple Algebraic simplifications *)
    | 5, Apply2(Plus,expr1,Apply1(Minus,expr2)) 
                                        -> Apply2(Minus,expr1,expr2)
    | 6, Apply2(Times,Const(-1.),expr)  -> Apply1(Minus,expr)
    | 7, Case(Pair(Const c,Const d), x1, ty1, x2, ty2, expr)
                                        -> subst x2 ty2 (Const d) (subst x1 ty1 (Const c) expr)
    | 8, Apply1(Minus,Apply1(Minus,expr))
                                        -> expr
    | 9, Apply1(Minus,Const c)          -> Const(-.c)
    | 10, Apply2(Minus,expr1,Apply1(Minus,expr2))
                                        -> Apply2(Plus,expr1,expr2)
    | 11, Let(x,ty,Const(c),e)          -> subst x ty (Const(c)) e
    | 32, Apply2(Times,Apply1(Minus,expr1),expr2) 
                                        -> Apply1(Minus,Apply2(Times,expr1,expr2))
    | 33, Apply2(Times,expr1,Apply1(Minus,expr2)) 
                                        -> Apply1(Minus,Apply2(Times,expr1,expr2))
    | 35, Apply1(Power n, Apply1(Minus, expr))
                                        -> if n mod 2==0 
                                            then Apply1(Power n,expr)
                                            else Apply1(Minus,Apply1(Power n,expr))
    | 36, Apply1(Power n,Apply1(Exp,expr))
                                        -> Apply1(Exp,Apply2(Times,Const(float_of_int n),expr))
    (* Basic rules for sin, cos *)
    | 37, Apply1(Sin,Apply1(Minus,expr))-> Apply1(Minus,Apply1(Sin,expr))
    | 38, Apply1(Cos,Apply1(Minus,expr))-> Apply1(Cos,expr)
    | 39, Apply2(Plus,Apply1(Power 2,Apply1(Sin,expr1)),Apply1(Power 2,Apply1(Cos,expr2)))
      when equalTerms expr1 expr2       -> Const 1. 
    (* 0 simplification *)
    | 12, Apply2(Times,_,Const 0.)      -> Const 0.
    | 13, Apply2(Times,Const 0.,_)      -> Const 0.
    | 14, Apply2(Plus,expr,Const 0.)    -> expr
    | 15, Apply2(Plus,Const 0.,expr)    -> expr
    (* 1 simplification *)
    | 16, Apply2(Times,expr,Const 1.)   -> expr
    | 17, Apply2(Times,Const 1.,expr)   -> expr
    (* Real factorisation *)
    | 18, Apply2(Plus,Apply2(Times,expr1,expr2),Apply2(Times,expr3,expr4)) 
      when equalTerms expr1 expr3       -> Apply2(Times,expr1,Apply2(Plus,expr2,expr4))
    | 19, Apply2(Plus,Apply2(Times,expr1,expr2),Apply2(Times,expr3,expr4)) 
      when equalTerms expr2 expr4       -> Apply2(Times,Apply2(Plus,expr1,expr3),expr2)
    | 20, Apply2(Plus,expr1,expr2) when equalTerms expr1 expr2 
                                        -> Apply2(Times,Const 2.,expr1)
    (* exp(a)exp(b) = exp(a+b) *)
    | 21, Apply2(Times,Apply1(Exp,expr1),Apply1(Exp,expr2)) 
                                        -> Apply1(Exp,Apply2(Plus,expr1,expr2))
    (* Let commutativity *)
    | 22, Let(x,ty1,Let(y,ty2,expr1,expr2),expr3)   
                                        -> Let(y,ty2, expr1,Let(x,ty1, expr2, expr3))
    | 23, Case(Let(x1,ty1,expr1,expr2),x2,ty2,x3,ty3,expr3)
                                        -> Let(x1,ty1,expr1,Case(expr2,x2,ty2,x3,ty3,expr3))
    | 24, Case(Case(expr1,x1,ty1,x2,ty2,expr2),x3,ty3,x4,ty4,expr3)
                                        -> Case(expr1,x1,ty1,x2,ty2,Case(expr2,x3,ty3,x4,ty4,expr3))
    | 40, NCase(NCase(expr1,varList1,expr2),varList2,expr3)
                                        -> NCase(expr1,varList1,NCase(expr2,varList2,expr3))
    | 41, NCase(Let(x1,ty1,expr1,expr2),varList,expr3)
                                        -> Let(x1,ty1,expr1,NCase(expr2,varList,expr3))
    | 42, NCase(Case(expr1,x1,ty1,x2,ty2,expr2),varList,expr3) 
                                        -> Case(expr1,x1,ty1,x2,ty2,NCase(expr2,varList,expr3))
    | 43, Case(NCase(expr1,varList,expr2),x1,ty1,x2,ty2,expr3)
                                        -> NCase(expr1,varList,Case(expr2,x1,ty1,x2,ty2,expr3))
    | 44, Let(x,ty,Case(expr1,x1,ty1,x2,ty2,expr2),expr3)
                                        -> Case(expr1,x1,ty1,x2,ty2,Let(x,ty,expr2,expr3))
    | 45, Let(x,ty,NCase(expr1,varList,expr2),expr3)
                                        -> NCase(expr1,varList,Let(x,ty,expr2,expr3))
    (* Applies forward substitution: let x=y in e -> e[y/x] where y is a variable *)
    | 25, Let(x,_,Var(y,ty),e)          -> subst x ty (Var(y,ty)) e
    | 26, Case(Pair(expr1,expr2), x3, ty3, x4, ty4, expr) 
      when isVar expr1 || isVar expr2 || isConst expr1 || isConst expr2                                   
                                        -> subst x4 ty4 expr1 (subst x3 ty3 expr2 expr)
    | 46, NCase(Tuple(exprList),varList,expr)
      when List.for_all (fun x -> isVar x || isConst x) exprList
                                        -> simSubst (List.map (fun ((x,y),z) -> x,y,z) (List.combine varList exprList)) expr 
    (* let x=e1 in let y=e1 in e2 -> let x=e0 in let y=x in e2 *)
    | 27, Let(x1,ty1,e0,Let(x2,ty2,e1,e2)) 
      when (equalTerms e0 e1)           -> Let(x1,ty1,e0,Let(x2,ty2,Var(x1,ty1),e2))
    (* let x=e0 in let y=e1 in e2 -> let y=e1 in let x=e0 in e2 (x not a FV in e1) *)
    | 28, Let(x1,ty1,e0,Let(x2,ty2,e1,e2)) when not(List.mem x1 (freeVars e1)) 
                                        -> Let(x2,ty2,e1,Let(x1,ty1,e0,e2))
    (* replaces inlined lambdas in (fun x1...xn.e)[e1...en] to 
        let x1=e1 in let x2=e2 in ... in let xn=en in e
        for later optimisations like forward substitution *)                               
    | 29, App(Fun(varList,expr),exprList) 
                                        -> List.fold_left2 
                                                  (fun acc (x,ty) expr -> Let(x,ty,expr,acc)) 
                                                  expr 
                                                  (List.rev varList) 
                                                  (List.rev exprList)
    (* CBN evaluates a variable which has a function type *)
    | 30, Let(x,ty,expr1,expr2) 
      when isArrow ty                   -> subst x ty expr1 expr2
    | 31, Case(Pair(expr1,expr2),x,ty1,y,ty2,expr3) 
      when isArrow ty2                  -> Let(x,ty1,expr1,subst y ty2 expr2 expr3)
    (* Default, do nothing *)
    | _,_                               -> expr

  let rec catamorphism lis expr = 
    let aux expr = begin 
    match expr with
      | Var _                                -> expr
      | Const _                              -> expr
      | Apply1(op, expr)                     -> Apply1(op,catamorphism lis expr)
      | Apply2(op, expr1, expr2)             -> Apply2(op,catamorphism lis expr1, catamorphism lis expr2)
      | Let(x, ty, expr1, expr2)             -> Let(x,ty,catamorphism lis expr1, catamorphism lis expr2)
      | Pair(expr1, expr2)                   -> Pair(catamorphism lis expr1, catamorphism lis expr2)   
      | Tuple(exprList)                      -> Tuple(List.map (catamorphism lis) exprList)
      | App(expr, exprList)                  -> App(catamorphism lis expr, List.map (catamorphism lis) exprList)
      | Fun(varList, expr)                   -> Fun(varList, catamorphism lis expr)
      | Case(expr1, x1, ty1, x2, ty2, expr2) -> Case(catamorphism lis expr1,x1,ty1,x2,ty2,catamorphism lis expr2)
      | NCase(expr1, varList, expr2)         -> NCase(catamorphism lis expr1, varList, catamorphism lis expr2) 
    end in 
    (* try rewrite i on expr *)
    (* for all i in lis *)
    aux (List.fold_left rule expr lis)

    (* iterate catamorphism n times on expr *)
    let iterate n lis expr = 
      let rec aux n expr = if n==0 then expr else aux (n-1) (catamorphism lis expr) in 
      aux n expr

    let rec normalize list expr =
      let rewrittenExpr = catamorphism list expr in
      if equalTerms rewrittenExpr expr then expr
      else  normalize list rewrittenExpr 
end