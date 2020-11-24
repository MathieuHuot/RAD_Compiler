module type Catamorphism = sig
  type adt (* a chosen syntax that needs rewriting, preferably given by an algebraic data type *)
  type pattern 
  val rule : adt -> pattern * (adt Lazy.t)  (* applies a rule on an adt depending on its pattern *)
  val catamorphism : pattern list -> adt -> adt (* applies the rule to each pattern found within an adt *)
  val iterate : int -> pattern list -> adt -> adt (* iterate a catamorphism a given number of times *)
end

module SourceCata : Catamorphism with type adt = Syntax.SourceLanguage.sourceSyn and type pattern = int = struct
  open Syntax.SourceLanguage
  open Lazy

  type adt = sourceSyn
  type pattern = int

  let rule expr = match expr with
    (* Constant propagation *) 
    | Apply2(Plus,Const a,Const b)  -> 0, lazy (Const(a+.b))
    | Apply2(Times,Const a,Const b) -> 1, lazy (Const(a*.b))
    (* Real factorisation *)
    | Apply2(Plus,Apply2(Times,expr1,expr2),Apply2(Times,expr3,expr4)) 
      when equalTerms expr1 expr3   -> 2, lazy (Apply2(Times,expr1,Apply2(Plus,expr2,expr4)))
    | Apply2(Plus,Apply2(Times,expr1,expr2),Apply2(Times,expr3,expr4)) 
      when equalTerms expr2 expr4   -> 3, lazy (Apply2(Times,Apply2(Plus,expr1,expr3),expr2))
    (* exp(a)exp(b) = exp(a+b) *)
    | Apply2(Times,Apply1(Exp,expr1),Apply1(Exp,expr2)) 
                                    -> 4, lazy (Apply1(Exp,Apply2(Plus,expr1,expr2)))
    (* 0 simplification *)
    | Apply2(Times,_,Const 0.)      -> 5,lazy (Const 0.)
    | Apply2(Times,Const 0.,_)      -> 6,lazy (Const 0.)
    | Apply2(Plus,expr,Const 0.)    -> 7,lazy expr
    | Apply2(Plus,Const 0.,expr)    -> 8,lazy expr
    (* 1 simplification *)
    | Apply2(Times,expr,Const 1.)   -> 9,lazy expr
    | Apply2(Times,Const 1.,expr)   -> 10,lazy expr
    (* Applies forward substitution: let x=y in e -> e[y/x] where y is a variable *)
    | Let(x,_,Var(y,ty),e)          -> 11, lazy (subst x ty (Var(y,ty)) e)
    (* let x=e1 in let y=e1 in e2 -> let x=e0 in let y=x in e2 *)
    | Let(x1,ty1,e0,Let(x2,ty2,e1,e2)) 
      when (equalTerms e0 e1)       -> 12, lazy (Let(x1,ty1,e0,Let(x2,ty2,Var(x1,ty1),e2)))
    (* let x=e0 in let y=e1 in e2 -> let y=e1 in let x=e0 in e2 (x not a FV in e1) *)
    | Let(x1,ty1,e0,Let(x2,ty2,e1,e2)) 
      when not(List.mem x1 (freeVars e1)) 
                                    -> 13, lazy (Let(x2,ty2,e1,Let(x1,ty1,e0,e2)))
    | expr                          -> 101, lazy expr

  let rec catamorphism list expr = 
    let aux expr = begin 
    match expr with
      | Var _                  -> expr
      | Const _                -> expr
      | Apply1(op,expr)        -> Apply1(op,catamorphism list expr)
      | Apply2(op,expr1,expr2) -> Apply2(op,catamorphism list expr1,catamorphism list expr2)
      | Let(x,ty,expr1,expr2)  -> Let(x,ty,catamorphism list expr1,catamorphism list expr2)
    end in 
    let f expr i =
      let (j,e) = rule expr in
      if i==j then force e else expr
    in
    aux (List.fold_left f expr list)

    let iterate n list expr = 
      let rec aux n expr = if n==0 then expr else aux (n-1) (catamorphism list expr) in 
      aux n expr
end

module TargetCata : Catamorphism with type adt = Syntax.TargetLanguage.targetSyn and type pattern = int = struct
  open Syntax.TargetLanguage
  open Lazy

  type adt = targetSyn
  type pattern = int

  let rule expr = match expr with
    (* Constant propagation *) 
    | Apply2(Plus,Const a,Const b)  -> 0, lazy (Const(a+.b))
    | Apply2(Times,Const a,Const b) -> 1, lazy (Const(a*.b))
    (* Real factorisation *)
    | Apply2(Plus,Apply2(Times,expr1,expr2),Apply2(Times,expr3,expr4)) 
      when equalTerms expr1 expr3   -> 2, lazy (Apply2(Times,expr1,Apply2(Plus,expr2,expr4)))
    | Apply2(Plus,Apply2(Times,expr1,expr2),Apply2(Times,expr3,expr4)) 
      when equalTerms expr2 expr4   -> 3, lazy (Apply2(Times,Apply2(Plus,expr1,expr3),expr2))
    (* exp(a)exp(b) = exp(a+b) *)
    | Apply2(Times,Apply1(Exp,expr1),Apply1(Exp,expr2)) 
                                    -> 4, lazy (Apply1(Exp,Apply2(Plus,expr1,expr2)))
    (* 0 simplification *)
    | Apply2(Times,_,Const 0.)      -> 5,lazy (Const 0.)
    | Apply2(Times,Const 0.,_)      -> 6,lazy (Const 0.)
    | Apply2(Plus,expr,Const 0.)    -> 7,lazy expr
    | Apply2(Plus,Const 0.,expr)    -> 8,lazy expr
    (* 1 simplification *)
    | Apply2(Times,expr,Const 1.)   -> 9,lazy expr
    | Apply2(Times,Const 1.,expr)   -> 10,lazy expr
    (* Applies forward substitution: let x=y in e -> e[y/x] where y is a variable *)
    | Let(x,_,Var(y,ty),e)          -> 11, lazy (subst x ty (Var(y,ty)) e)
    (* let x=e1 in let y=e1 in e2 -> let x=e0 in let y=x in e2 *)
    | Let(x1,ty1,e0,Let(x2,ty2,e1,e2)) 
      when (equalTerms e0 e1)       -> 12, lazy (Let(x1,ty1,e0,Let(x2,ty2,Var(x1,ty1),e2)))
    (* let x=e0 in let y=e1 in e2 -> let y=e1 in let x=e0 in e2 (x not a FV in e1) *)
    | Let(x1,ty1,e0,Let(x2,ty2,e1,e2)) 
      when not(List.mem x1 (freeVars e1)) 
                                    -> 13, lazy (Let(x2,ty2,e1,Let(x1,ty1,e0,e2)))
    (* replaces inlined lambdas in (fun x1...xn.e)[e1...en] to 
        let x1=e1 in let x2=e2 in ... in let xn=en in e
        for later optimisations like forward substitution *)                               
    | App(Fun(varList,expr),exprList) 
                                    -> 14, lazy (List.fold_left2 
                                                  (fun acc (x,ty) expr -> Let(x,ty,expr,acc)) 
                                                  expr 
                                                  (List.rev varList) 
                                                  (List.rev exprList))
    (* CBN evaluates a variable which has a function type *)
    | Let(x,ty,expr1,expr2) 
      when isArrow ty               -> 15, lazy (subst x ty expr1 expr2)
    | Case(Pair(expr1,expr2),x,ty1,y,ty2,expr3) 
      when isArrow ty2              -> 16, lazy (Let(x,ty1,expr1,subst y ty2 expr2 expr3))
    (* Constant propagation part 2 *)
    | Let(x,ty,Const(c),e)          -> 17, lazy (subst x ty (Const(c)) e)
    (* More forward substitution *)
    | Case(Pair(Var(x1,ty1),Var(x2,ty2)), x3, ty3, x4, ty4, expr) 
                                    -> 18, lazy  (subst x4 ty4 (Var(x2,ty2)) (subst x3 ty3 (Var(x1,ty1)) expr))
    (* More constant propagation *)
    | Apply1(Cos, Const c)          -> 19, lazy (Const(cos c))
    | Apply1(Sin, Const c)          -> 20, lazy (Const(sin c))
    | Apply1(Exp, Const c)          -> 21, lazy (Const(exp c))
    | Apply2(Plus,expr1,Apply1(Minus,expr2)) 
                                    -> 22, lazy (Apply2(Minus,expr1,expr2))
    | Apply2(Times,Const(-1.),expr) -> 23, lazy (Apply1(Minus,expr))
    | Case(Pair(Const c,Const d), x1, ty1, x2, ty2, expr)
                                    -> 24, lazy (subst x2 ty2 (Const d) (subst x1 ty1 (Const c) expr))
    | Apply1(Minus,Apply1(Minus,expr))
                                    -> 25, lazy expr
    | Apply1(Minus,Const c)         -> 26, lazy (Const(-.c))
    | Apply2(Minus,expr1,Apply1(Minus,expr2))
                                    -> 27, lazy (Apply2(Plus,expr1,expr2))
    (* Default, do nothing *)
    | expr                          -> 101, lazy expr

  let rec catamorphism list expr = 
    let aux expr = begin 
    match expr with
      | Var _                                -> expr
      | Const _                              -> expr
      | Apply1(op, expr)                     -> Apply1(op,catamorphism list expr)
      | Apply2(op, expr1, expr2)             -> Apply2(op,catamorphism list expr1, catamorphism list expr2)
      | Let(x, ty, expr1, expr2)             -> Let(x,ty,catamorphism list expr1, catamorphism list expr2)
      | Pair(expr1, expr2)                   -> Pair(catamorphism list expr1, catamorphism list expr2)   
      | Tuple(exprList)                      -> Tuple(List.map (catamorphism list) exprList)
      | App(expr, exprList)                  -> App(catamorphism list expr, List.map (catamorphism list) exprList)
      | Fun(varList, expr)                   -> Fun(varList, catamorphism list expr)
      | Case(expr1, x1, ty1, x2, ty2, expr2) -> Case(catamorphism list expr1,x1,ty1,x2,ty2,catamorphism list expr2)
    end in 
    let f expr i =
      let (j,e) = rule expr in
      if i==j then force e else expr
    in
    aux (List.fold_left f expr list)

    let iterate n list expr = 
      let rec aux n expr = if n==0 then expr else aux (n-1) (catamorphism list expr) in 
      aux n expr
end