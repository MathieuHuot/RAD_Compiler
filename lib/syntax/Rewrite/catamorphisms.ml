module type Catamorphism = sig
  type adt (* a chosen syntax that needs rewriting, preferably given by an algebraic data type *)
  type pattern 
  val rule : adt -> pattern * (adt Lazy.t)  (* applies a rule on an adt depending on its pattern *)
  val catamorphism : pattern list -> adt -> adt (* applies the rule to each pattern found within an adt *)
end

module CataSource : Catamorphism with type adt = Syntax.SourceLanguage.sourceSyn and type pattern = int = struct
  open Syntax.SourceLanguage
  open Lazy

  type adt = sourceSyn
  type pattern = int

  let rule expr = match expr with 
    | Apply2(Plus,Const a,Const b)  -> 0, lazy (Const(a+.b))
    | Apply2(Times,Const a,Const b) -> 1, lazy (Const(a*.b))
    | expr                          -> 2, lazy expr

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
end