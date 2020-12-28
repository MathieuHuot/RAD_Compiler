(* Catamorphisms are generalized folds operators *)
(* There is no easy way to implement them generally in OCaml compared to FSharp or Haskell *)
(* So instead we will just provide a few generalized folds for our AST: *)
(* Two for predicates: forall, exists *)

module type Traverse = sig
  type adt
  type return
  val traverse: adt -> (return -> return -> return) -> (adt -> return) -> return
end

module SourceTr : Traverse with type adt = Syntax.Source.t and type return = bool = struct
open Syntax.Source
type adt = t
type return = bool

let rec traverse expr g f =
  match expr with
  | Var _ -> false
  | Const _ -> false
  | Apply1(_, expr) -> traverse expr g f 
  | Apply2(_, expr1, expr2) -> g (traverse expr1 g f) (traverse expr2 g f)
  | Let(_, _, expr1, expr2) -> g (traverse expr1 g f) (traverse expr2 g f) 
end

(* module type Cata = functor
  (Tr: sig 
    type adt = SourceTr.adt
    type return = SourceTr.return
    val traverse: adt -> (return -> return -> return) -> (adt -> return) -> return
    end)
  -> sig 
      (* type adt = SourceTr.adt
      type return = SourceTr.return *)
      val cata: Tr.adt -> (Tr.adt -> Tr.return) -> Tr.return end *)

  module SourceForAll =  
  functor (Tr: Traverse with type adt = Syntax.Source.t and type return = bool) ->
  struct
  open Syntax.Source
   
  let traverse = Tr.traverse

  let cata expr f = match expr with
    | Var(x,ty) -> f (Var(x,ty))
    | Const c   -> f(Const c)
    | expr      -> traverse expr (&&) f
  end
  
  module SourceExists =  
  functor (Tr: Traverse with type adt = Syntax.Source.t and type return = bool) ->
  struct
  open Syntax.Source
  
  let traverse = Tr.traverse

  let cata expr f = match expr with
    | Var(x,ty) -> f (Var(x,ty))
    | Const c   -> f(Const c)
    | expr      -> traverse expr (||) f
  end

  module IsInWeakAnf = struct
  module LR = SourceForAll(SourceTr)
  let run = fun x -> LR.cata x (fun _ -> true)
  end
