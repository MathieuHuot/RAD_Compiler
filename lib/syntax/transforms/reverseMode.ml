open Anf
open Syntax.SourceLanguage
open Syntax.TargetLanguage

let naiveReverseADType (ty : sourceType) (retTy : targetType) =
  let rec nRAD (ty : sourceType) = match ty with
  | Real          -> Prod(Real, Arrow(Real,retTy))
  | Prod(ty1,ty2) -> Prod(nRAD ty1,nRAD ty2)
  in nRAD ty

let semiNaiveReverseADType (ty : sourceType) (retTy : targetType) =
    Prod(sourceToTargetType ty, Arrow(sourceToTargetType ty,retTy))

   (*FIXME: this is where I start to suffer from having pairs instead of n-ary tuples! That's annoying, 
    especially knowing it's just Intermediate Repr and going to be removed eventually! *) 
let semiNaiveReverseAD (expr : synSource) : synTarget =
  let retTy = sourceToTargetType (typeSource expr) in (*TODO: very wrong, should be type of the context*)
  let new_var = Syntax.Vars.fresh() in 
  let id_cont = Fun(new_var,retTy,Var(new_var, retTy)) in
  let rec rad (expr : synSource) (cont : synTarget) (contType : targetType) : synTarget * targetType = match expr with
    | Const c                -> let newContType = Prod(contType,Real) in
                                let newVar = Syntax.Vars.fresh() in
                                let newVar1 = Syntax.Vars.fresh() in
                                let newVar2 = Syntax.Vars.fresh() in
                                let newContCore = Case(Var(newVar,newContType),newVar1,contType,newVar2,Real,App(cont,Var(newVar1,newContType))) in
                                let newCont = Fun(newVar,newContType,newContCore) in
                                Pair(Const c,newCont), newContType
    | Var(x,ty)              -> let newContType = Prod(contType,sourceToTargetType ty) in
                                let newVar = Syntax.Vars.fresh() in
                                let newVar1 = Syntax.Vars.fresh() in
                                let newVar2 = Syntax.Vars.fresh() in
                                let newContCore = Case(Var(newVar,newContType),newVar1,contType,newVar2,Real,App(cont,Var(newVar1,newContType))) in  (*TODO: WRONG !*)
                                let newCont = Fun(newVar,newContType,newContCore) in
                                Pair(Var(x,sourceToTargetType ty),newCont), newContType
    | Apply1(op,expr)        -> failwith "TODO"
    | Apply2(op,expr1,expr2) -> failwith "TODO"
    | Let(y,ty,expr1,expr2)  -> failwith "TODO"
  in let x,_ = rad expr (id_cont) retTy 
  in x