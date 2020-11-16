open Anf
open Syntax.SourceLanguage
open Syntax.TargetLanguage

let naiveReverseADType (ty : sourceType) (retTy : targetType) =
  let rec nRAD (ty : sourceType) = match ty with
  | Real          -> Prod(Real, Arrow(Real,retTy))
  | Prod(ty1,ty2) -> Prod(nRAD ty1,nRAD ty2)
  in nRAD ty

let naiveReverseAD expr retTy = 
  (* let X = Var (Syntax.Vars.fresh(),Real) in *)
  let rec nRAD (expr : synSource) : synTarget = match expr with
  | Const c                -> failwith "TODO"
  | Var(x,ty)              -> failwith "TODO"
  | Apply1(op,expr)        -> failwith "TODO"
  | Apply2(op,expr1,expr2) -> failwith "TODO"
  | Let(y,ty,expr1,expr2)  -> failwith "TODO"
  in nRAD expr

let semiNaiveReverseADType (ty : sourceType) (retTy : targetType) =
    Prod(sourceToTargetType ty, Arrow(sourceToTargetType ty,retTy))