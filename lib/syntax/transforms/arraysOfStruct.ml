open Syntax
open Operators

module Type = struct
  type t = Real | Arrow of t list * t | NProd of t list | Array of int * t
end

type t = Var of Var.t * Type.t | Const of float | Apply1 of op1 * t | Apply2 of op2 * t * t | Let of Var.t * Type.t * t * t
| Fun of ((Var.t * Type.t) list) * t | App of t * (t list) | Tuple of t list | NCase of t * ((Var.t * Type.t) list) * t | Map of Var.t * Type.t * t * t  
| Map2 of Var.t * Type.t * Var.t * Type.t * t * t * t | Map3 of Var.t * Type.t * Var.t * Type.t * Var.t * Type.t * t * t * t * t 
| Reduce of Var.t *  Type.t * Var.t * Type.t * t * t * t | Scan of Var.t * Type.t * Var.t * Type.t * t * t * t | Zip of t * t 
| Unzip of t| Zip3 of t * t * t | Unzip3 of t | Get of int * t | Fold of  Var.t * Type.t * Var.t * Type.t * t * t * t | Array of t list 
| AoS of t | SoA of t

let rec type_embedding (ty: Target.Type.t) : Type.t =
  match ty with 
  | Target.Type.Real -> Real
  | Target.Type.NProd(tyList) -> NProd(List.map type_embedding tyList)
  | Target.Type.Arrow(tyList, ty) ->Arrow(List.map type_embedding tyList, type_embedding ty)
  | Target.Type.Array(n, ty) -> Array(n, type_embedding ty)

let rec embedding (expr: Target.t) : t = match expr with
  | Target.Var(x, ty) -> Var(x, type_embedding ty)
  | Target.Const c -> Const c
  | Target.Apply1(op, expr) -> Apply1(op, embedding expr)
  | Target.Apply2(op, expr1, expr2) -> Apply2(op, embedding expr1, embedding expr2)
  | Target.Let(x, ty, expr1, expr2) -> Let(x, type_embedding ty, embedding expr1, embedding expr2)
  | Target.App(expr1, exprList) -> App(embedding expr1,List.map embedding exprList)
  | Target.Fun(varList, expr) -> Fun(List.map (fun (x, ty) -> (x, type_embedding ty)) varList, embedding expr)
  | Target.Tuple(exprList) -> Tuple(List.map embedding exprList)
  | Target.NCase(expr1, varList, expr2) -> NCase(embedding expr1, List.map (fun (x, ty) -> (x, type_embedding ty)) varList,  embedding expr2)
  | Target.Map(x, ty, expr1, expr2) -> Map(x, type_embedding ty, embedding expr1, embedding expr2)
  | Target.Map2(x1, ty1, x2, ty2, expr1, expr2, expr3) -> Map2(x1, type_embedding ty1, x2, type_embedding ty2, embedding expr1, embedding expr2, embedding expr3)
  | Target.Map3(x1, ty1, x2, ty2, x3, ty3, expr1, expr2, expr3, expr4) -> Map3(x1, type_embedding ty1, x2, type_embedding ty2, x3, type_embedding ty3 ,embedding expr1, embedding expr2, embedding expr3, embedding expr4) 
  | Target.Reduce(x1, ty1, x2, ty2, expr1, expr2, expr3) -> Reduce(x1, type_embedding ty1, x2, type_embedding ty2, embedding expr1, embedding expr2, embedding expr3) 
  | Target.Scan(x1, ty1, x2, ty2, expr1, expr2, expr3) -> Scan(x1, type_embedding ty1, x2, type_embedding ty2, embedding expr1, embedding expr2, embedding expr3) 
  | Target.Fold(x1, ty1, x2, ty2, expr1, expr2, expr3) -> Fold(x1, type_embedding ty1, x2, type_embedding ty2, embedding expr1, embedding expr2, embedding expr3) 
  | Target.Zip(expr1, expr2) -> Zip(embedding expr1, embedding expr2)
  | Target.Zip3(expr1, expr2, expr3) -> Zip3(embedding expr1, embedding expr2, embedding expr3) 
  | Target.Unzip(expr) -> Unzip(embedding expr)
  | Target.Unzip3(expr) -> Unzip3(embedding expr)
  | Target.Array (exprList) -> Array(List.map embedding exprList)
  | Target.Get(n, expr) -> Get(n, embedding expr)

let soa_init (expr: t) = SoA (AoS (expr))

let rec type_projection (ty: Type.t) : Target.Type.t =
    match ty with 
    | Real -> Target.Type.Real
    | NProd(tyList) -> Target.Type.NProd(List.map type_projection tyList)
    | Arrow(tyList, ty) -> Target.Type.Arrow(List.map type_projection tyList, type_projection ty)
    | Array(n, ty) -> Target.Type.Array(n, type_projection ty)

let rec projection (expr: t) : Target.t = match expr with
  | SoA _ -> failwith "cannot be projected back to Target.t"
  | AoS _ -> failwith "cannot be projected back to Target.t"
  | Var(x, ty) -> Var(x,  type_projection ty)
  | Const c -> Const c
  | Apply1(op, expr) -> Apply1(op, projection expr)
  | Apply2(op, expr1, expr2) -> Apply2(op, projection expr1, projection expr2)
  | Let(x, ty, expr1, expr2) -> Let(x,  type_projection ty, projection expr1, projection expr2)
  | App(expr1, exprList) -> App(projection expr1,List.map projection exprList)
  | Fun(varList, expr) -> Fun(List.map (fun (x, ty) -> (x,  type_projection ty)) varList, projection expr)
  | Tuple(exprList) -> Tuple(List.map projection exprList)
  | NCase(expr1, varList, expr2) -> NCase(projection expr1, List.map (fun (x, ty) -> (x,  type_projection ty)) varList,  projection expr2)
  | Map(x, ty, expr1, expr2) -> Map(x,  type_projection ty, projection expr1, projection expr2)
  | Map2(x1, ty1, x2, ty2, expr1, expr2, expr3) -> Map2(x1,  type_projection ty1, x2,  type_projection ty2, projection expr1, projection expr2, projection expr3)
  | Map3(x1, ty1, x2, ty2, x3, ty3, expr1, expr2, expr3, expr4) -> Map3(x1,  type_projection ty1, x2,  type_projection ty2, x3,  type_projection ty3 ,projection expr1, projection expr2, projection expr3, projection expr4) 
  | Reduce(x1, ty1, x2, ty2, expr1, expr2, expr3) -> Reduce(x1,  type_projection ty1, x2,  type_projection ty2, projection expr1, projection expr2, projection expr3) 
  | Scan(x1, ty1, x2, ty2, expr1, expr2, expr3) -> Scan(x1,  type_projection ty1, x2,  type_projection ty2, projection expr1, projection expr2, projection expr3) 
  | Fold(x1, ty1, x2, ty2, expr1, expr2, expr3) -> Fold(x1,  type_projection ty1, x2,  type_projection ty2, projection expr1, projection expr2, projection expr3) 
  | Zip(expr1, expr2) -> Zip(projection expr1, projection expr2)
  | Zip3(expr1, expr2, expr3) -> Zip3(projection expr1, projection expr2, projection expr3) 
  | Unzip(expr) -> Unzip(projection expr)
  | Unzip3(expr) -> Unzip3(projection expr)
  | Array (exprList) -> Array(List.map projection exprList)
  | Get(n, expr) -> Get(n, projection expr)

let rec reduction (expr: t) = match expr with
| _ -> failwith "TODO"

let arrayOfStructConversion (expr: Target.t) : Target.t =
  expr |> embedding |> soa_init |> reduction |> projection