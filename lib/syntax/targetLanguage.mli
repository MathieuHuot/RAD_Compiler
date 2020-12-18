module VarSet : sig
  include CCSet.S with type elt = Vars.t
end

type 'a tuple = 'a list

module Type : sig
  type t = Real | Arrow of t list * t | NProd of t tuple

  val pp : Format.formatter -> t -> unit
  val to_string : t -> string
  val isArrow : t -> bool
  val sourceToTarget : SourceLanguage.sourceType -> t
  val equal : t -> t -> bool
end

type targetSyn =
  |Var of Vars.t * Type.t
  (* x *)
  | Const of float
  (* 1. | 0.2039 *)
  | Apply1 of Operators.op1 * targetSyn
  (* op1 (expr) *)
  | Apply2 of Operators.op2 * targetSyn * targetSyn
  (* op2 (expr1, expr2) *)
  | Let of Vars.t * Type.t * targetSyn * targetSyn
  (* let x = expr1 in expr2 *)
  | Fun of ((Vars.t * Type.t) list) * targetSyn
  (* fun x1,x2,… -> expr *)
  | App of targetSyn * (targetSyn list)
  (* expr1 (expr2) *)
  | Tuple of targetSyn tuple
  (* (expr1, expr2, … ) *)
  | NCase of targetSyn * ((Vars.t * Type.t) list) * targetSyn
  (* let x1,x2,x3,… = expr1 in expr2 *)

type context = ((Vars.t * Type.t), targetSyn) CCList.Assoc.t

val varToSyn : (Vars.t * Type.t) tuple -> targetSyn tuple
val to_string : targetSyn -> string
val pp : Format.formatter -> targetSyn -> unit

val map : (targetSyn -> targetSyn) -> targetSyn -> targetSyn
val fold : (targetSyn -> 'a -> 'a) -> targetSyn -> 'a -> 'a

val equal: ?eq:(float -> float -> bool) -> targetSyn -> targetSyn ->  bool
val weakEqual: targetSyn -> targetSyn ->  bool
val isValue : targetSyn -> bool
val freeVars : targetSyn -> VarSet.t
val listUnusedVars : targetSyn -> (Vars.t * Type.t) list
val subst : Vars.t -> Type.t -> targetSyn -> targetSyn -> targetSyn
val simSubst : context -> targetSyn -> targetSyn
val canonicalAlphaRename : string -> targetSyn -> targetSyn
val typeTarget : targetSyn -> (Type.t, string) result
val isWellTyped : targetSyn -> bool
val strict_interpret : targetSyn -> context -> targetSyn
val interpret : targetSyn -> context -> targetSyn
