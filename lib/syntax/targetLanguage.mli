module VarSet : sig
  include CCSet.S with type elt = Vars.t
end

type 'a tuple = 'a list

type targetType = Real 
            | Arrow of targetType list * targetType
            | NProd of targetType tuple 

and targetSyn =
  |Var of Vars.t * targetType
  (* x *)
  | Const of float
  (* 1. | 0.2039 *)
  | Apply1 of Operators.op1 * targetSyn
  (* op1 (expr) *)
  | Apply2 of Operators.op2 * targetSyn * targetSyn
  (* op2 (expr1, expr2) *)
  | Let of Vars.t * targetType * targetSyn * targetSyn
  (* let x = expr1 in expr2 *)
  | Fun of ((Vars.t * targetType) list) * targetSyn
  (* fun x1,x2,… -> expr *)
  | App of targetSyn * (targetSyn list)
  (* expr1 (expr2) *)
  | Tuple of targetSyn tuple
  (* (expr1, expr2, … ) *)
  | NCase of targetSyn * ((Vars.t * targetType) list) * targetSyn
  (* let x1,x2,x3,… = expr1 in expr2 *)

type context = ((Vars.t * targetType), targetSyn) CCList.Assoc.t

val to_string : targetSyn -> string
val pp : Format.formatter -> targetSyn -> unit

val isArrow : targetType -> bool
val sourceToTargetType : SourceLanguage.sourceType -> targetType
val equalTypes : targetType -> targetType -> bool
val equalTerms: ?eq:(float -> float -> bool) -> targetSyn -> targetSyn ->  bool
val weakEqualTerms: targetSyn -> targetSyn ->  bool
val isValue : targetSyn -> bool
val freeVars : targetSyn -> VarSet.t
val subst : Vars.t -> targetType -> targetSyn -> targetSyn -> targetSyn
val simSubst : context -> targetSyn -> targetSyn
val canonicalAlphaRename : string -> targetSyn -> targetSyn
val typeTarget : targetSyn -> (targetType, string) result
val isWellTyped : targetSyn -> bool
val interpret : targetSyn -> context -> targetSyn
