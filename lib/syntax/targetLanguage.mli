type 'a tuple = 'a list

type targetType = Real 
            | Prod of targetType * targetType
            | Arrow of (targetType list ) * targetType
            | NProd of targetType tuple 

and targetSyn = Var of Vars.t * targetType
            | Const of float 
            | Apply1 of Operators.op1 * targetSyn 
            | Apply2 of Operators.op2 * targetSyn * targetSyn
            | Let of Vars.t * targetType * targetSyn * targetSyn
            | Pair of targetSyn * targetSyn
            | Fun of ((Vars.t * targetType) list) * targetSyn
            | App of targetSyn * (targetSyn list)
            | Case of targetSyn * Vars.t * targetType * Vars.t * targetType * targetSyn
            | Tuple of targetSyn tuple
            | NCase of targetSyn * ((Vars.t * targetType) list) * targetSyn     

type context = (Vars.t * targetType * targetSyn) list

val isArrow : targetType -> bool
val sourceToTargetType : SourceLanguage.sourceType -> targetType
val equalTypes : targetType -> targetType -> bool
val equalTerms: targetSyn -> targetSyn ->  bool
val isValue : targetSyn -> bool
val freeVars : targetSyn -> Vars.t list
val subst : Vars.t -> targetType -> targetSyn -> targetSyn -> targetSyn
val simSubst : context -> targetSyn -> targetSyn
val canonicalAlphaRename : string -> targetSyn -> targetSyn
val typeTarget : targetSyn -> targetType option
val isWellTyped : targetSyn -> bool
val interpret : targetSyn -> context -> targetSyn
