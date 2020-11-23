type 'a tuple = 'a list

type targetType = Real 
            | Prod of targetType * targetType
            | Arrow of (targetType list ) * targetType
            | NProd of targetType tuple 

and targetSyn = Var of Vars.var * targetType
            | Const of float 
            | Apply1 of Operators.op1 * targetSyn 
            | Apply2 of Operators.op2 * targetSyn * targetSyn
            | Let of Vars.var * targetType * targetSyn * targetSyn
            | Pair of targetSyn * targetSyn
            | Fun of ((Vars.var * targetType) list) * targetSyn
            | App of targetSyn * (targetSyn list)
            | Case of targetSyn * Vars.var * targetType * Vars.var * targetType * targetSyn
            | Tuple of targetSyn tuple     

type context

val sourceToTargetType : SourceLanguage.sourceType -> targetType
val equalTerms: targetSyn -> targetSyn ->  bool
val isValue : targetSyn -> bool
val freeVars : targetSyn -> Vars.var list
val subst : Vars.var -> targetType -> targetSyn -> targetSyn -> targetSyn
val canonicalAlphaRename : string -> targetSyn -> targetSyn
val typeTarget : targetSyn -> targetType option
val isWellTyped : targetSyn -> bool
val interpret : targetSyn -> context -> targetSyn