type targetType = Real 
            | Prod of targetType * targetType
            | Arrow of targetType * targetType 

and synTarget = Var of Vars.var * targetType
            | Const of float 
            | Apply1 of Operators.op1 * synTarget 
            | Apply2 of Operators.op2 * synTarget * synTarget
            | Let of Vars.var * targetType * synTarget * synTarget
            | Pair of synTarget * synTarget
            | Fun of Vars.var * targetType * synTarget
            | App of synTarget * synTarget
            | Case of synTarget * Vars.var * targetType * Vars.var * targetType * synTarget

type context

val isValue : synTarget -> bool
val freeVars: synTarget -> Vars.var list
val canonicalAlphaRename: string -> synTarget -> synTarget
val typeTarget: synTarget -> targetType
val isWellTyped: synTarget -> bool
val interpreter: synTarget -> context -> synTarget