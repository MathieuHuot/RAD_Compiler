type sourceType = Real | Prod of sourceType * sourceType

and synSource = Var of Vars.var * sourceType
            | Const of float 
            | Apply1 of Operators.op1 * synSource 
            | Apply2 of Operators.op2 * synSource * synSource 
            | Let of Vars.var * sourceType * synSource * synSource

type context = (Vars.var * sourceType * synSource) list

val isValue : synSource -> bool
val freeVars: synSource -> Vars.var list
val canonicalAlphaRename: string -> synSource -> synSource
val typeSource: synSource -> sourceType
val isWellTyped: synSource -> bool
val interpreter: synSource -> context -> float 