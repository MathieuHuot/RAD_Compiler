type sourceType = Real | Prod of sourceType * sourceType

and sourceSyn = Var of Vars.var * sourceType
            | Const of float 
            | Apply1 of Operators.op1 * sourceSyn 
            | Apply2 of Operators.op2 * sourceSyn * sourceSyn 
            | Let of Vars.var * sourceType * sourceSyn * sourceSyn

type context = (Vars.var * sourceType * sourceSyn) list

val isValue : sourceSyn -> bool
val equalTerms : sourceSyn -> sourceSyn ->  bool
val freeVars : sourceSyn -> Vars.var list
val canonicalAlphaRename : string -> sourceSyn -> sourceSyn
val typeSource : sourceSyn -> sourceType option
val isWellTyped : sourceSyn -> bool
val interpret : sourceSyn -> context -> float