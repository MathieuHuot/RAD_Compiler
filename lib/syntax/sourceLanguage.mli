type 'a tuple = 'a list

type sourceType = Real | Prod of sourceType * sourceType

and sourceSyn = Var of Vars.var * sourceType
            | Const of float 
            | Apply1 of Operators.op1 * sourceSyn 
            | Apply2 of Operators.op2 * sourceSyn * sourceSyn 
            | Let of Vars.var * sourceType * sourceSyn * sourceSyn

type context = (Vars.var * sourceType * sourceSyn) list

val isValue : sourceSyn -> bool
val equalTypes : sourceType -> sourceType -> bool
val equalTerms : sourceSyn -> sourceSyn ->  bool
val subst : Vars.var -> sourceType -> sourceSyn -> sourceSyn -> sourceSyn
val simSubst : context -> sourceSyn -> sourceSyn
val freeVars : sourceSyn -> Vars.var list
val canonicalAlphaRename : string -> sourceSyn -> sourceSyn
val typeSource : sourceSyn -> sourceType option
val isWellTyped : sourceSyn -> bool
val interpret : sourceSyn -> context -> float