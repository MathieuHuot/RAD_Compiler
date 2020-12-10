type 'a tuple = 'a list

type sourceType = Real | Prod of sourceType * sourceType

type sourceSyn = Var of Vars.t * sourceType
            | Const of float 
            | Apply1 of Operators.op1 * sourceSyn 
            | Apply2 of Operators.op2 * sourceSyn * sourceSyn 
            | Let of Vars.t * sourceType * sourceSyn * sourceSyn

type context = (Vars.t * sourceType * sourceSyn) list

val to_string : sourceSyn -> string
val pp : Format.formatter -> sourceSyn -> unit

val isValue : sourceSyn -> bool
val equalTypes : sourceType -> sourceType -> bool
val equalTerms : sourceSyn -> sourceSyn ->  bool
val subst : Vars.t -> sourceType -> sourceSyn -> sourceSyn -> sourceSyn
val simSubst : context -> sourceSyn -> sourceSyn
val freeVars : sourceSyn -> Vars.t list
val canonicalAlphaRename : string -> sourceSyn -> sourceSyn
val typeSource : sourceSyn -> sourceType option
val isWellTyped : sourceSyn -> bool
val interpret : sourceSyn -> context -> float
