type 'a tuple = 'a list

type sourceType = Real | Prod of sourceType * sourceType

type sourceSyn = Var of Var.t * sourceType
            | Const of float 
            | Apply1 of Operators.op1 * sourceSyn 
            | Apply2 of Operators.op2 * sourceSyn * sourceSyn 
            | Let of Var.t * sourceType * sourceSyn * sourceSyn

type context = ((Var.t * sourceType), sourceSyn) CCList.Assoc.t

val to_string : sourceSyn -> string
val pp : Format.formatter -> sourceSyn -> unit

val isValue : sourceSyn -> bool
val equalTypes : sourceType -> sourceType -> bool
val equalTerms : sourceSyn -> sourceSyn ->  bool
val subst : Var.t -> sourceType -> sourceSyn -> sourceSyn -> sourceSyn
val simSubst : context -> sourceSyn -> sourceSyn
val freeVar : sourceSyn -> Var.t list
val canonicalAlphaRename : string -> sourceSyn -> sourceSyn
val typeSource : sourceSyn -> sourceType option
val isWellTyped : sourceSyn -> bool
val interpret : sourceSyn -> context -> float
