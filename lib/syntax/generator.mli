(* produces a random closed term of max depth the given input *)
type varSourceContext = (Var.t * Source.sourceType) list
type varTargetContext = (Var.t * Target.Type.t) list

val sourceSynGen : int -> varSourceContext -> Source.sourceSyn
val tGen : int -> varTargetContext -> Target.t
