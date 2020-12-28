(* produces a random closed term of max depth the given input *)
type varSourceContext = (Var.t * Source.Type.t) list
type varTargetContext = (Var.t * Target.Type.t) list

val sourceSynGen : int -> varSourceContext -> Source.t
val targetSynGen : int -> varTargetContext -> Target.t
