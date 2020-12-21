(* produces a random closed term of max depth the given input *)
type varSourceContext = (Vars.t * Source.sourceType) list
type varTargetContext = (Vars.t * Target.Type.t) list

val sourceSynGen : int -> varSourceContext -> Source.sourceSyn
val targetSynGen : int -> varTargetContext -> Target.targetSyn
