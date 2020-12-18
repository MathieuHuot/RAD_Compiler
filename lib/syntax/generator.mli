(* produces a random closed term of max depth the given input *)
type varSourceContext = (Vars.t * SourceLanguage.sourceType) list
type varTargetContext = (Vars.t * TargetLanguage.Type.t) list

val sourceSynGen : int -> varSourceContext -> SourceLanguage.sourceSyn
val targetSynGen : int -> varTargetContext -> TargetLanguage.targetSyn
