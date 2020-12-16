type context = (Syntax.Vars.t * Syntax.SourceLanguage.sourceType) Syntax.SourceLanguage.tuple

val semiNaiveReverseAD : context -> Syntax.SourceLanguage.sourceSyn -> Syntax.TargetLanguage.targetSyn
val grad : context -> Syntax.SourceLanguage.sourceSyn -> Syntax.TargetLanguage.targetSyn
