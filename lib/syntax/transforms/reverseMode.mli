type context = (Syntax.Vars.t * Syntax.SourceLanguage.sourceType) Syntax.SourceLanguage.tuple

val naiveReverseADType : Syntax.SourceLanguage.sourceType -> Syntax.TargetLanguage.targetType -> Syntax.TargetLanguage.targetType
val semiNaiveReverseADType : Syntax.SourceLanguage.sourceType -> Syntax.TargetLanguage.targetType -> Syntax.TargetLanguage.targetType
val semiNaiveReverseAD : context -> Syntax.SourceLanguage.sourceSyn -> Syntax.TargetLanguage.targetSyn
val grad : context -> Syntax.SourceLanguage.sourceSyn -> Syntax.TargetLanguage.targetSyn
