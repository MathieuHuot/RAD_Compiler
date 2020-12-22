type context = (Syntax.Var.t * Syntax.Source.sourceType) Syntax.Source.tuple

val semiNaiveReverseAD : context -> Syntax.Source.sourceSyn -> Syntax.Target.t
val grad : context -> Syntax.Source.sourceSyn -> Syntax.Target.t
