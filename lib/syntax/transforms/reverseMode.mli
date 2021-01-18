type context = (Syntax.Var.t * Syntax.Source.Type.t) Syntax.Source.tuple

val semiNaiveReverseAD : context -> Syntax.Source.t -> Syntax.Target.t
val grad : context -> Syntax.Source.t -> Syntax.Target.t
val grad2 : context -> Syntax.Source.t -> Syntax.Target.t