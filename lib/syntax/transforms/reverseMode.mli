type gradient_variables = (Syntax.Var.t * Syntax.Source.Type.t) Syntax.Source.tuple

val semiNaiveReverseAD : gradient_variables -> Syntax.Source.t -> Syntax.Target.t
val grad : gradient_variables -> Syntax.Source.t -> Syntax.Target.t
val grad2 : gradient_variables -> Syntax.Source.t -> Syntax.Target.t
