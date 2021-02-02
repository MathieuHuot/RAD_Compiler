type gradient_variables = (Syntax.Var.t * Syntax.Source.Type.t) Syntax.Source.tuple

val forwardADType : Syntax.Source.Type.t -> Syntax.Target.Type.t
val forwardAD : Syntax.Source.t -> Syntax.Target.t
val grad : gradient_variables -> Syntax.Source.t -> Syntax.Target.t list
