module TypeGen : sig
  val gen: int -> Syntax.Source.Type.t QCheck.Gen.t
end

val gen: (Syntax.Var.t * Syntax.Source.Type.t) Syntax.Source.tuple -> int -> Syntax.Source.Type.t -> Syntax.Source.t QCheck.Gen.t

val shrink : Syntax.Source.t QCheck.Shrink.t

