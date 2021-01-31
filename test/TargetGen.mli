module TypeGen : sig
  val gen: int -> Syntax.Target.Type.t QCheck.Gen.t
end

val gen: (Syntax.Var.t * Syntax.Target.Type.t) Syntax.Target.tuple -> int -> Syntax.Target.Type.t -> Syntax.Target.t QCheck.Gen.t

val shrink : Syntax.Target.t QCheck.Shrink.t
