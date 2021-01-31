val constantPropagation : Target.t -> Target.t Rewriter.output
  val simpleAlgebraicSimplifications : Target.t -> Target.t Rewriter.output
  val zeroSimplification : Target.t -> Target.t Rewriter.output
  val trigoSimplification : Target.t -> Target.t Rewriter.output
  val realFactorisation : Target.t -> Target.t Rewriter.output
  val letCommutativity : Target.t -> Target.t Rewriter.output
  val forwardSubstitution : Target.t -> Target.t Rewriter.output
  val letSimplification : Target.t -> Target.t Rewriter.output
  val lambdaRemoval : Target.t -> Target.t Rewriter.output
  val deadVarElim : Target.t -> Target.t Rewriter.output
  val oneCaseRemoval : Target.t -> Target.t Rewriter.output
  val fullOpti : Target.t -> Target.t