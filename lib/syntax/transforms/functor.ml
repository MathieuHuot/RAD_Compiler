
module type RealFunctor = sig
  type sourceTerms
  type sourceTypes
  type targetTerms
  type targetTypes
  val mapTerms : sourceTerms -> targetTerms
  val mapTypes : sourceTypes -> targetTypes
  val verifier : (sourceTerms -> sourceTypes) -> (targetTerms -> targetTypes) -> bool
end
