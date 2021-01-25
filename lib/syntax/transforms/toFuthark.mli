module Precision : sig
  type t = Single | Double
end  

val toFuthark : Precision.t -> Syntax.Target.t CCList.printer
val pp : Precision.t -> Syntax.Target.t -> unit