module Precision : sig
type t
end  

val toFuthark : Precision.t -> Syntax.Target.t CCList.printer
val print : Precision.t -> Syntax.Target.t -> unit