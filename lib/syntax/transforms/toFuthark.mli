type precision = Single | Double

val toFuthark : precision -> Syntax.Target.t CCList.printer
val print : precision -> Syntax.Target.t -> unit