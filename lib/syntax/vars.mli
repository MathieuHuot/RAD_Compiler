type t = string * int
val fresh : unit -> t
val equal : t -> t -> bool
val to_string : t -> string
val pp : Format.formatter -> t -> unit
