(** Module for the variable of the target and source language *)

type t = string * int
(** A variable is a name and a numbre, for example  *)

val fresh : unit -> t
(** [fresh ()] create a fresh variable assuming that the name ["y"] is not used. *)

val equal : t -> t -> bool
(** Equality between variables *)

val pp : Format.formatter -> t -> unit
(** Pretty printer *)

val to_string : t -> string
(** [to_string v] print [v] in a string using {!pp} *)
