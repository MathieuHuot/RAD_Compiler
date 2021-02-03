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

val dvar : t -> t * t
(** takes a primal var as input and returns a pair of the primal 
    variable and a new tangent variable. Assumes that no variable 
    from the initial term starts with d, in other words that the 
    newly returned variable is fresh *)

val dvar2 : t -> t * t * t 
(** Similarly as above but returns a triple *)

val dvar22 : t -> t * t * t * t 
(** Similarly as above but returns a quadruple *)

val dvar33 : t -> t * t * t * t * t * t * t * t
(** Similarly as above but returns an 8-tuple *)

module Parse : sig
  val pVar : t CCParse.t

  val of_string : string -> (t, string) Result.t
end
