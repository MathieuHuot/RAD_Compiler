type 'a tuple = 'a list

module Type : sig
  (** Type of the source language *)

  type t =
    | Real (** Type of constant *)
    | Prod of t * t(** Type of pair *)

  val pp : Format.formatter -> t -> unit
  (** Pretty printer *)

  val to_string : t -> string
  (** [to_string t] prints [t] in a string using {!pp} *)

  val equal : t -> t -> bool
  (** Equality function *)
end

type sourceSyn = Var of Var.t * Type.t
            | Const of float 
            | Apply1 of Operators.op1 * sourceSyn 
            | Apply2 of Operators.op2 * sourceSyn * sourceSyn 
            | Let of Var.t * Type.t * sourceSyn * sourceSyn

type context = ((Var.t * Type.t), sourceSyn) CCList.Assoc.t

val to_string : sourceSyn -> string
val pp : Format.formatter -> sourceSyn -> unit

val isValue : sourceSyn -> bool
val equalTerms : sourceSyn -> sourceSyn ->  bool
val subst : Var.t -> Type.t -> sourceSyn -> sourceSyn -> sourceSyn
val simSubst : context -> sourceSyn -> sourceSyn
val freeVar : sourceSyn -> Var.t list
val canonicalAlphaRename : string -> sourceSyn -> sourceSyn
val typeSource : sourceSyn -> Type.t option
val isWellTyped : sourceSyn -> bool
val interpret : sourceSyn -> context -> float
