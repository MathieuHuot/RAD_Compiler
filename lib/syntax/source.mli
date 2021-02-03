(** Module for the source language *)

module VarSet : sig
  include CCSet.S with type elt = Var.t
end

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

  module Parse : sig
    val pType : t CCParse.t

    val of_string : string -> t CCParse.or_error
  end
end

type t =
  | Var of Var.t * Type.t
  (** [Var (x,t)] is a variable [x] of type [t] *)
  | Const of float
  (** [Const f] is a real nomber [f] for example [1.] or [0.2039] *)
  | Apply1 of Operators.op1 * t
  (** [Apply1 (op, expr)] is the application of the unary operator [op] to
      [expr]: [op(expr)] *)
  | Apply2 of Operators.op2 * t * t
  (** [Apply2 (op, expr1, expr2)] is the application of the binary operator [op] to
      [expr1] and [expr2]: [op(expr1, expr1, expr22)] *)
  | Let of Var.t * Type.t * t * t
  (** [Let (x,t, expr1, expr2)] corresponds to [let (x:t) = expr1 in expr2] *)

type context = ((Var.t * Type.t), t) CCList.Assoc.t
(** Type of a context. Associate a variable and its type to an expression*)

val pp : Format.formatter -> t -> unit
(** [Format.printf "%a@." pp expr] pretty prints [expr]*)

val to_string : t -> string
(** [to_string expr] prints [expr] in a string with {!pp} *)

val map : (t -> t) -> t -> t
(** [map f expr] applies [f] to [expr] and recursively applies [f]
    to the subterm of [f expr]*)

val fold : (t -> 'a -> 'a) -> t -> 'a -> 'a
(** [fold f expr a] applies [f] recursively to [expr] starting from the leaves of [expr] *)

val equal: ?eq:(float -> float -> bool) -> t -> t ->  bool
(** [equal ~eq expr1 expr2] compares recursively [expr1] with [expr2] using
    [eq] to compare constant term. *)

val isValue : t -> bool
(** [isValue expr] returns true if [expr] is [Const …] and false otherwise. *)

val subst : Var.t -> Type.t -> t -> t -> t
(** [subst x t expr1 expr2] substitutes the variable [x] of type [t] with
    [expr1] in [expr2]. *)

val simSubst : context -> t -> t
(** [simSubst c expr] substitute the free variable contained in the context [c]
    in [expr]. *)

val freeVar : t -> VarSet.t
(** [freeVar expr] returns the set of free variable in [expr]. *)

val canonicalAlphaRename : string -> t -> t
(** [canonicalAplphaRename name expr] *)

val inferType : t -> (Type.t, string) result
(** [inferType expr] tries to type [expr]. Returns [Result.Ok t] if
    [expr] as type [t] and [Reult.Error s] if [expr] cannot be type and [s]
    is the error message. *)

val isWellTyped : t -> bool
(** [isWellTyped expr] returns [true] if [expr] is well typed. *)

val interpret : t -> context -> float
(** [strict_interpret expr c] takes an expression [expr] and a context [c]
    and interprets [expr] under the context [c]. [expr] need to be a well typed
    term and closed with [c].*)

(** {2 Traverse} *)
module Traverse : functor (S: Strategy.S) -> sig
  val map : (t -> t Rewriter.output) -> t -> t Rewriter.output
end

(** {2 Parser} *)
module Parse : sig
  val pTerm : t CCParse.t

  val of_string : string -> t CCParse.or_error
end
