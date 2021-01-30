(** Module for the source language *)

module VarSet : sig
  include CCSet.S with type elt = Var.t
end

type 'a tuple = 'a list

module Type : sig
  (** Type of the source language *)

  type t =
    | Real (** Type of constants *)
    | Prod of t * t(** Type of pairs *)
    | Array of t (** Type of arrays *)

  val pp : Format.formatter -> t -> unit
  (** Pretty printer *)

  val to_string : t -> string
  (** [to_string t] prints [t] in a string using {!pp} *)

  val equal : t -> t -> bool
  (** Equality function *)

  val isGroundType : t -> bool 
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
  | Map of Var.t * Type.t * t * t  (** map x ty e1 [a1,...,an] = [e1[a1/x],...,e1[an/x]] *)
  | Map2 of Var.t * Type.t * Var.t * Type.t * t * t * t (** map2 x ty2 y ty2 e1 [a1,...,an] [b1,...,bn] = [e1[a1/x,b1/y],...,e1[an/x,bn/y]] *)
  | Reduce of Var.t *  Type.t * Var.t * Type.t * t * t * t (** reduce x y e1 z A means reduce (x,y -> e1) from z on A *)
  | Scan of Var.t * Type.t * Var.t * Type.t * t * t * t   (** scan x ty1 y ty2 e1 z A *)
  | Get of int * t (** get i [a1,...,an] returns ai *)
  | Fold of  Var.t * Type.t * Var.t * Type.t * t * t * t(** fold z x ty1 y ty2 e z A means fold A from z with (x:ty1, y:ty2 -> e) *)
  | Array of t list 

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
