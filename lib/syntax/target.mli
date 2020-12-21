(** Module for the target language *)

module VarSet : sig
  include CCSet.S with type elt = Var.t
end

type 'a tuple = 'a list

module Type : sig
  (** Type of the target language *)

  type t =
    | Real (** Type of constant *)
    | Arrow of t list * t (** Type of function *)
    | NProd of t tuple (** Type of tuple *)

  val pp : Format.formatter -> t -> unit
  (** Pretty printer *)

  val to_string : t -> string
  (** [to_string t] prints [t] in a string using {!pp} *)

  val isArrow : t -> bool
  (** [isArrow t] return true if [t] is [Arrow _] and false otherwise *)

  val sourceToTarget : Source.sourceType -> t
  (** [sourceToTarget t] map type of the source language to type of the target language *)

  val equal : t -> t -> bool
  (** Equality function *)
end

type targetSyn =
  |Var of Var.t * Type.t
  (** [Var (x,t)] is a variable [x] of type [t] *)
  | Const of float
  (** [Const f] is a real nomber [f] for example [1.] or [0.2039] *)
  | Apply1 of Operators.op1 * targetSyn
  (** [Apply1 (op, expr)] is the application of the unary operator [op] to
      [expr]: [op(expr)] *)
  | Apply2 of Operators.op2 * targetSyn * targetSyn
  (** [Apply2 (op, expr1, expr2)] is the application of the binary operator [op] to
      [expr1] and [expr2]: [op(expr1, expr1, expr22)] *)
  | Let of Var.t * Type.t * targetSyn * targetSyn
  (** [Let (x,t, expr1, expr2)] corresponds to [let (x:t) = expr1 in expr2] *)
  | Fun of ((Var.t * Type.t) list) * targetSyn
  (** [Fun (l, expr)] is a function where [l] is a list of argument and [expr] the
      bodie of the function: [fun (x1:t1), (x2:t2), … -> expr] where
      [l = [(x1,t1); (x2,t2); …]] *)
  | App of targetSyn * (targetSyn list)
  (** [App (expr, l] is the application of a function define by [expr] to some arguments
      [l]: [expr1 (expr1,expr2,…)] where [l = [expr1; expr2; …]] *)
  | Tuple of targetSyn tuple
  (** [Tuple l] is a tuple: [(expr1, expr2, … )] where [l = [expr1; expr2; …]] *)
  | NCase of targetSyn * ((Var.t * Type.t) list) * targetSyn
  (** [NCase (expr1, l, expr2] destructs tuples:
      [let (x1:t1, (x2:t2), … = (expr11, expr12, …) in expr2] where
      [expr1 = Tuple (expr11, expr12, …)] *)

type context = ((Var.t * Type.t), targetSyn) CCList.Assoc.t

val varToSyn : (Var.t * Type.t) list -> targetSyn list
(** [varToSyn l] maps each pair [(x,t)] in [l] to [Var (x,t)] *)

val pp : Format.formatter -> targetSyn -> unit
(** [Format.printf "%a@." pp expr] pretty prints [expr]*)

val to_string : targetSyn -> string
(** [to_string expr] prints [expr] in a string with {!pp} *)

val map : (targetSyn -> targetSyn) -> targetSyn -> targetSyn
(** [map f expr] applies [f] to [expr] and recursively applies [f]
    to the subterm of [f expr]*)

val fold : (targetSyn -> 'a -> 'a) -> targetSyn -> 'a -> 'a
(** [fold f expr a] applies [f] recursively to [expr] starting from the leaves of [expr] *)

val equal: ?eq:(float -> float -> bool) -> targetSyn -> targetSyn ->  bool
(** [equal ~eq expr1 expr2] compares recursively [expr1] with [expr2] using
    [eq] to compare constant term. *)

val weakEqual: targetSyn -> targetSyn ->  bool
(** [weakEqual expr1 expr2] compares recursively [expr1] with [expr2] using
    a weak equality function to compare constant term. *)

val isValue : targetSyn -> bool
(** [isValue expr] returns true if [expr] is [Const …] or [Fun _] or [Tuple _]
    and false otherwise. *)

val freeVar : targetSyn -> VarSet.t
(** [freeVar expr] returns the set of free variable in [expr]. *)

val listUnusedVar : targetSyn -> (Var.t * Type.t) list
(** [listUnusedVar expr] returns the set of bound variable define with a
    [Let] or [NCase] but not used. *)

val subst : Var.t -> Type.t -> targetSyn -> targetSyn -> targetSyn
(** [subst x t expr1 expr2] substitutes the variable [x] of type [t] with
    [expr1] in [expr2]. *)

val simSubst : context -> targetSyn -> targetSyn
(** [simSubst c expr] substitute the free variable contained in the context [c]
    in [expr]. *)

val canonicalAlphaRename : string -> targetSyn -> targetSyn
(** [canonicalAplphaRename name expr] *)

val typeTarget : targetSyn -> (Type.t, string) result
(** [typeTarget expr] tries to type [expr]. Returns [Result.Ok t] if
    [expr] as type [t] and [Reult.Error s] if [expr] cannot be type and [s]
    is the error message. *)

val isWellTyped : targetSyn -> bool
(** [isWellTyped expr] returns [true] if [expr] is well typed. *)

val strict_interpret : targetSyn -> context -> targetSyn
(** [strict_interpret expr c] takes an expression [expr] and a context [c]
    and interprets [expr] under the context [c]. [expr] need to be a well typed
    term and closed with [c].*)

val interpret : targetSyn -> context -> targetSyn
(** [interpret expr c] takes an expression [expr] and a context [c]
    and interprets [expr] under the context [c] as much as possible.
    [expr] does not need to be closed under [c] and does not need to be
    well typed.*)
