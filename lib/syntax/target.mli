(** Module for the target language *)

module VarSet : sig
  include CCSet.S with type elt = Var.t
end

type 'a tuple = 'a list

module Type : sig
  (** Type of the target language *)

  type t =
    | Real (** Type of constants *)
    | Arrow of t list * t (** Type of functions *)
    | NProd of t tuple (** Type of tuples *)
    | Array of int * t (** Type of arrays with fixed known size *)

  val pp : Format.formatter -> t -> unit
  (** Pretty printer *)

  val to_string : t -> string
  (** [to_string t] prints [t] in a string using {!pp} *)

  val isArrow : t -> bool
  (** [isArrow t] return true if [t] is [Arrow _] and false otherwise *)

  val isGroundType : t -> bool

  val from_source : Source.Type.t -> t
  (** [from_source t] map type of the source language to type of the target language *)

  val equal : t -> t -> bool
  (** Equality function *)

  module Parse : sig
    val pType : t CCParse.t

    val of_string : string -> t CCParse.or_error
  end
end

type t =
  |Var of Var.t * Type.t
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
  | Fun of ((Var.t * Type.t) list) * t
  (** [Fun (l, expr)] is a function where [l] is a list of argument and [expr] the
      bodie of the function: [fun (x1:t1), (x2:t2), … -> expr] where
      [l = [(x1,t1); (x2,t2); …]] *)
  | App of t * (t list)
  (** [App (expr, l] is the application of a function define by [expr] to some arguments
      [l]: [expr1 (expr1,expr2,…)] where [l = [expr1; expr2; …]] *)
  | Tuple of t tuple
  (** [Tuple l] is a tuple: [(expr1, expr2, … )] where [l = [expr1; expr2; …]] *)
  | NCase of t * ((Var.t * Type.t) list) * t
  (** [NCase (expr1, l, expr2] destructs tuples:
      [let (x1:t1, (x2:t2), … = (expr11, expr12, …) in expr2] where
      [expr1 = Tuple (expr11, expr12, …)] *)
  | Map of Var.t * Type.t * t * t  (** map x ty e1 [a1,...,an] = [e1[a1/x],...,e1[an/x]] *)
  | Map2 of Var.t * Type.t * Var.t * Type.t * t * t * t (** map2 x ty1 y ty2 e1 [a1,...,an] [b1,...,bn] = [e1[a1/x,b1/y],...,e1[an/x,bn/y]] *)
  | Map3 of Var.t * Type.t * Var.t * Type.t * Var.t * Type.t * t * t * t * t (** map3 x1 ty1 x2 ty2 x3 ty3 e [a1,...,an] [b1,...,bn] [c1,...,cn] = [e[a1/x1,b1/x2,c1/x3],...,e[an/x1,bn/x2,cn/x3]] *) 
  | Reduce of Var.t *  Type.t * Var.t * Type.t * t * t * t (** reduce x y e1 z A means reduce (x,y -> e1) from z on A *)
  | Scan of Var.t * Type.t * Var.t * Type.t * t * t * t   (** scan x ty1 y ty2 e1 z A *)
  | Zip of t * t (** zip [a1,...,an] [b1,...,bn] = [(a1,b1),...,(an,bn)] *)
  | Unzip of t (** Unzip [(a1,b1),...,(an,bn)] = [a1,...,an],[b1,...,bn] =  *)
  | Zip3 of t * t * t (** zip [a1,...,an] [b1,...,bn] [c1,...,cn] = [(a1,b1,c1),...,(an,bn,cn)] *)
  | Unzip3 of t (** Unzip  [(a1,b1,c1),...,(an,bn,cn)] = [a1,...,an],[b1,...,bn], [c1,...,cn] =  *)
  | Fold of  Var.t * Type.t * Var.t * Type.t * t * t * t(** fold z x ty1 y ty2 e z A means fold A from z with (x:ty1, y:ty2 -> e). It's a fold LEFT operator. *)
  | Array of t list      

type context = ((Var.t * Type.t), t) CCList.Assoc.t
(** Type of a context. Associate a variable and its type to an expression*)

val varToSyn : (Var.t * Type.t) list -> t list
(** [varToSyn l] maps each pair [(x,t)] in [l] to [Var (x,t)] *)

val from_source: Source.t -> t
(** [from_source] embeds Source.t into Target.t  *)

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

val weakEqual: t -> t ->  bool
(** [weakEqual expr1 expr2] compares recursively [expr1] with [expr2] using
    a weak equality function to compare constant term. *)

val isValue : t -> bool
(** [isValue expr] returns true if [expr] is [Const …] or [Fun _] or [Tuple _]
    and false otherwise. *)

val freeVar : t -> VarSet.t
(** [freeVar expr] returns the set of free variable in [expr]. *)

val listUnusedVar : t -> (Var.t * Type.t) list
(** [listUnusedVar expr] returns the set of bound variable define with a
    [Let] or [NCase] but not used. *)

val subst : Var.t -> Type.t -> t -> t -> t
(** [subst x t expr1 expr2] substitutes the variable [x] of type [t] with
    [expr1] in [expr2]. *)

val simSubst : context -> t -> t
(** [simSubst c expr] substitute the free variable contained in the context [c]
    in [expr]. *)

val canonicalAlphaRename : string -> t -> t
(** [canonicalAplphaRename name expr] *)

val inferType : t -> (Type.t, string) result
(** [inferType expr] tries to type [expr]. Returns [Result.Ok t] if
    [expr] as type [t] and [Reult.Error s] if [expr] cannot be type and [s]
    is the error message. *)

val isWellTyped : t -> bool
(** [isWellTyped expr] returns [true] if [expr] is well typed. *)


val interpret : t -> context -> t
(** [interpret expr c] takes an expression [expr] and a context [c]
    and interprets [expr] under the context [c] as much as possible.
    [expr] does not need to be closed under [c] and does not need to be
    well typed.*)

(** {2 Traverse} *)
module Traverse : functor (S: Strategy.S) -> sig
  val map : (t -> t Rewriter.output) -> t -> t Rewriter.output
end

(** {2 Parser} *)
module Parse : sig
  val pTerm : t CCParse.t

  val of_string : string -> t CCParse.or_error
end

(** {2 Derivatives of basic operators} *)

(** First order derivative of unary operator *)
val dop : Operators.op1 -> t -> t

(** Second order derivative of binary operator 
  [dop22 op  x d1x d2x ddx] returns ∂op(x)*d1x*d2x + ∂∂op(x)*ddx *)
val dop22 : Operators.op1 -> t -> t -> t -> t-> t

(** First partial first order derivative of binary operator *)
val d1op : Operators.op2 -> t -> t -> t

(** Second partial first order derivative of binary operator *)
val d2op : Operators.op2 -> t -> t -> t

(** Second order derivative of binary operator 
    [d2op22 op x d1x d2x ddx y d1y d2y ddy] returns 
    ∂1op(x)*ddx + ∂2op(x)*ddy + ∂1∂1op(x)*d1x*d2x + ∂1∂2op(x)*d1x*d2y + ∂2∂1op(x)*d1y*d2x + ∂2∂2op(x)*d1y*d2y *)
val d2op22 : Operators.op2 -> t -> t -> t -> t-> t -> t-> t -> t -> t

(** [ddop op e] returns ∂^2 op/∂x∂x(e) *)                          
val ddop : Operators.op1 -> t -> t

(** [d1d1op op e1 e2 ] returns ∂^2 op/∂x1∂x1(e1,e2)*)
val d1d1op :Operators.op2 -> t -> t -> t

(** [d1d2op op e1 e2 ] returns ∂^2 op/∂x1∂x2(e1,e2) *)
val d1d2op : Operators.op2 -> t -> t -> t
  
(** [d2d1op op e1 e2 ] returns ∂^2 op/∂x2∂x1(e1,e2) *) 
val d2d1op : Operators.op2 -> t -> t -> t
 
(** [d2d2op op e1 e2 ] returns ∂^2 op/∂x2∂x2(e1,e2) *)
val d2d2op : Operators.op2 -> t -> t -> t
