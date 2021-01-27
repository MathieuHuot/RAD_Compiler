(**
    Module defining useful type and function to write rewriter
*)

(** Type of value return by a rewriter. If the rewriter did something it returns
    [Success] if not it returns [Failure]
*)
type nonrec 'a output = Success of 'a | Failure of 'a

type 'a t = 'a -> 'a output
(** Type of a rewriter, take some ['a] and maybe rewrite it into something *)

let id x = Success x
(** Identity rewriter, do nothing and always return [Success] *)

let fail x = Failure x
(** Do nothing and always return [Failure] *)

let bind x f = match x with Success x -> f x | Failure _ -> x
(** Bind a function in case of Success *)

let ( >>= ) = bind
(** Infix version of {!bind} *)

let get = function Success x | Failure x -> x
(** Extract the value from the {!output} type *)

let get_exn = function
  | Success x -> x
  | Failure _ -> failwith "startegy failed"
(** Similar to {!get} but fail if the result is a [Failure] *)

let seq f1 f2 p =
  match f1 p with Success x -> Success (get (f2 x)) | Failure x -> f2 x
(** [seq f1 f2] combine two rewriter [f1] and [f2] by applying both and return [Success]
    if one of them return [Success] *)

let (>>) = seq
(** Infix version of {!seq} *)

let choose f1 f2 p =
  match f1 p with Success x -> Success x | Failure _ -> f2 p
(** [seq f1 f2] combine two rewriter [f1] and [f2]. Apply [f1] first and [f2] if [f1] fails *)

let rec choose_l l p =
  match l with
  | [] -> Failure p
  | h :: t -> (
      match h p with Success x -> Success x | Failure _ -> choose_l t p)
(** List version of {!choose} *)

let ( <+ ) = choose
(** Infix version of {!choose} *)
