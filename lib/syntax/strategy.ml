type nonrec 'a output = 'a Rewriter.output = Success of 'a | Failure of 'a

module type S = sig
  (** Signature of a strategy.
   *
   * The strategy define how rewriting rule are apply and in which order. *)

  val return : 'a -> 'a output

  val ( >>= ) : 'a output -> ('a -> 'a output) -> 'a output

  val ( >|= ) : 'a output -> ('a -> 'b) -> 'b output

  val apply2 : ('a -> 'a output) -> 'a -> 'a -> ('a * 'a) output

  val applyl : ('a -> 'a output) -> 'a list -> 'a list output
end

module One : S = struct
  (** Apply rewriting rule only once. *)

  let return x = Failure x

  let ( >>= ) x f = match x with Success _ -> x | Failure x -> f x

  let ( >|= ) x f =
    match x with Success x -> Success (f x) | Failure x -> Failure (f x)

  let apply2 f x1 x2 =
    match f x1 with
    | Success x1 -> Success (x1, x2)
    | Failure x1 -> f x2 >|= fun x2 -> (x1, x2)

  let rec applyl f = function
    | [] -> return []
    | h :: t -> (
        match f h with
        | Success x -> Success (x :: t)
        | Failure _ -> applyl f t >|= fun l -> h :: l)
end

module All : S = struct
  (** Traverse the syntax tree and apply the writing rule whenever it is possible. *)

  let return x = Failure x

  let ( >>= ) x f =
    match x with
    | Success x -> ( match f x with Success x | Failure x -> Success x)
    | Failure x -> f x

  let ( >|= ) x f =
    match x with Success x -> Success (f x) | Failure x -> Failure (f x)

  let apply2 f x1 x2 =
    match f x1 with
    | Success x1 -> (
        match f x2 with Success x2 | Failure x2 -> Success (x1, x2))
    | Failure x1 -> f x2 >|= fun x2 -> (x1, x2)

  let rec applyl f = function
    | [] -> return []
    | h :: t -> (
        match f h with
        | Success x -> applyl f t >>= fun l -> Success (x :: l)
        | Failure _ -> applyl f t >|= fun l -> h :: l)
end

module Repeat : S = struct
  (** Apply the writing rules until it converges. *)

  let return x = Failure x

  let rec repeat success x f =
    match f x with
    | Success x -> repeat true x f
    | Failure x -> if success then Success x else Failure x

  let ( >>= ) x f =
    match x with Success x -> repeat true x f | Failure x -> repeat false x f

  let ( >|= ) x f =
    match x with Success x -> Success (f x) | Failure x -> Failure (f x)

  let apply2 f x1 x2 =
    match repeat false x1 f with
    | Success x1 -> repeat true x2 f >|= fun x2 -> (x1, x2)
    | Failure x1 -> repeat false x2 f >|= fun x2 -> (x1, x2)

  let rec applyl f = function
    | [] -> return []
    | h :: t -> (
        match repeat false h f with
        | Success x -> (
            match applyl f t with Success l | Failure l -> Success (x :: l))
        | Failure _ -> applyl f t >|= fun l -> h :: l)
end
