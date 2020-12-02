(* Module for optimisations strategies. Allows to create and combine strategies. *)

(* Restricted form of monads where 'a='b *)
module type MONAD = sig
  type 'a mon
  val ret: 'a -> 'a mon
  val bind: 'a mon -> ('a -> 'a mon) -> 'a mon
  type 'a result
  val run: 'a mon -> 'a result
end

module Strategy = struct
  type 'a rewriteResult = Success of 'a | Failure of 'a strategy
  and 'a strategy = 'a -> 'a rewriteResult
  type 'a mon = 'a rewriteResult

  let id : 'a strategy = (fun p -> Success(p))
  let ret = id
  let bind = fun (s :'a mon) -> fun (f : 'a -> 'a mon) -> match s with 
    | Success(p) -> f(p)
    | Failure(st) -> Failure(st)
  
  type 'a result = 'a
  (* Runs a strategy and returns the result if successes *)
  let run (m: 'a mon) : 'a result = match m with 
    | Success(expr) -> expr
    | Failure(_)    -> failwith "run: strategy failed"

  (* strategy that always fails *)
  let rec fail : 'a strategy = fun _ -> Failure(fail)

  (* Composes sequentially two strategies *)
  let seq : 'a strategy -> 'a strategy -> 'a strategy = 
    fun fs -> fun ss -> fun p -> bind (fs p) ss

  (* convenient infix notation for seq *) 
  let (>>) fs ss = seq fs ss  

  (* applies the second strategy only if the first one failed *)
  let lChoice : 'a strategy -> 'a strategy -> 'a strategy =
    fun fs -> fun ss -> fun p -> match fs p with 
    | Success(p2) -> Success(p2)
    | Failure _   -> ss p

  (* convenient infix notation for lChoice *) 
  let (<+) fs ss = lChoice fs ss

  (* tries to apply the first strategy and applies the identity if fails *)  
  let tryStrat : 'a strategy -> 'a strategy =
    fun s -> fun p -> p |>  (s <+ id)

  (* applies a strategy until it is no longer applicable *)  
  let rec repeat : 'a strategy -> 'a strategy = 
    fun s -> fun p -> p |> tryStrat(s >> (repeat s))

  (* applies a strategy n times *)    
  let rec iterate : int -> 'a strategy -> 'a strategy = 
    fun n -> fun s -> match n with | 0 -> id | n -> s >> iterate (n-1) s 

  (* tries to apply as many strategies as possible in order from a list *) 
  let rec tryStratList : 'a strategy list -> 'a strategy =
  fun sList -> match sList with 
  | []    -> id
  | s::tl -> tryStrat s >> tryStratList tl  
end 

module type EvalStrat = sig
  open Strategy
  type adt
  val all: adt strategy -> adt strategy
  val one: adt strategy -> adt strategy
  val some: adt strategy -> adt strategy
end

module CompleteTraversalStrat =
  functor (EvStrat: EvalStrat ) ->
    struct
    open Strategy
    let rec topDown (s : 'a strategy) : 'a strategy = 
      fun p -> p |>  (s <+ (s |> topDown |> EvStrat.one))

    let rec bottomUp (s : 'a strategy) : 'a strategy = 
      fun p -> p |> ((s |> bottomUp |> EvStrat.one) <+ s)

    let rec allTopDown (s : 'a strategy) : 'a strategy = 
      fun p -> p |> seq s (s |> allTopDown |> EvStrat.all)

    let rec allBottomUp (s : 'a strategy) : 'a strategy = 
      fun p -> p |> seq (s |> allBottomUp |> EvStrat.all) s

    let rec tryAll (s : 'a strategy) : 'a strategy = 
      fun p -> p |> seq (s |> tryStrat |> tryAll |> EvStrat.all) (tryStrat s)

    let normalize (s : 'a strategy) : 'a strategy =
      fun p -> p |> repeat (topDown s)
    end