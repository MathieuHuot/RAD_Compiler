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

  (* applies the second strategy only if the first one failed *)
  let lChoice : 'a strategy -> 'a strategy -> 'a strategy =
    fun fs -> fun ss -> fun p -> match fs p with 
    | Success(p2) -> Success(p2)
    | Failure _   -> ss p
  (* convenient infix notation for lChoice*) 
  let (<+) fs ss = lChoice fs ss

  (* tries to apply the first strategy and applies the identity if fails *)  
  let tryStrat : 'a strategy -> 'a strategy =
    fun s -> fun p -> p |>  (s <+ id)

  (* applies a strategy until it is no longer applicable *)  
  let rec repeat : 'a strategy -> 'a strategy = 
    fun s -> fun p -> p |> tryStrat (seq s (repeat s))
end 

module type EvalStrat = sig
  open Strategy
  val all: 'a strategy -> 'a strategy
  val one: 'a strategy -> 'a strategy
  val some: 'a strategy -> 'a strategy
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
      fun p -> p |> seq (s |> tryAll |> EvStrat.all) (tryStrat s)

    let normalize (s : 'a strategy) : 'a strategy =
      fun p -> p |> repeat (topDown s)
    end