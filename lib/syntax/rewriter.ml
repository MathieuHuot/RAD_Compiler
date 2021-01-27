type nonrec 'a output = Success of 'a | Failure of 'a

type 'a t = 'a -> 'a output

let id x = Success x

let return = id

let bind x f = match x with Success x -> f x | Failure _ -> x

let ( >>= ) = bind

let get = function Success x | Failure x -> x

let get_exn = function
  | Success x -> x
  | Failure _ -> failwith "startegy failed"

let fail x = Failure x

let seq f1 f2 p =
  match f1 p with Success x -> Success (get (f2 x)) | Failure x -> f2 x

let (>>) = seq

let choose f1 f2 p =
  match f1 p with Success x -> Success x | Failure _ -> f2 p

let rec choose_l l p =
  match l with
  | [] -> Failure p
  | h :: t -> (
      match h p with Success x -> Success x | Failure _ -> choose_l t p)

let ( <+ ) = choose
