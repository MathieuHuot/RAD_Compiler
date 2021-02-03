(* A variable is just given by a name, a number *)
type t = string * int

(* we assume programs don't use the variable name y *)
let fresh : unit -> t =
    (* A counter to produce unique numbers *)
    let counter = ref 0 in
    fun () ->
    let n = !counter in
    let succ = n+1 in
    counter := succ;
    assert (succ <> 0 ); (* check overflow*)
    "y", n

let equal var1 var2 = String.equal (fst var1) (fst var2) && snd var1 = snd var2

let to_string (name, id) = name ^ (string_of_int id)

let pp fmt (name, id) = Format.fprintf fmt "%s%i" name id

(** Takes a primal var as input and returns a pair of the primal variable and a new tangent variable.
    Assumes that no variable from the initial term starts with d, in other words that the newly returned variable is fresh *)
let dvar var : t * t = let str, i = var in var, ("d"^str, i) 

(** Similarly as above but returns a triple *)
let dvar2 var : t * t * t = let str,i = var in var,("d"^str,i),("d2"^str,i) 

(** Similarly as above but returns a quadruple *)
let dvar22 var : t * t * t * t = let str, i = var in var, ("d1"^str, i), ("d2"^str, i), ("dd"^str, i) 

(** Similarly as above but returns an 8-tuple *)
let dvar33 var : t * t * t * t * t * t * t * t = 
  let str, i = var in var, 
                      ("d1"^str, i), ("d2"^str, i), ("d3"^str, i), 
                      ("dd1"^str, i),  ("dd2"^str, i),  ("dd3"^str, i),  
                      ("ddd"^str, i)

module Parse = struct
  open CCParse

  let pVar = U.pair ~start:"" ~stop:"" ~sep:"" (chars_if is_alpha) U.int

  let of_string = parse_string pVar
end
