(* A global counter to produce unique numbers *)
let counter = ref 0

(* A variable is just given by a name and a number *)
type var = string * int

(* we assume programs don't use the variable name y *)
let fresh () : var = 
    let n = !counter in
    let succ = n+1 in
    counter := succ;
    assert (succ <> 0 ); (* check overflow*)
    "y", n

let equal = (==)