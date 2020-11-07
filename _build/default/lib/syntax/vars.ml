
(* A global counter to produce unique numbers *)
let counter = ref 0

(* A variable has a unique identifier *)
type var = int

let fresh () : var = 
    let n = !counter in
    let succ = n+1 in
    counter := succ;
    assert (succ <> 0 );
    n

let equal = (==)