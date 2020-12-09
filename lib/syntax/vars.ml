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
