open Syntax.SourceLanguage
open Syntax.Operators

let x = Var(3);;

let f op = match op with 
| Cos -> (Lwt_io.printf "Hello\n")
| Sin -> (Lwt_io.printf "World\n");;

f(Cos);;
f(Sin);; 

let g () = match x with 
| Var(a) -> (Lwt_io.printf "%d" a) 
| _ -> (Lwt_io.printf "42");;

g();;