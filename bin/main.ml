open Syntax.SourceLanguage
open Syntax.Operators
open Syntax.PrettyPrinter.SourcePrinter

let f = Apply1(Cos, Const 7.);; 

prettyPrinter f;;

Random.self_init();;
Lwt_io.print(string_of_int(Random.int 4));;
Lwt_io.print(string_of_int(Random.int 4));;
Lwt_io.print(string_of_int(Random.int 4));;
Lwt_io.print(string_of_int(Random.int 4));;
