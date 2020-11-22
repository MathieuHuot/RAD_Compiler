open Syntax.SourceLanguage
open Syntax.Operators
open Syntax.PrettyPrinter.SourcePrinter

let f = Apply1(Cos, Const 7.);; 

prettyPrinter f;;