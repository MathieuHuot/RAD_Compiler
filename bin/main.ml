open Syntax
open Transforms

let _ =
  let _x = 2 in
  Format.printf "random term:@.";
  Format.printf "%a@." SourceLanguage.pp
    (Anf.SourceAnf.anf (Generator.sourceSynGen 10 []));
  Format.printf "end random term:@.@.@.";

  (* Some terms for tests *)
  let x1 = ("x", 1) in
  let x2 = ("x", 2) in
  let var1 = TargetLanguage.Var (x1, TargetLanguage.Real) in
  let var2 = TargetLanguage.Var (x2, TargetLanguage.Real) in
  let f1 = TargetLanguage.Apply1 (Cos, TargetLanguage.Const 7.) in
  let _f2 =
    TargetLanguage.Let
      ( x1,
        TargetLanguage.Real,
        TargetLanguage.Apply2 (Plus, TargetLanguage.Const 5., var2),
        TargetLanguage.Apply1 (Sin, var1) )
  in
  let f3 =
    TargetLanguage.Apply2
      (Plus, TargetLanguage.Const 7., TargetLanguage.Const 8.)
  in
  let f4 = TargetLanguage.Apply1 (Exp, TargetLanguage.Const 6.) in
  let f5 = TargetLanguage.Apply1 (Sin, var1) in
  let f6 = TargetLanguage.Apply1 (Cos, TargetLanguage.Const 0.716814692820) in
  let _f7 =
    TargetLanguage.Apply1
      (Sin, TargetLanguage.Var (Vars.fresh (), TargetLanguage.Real))
  in

  (* Interpreters tests*)
  let printVal expr context =
    Format.printf "%a@." TargetLanguage.pp
      (TargetLanguage.interpret expr context)
  in
  printVal (TargetLanguage.Const 7.) [];
  printVal f1 [];
  printVal f3 [];
  printVal f4 [];
  printVal f5 [ (x1, TargetLanguage.Real, TargetLanguage.Const 0.) ];
  printVal f5 [ (x1, TargetLanguage.Real, TargetLanguage.Const 2.) ];
  printVal f5 [ (x1, TargetLanguage.Real, TargetLanguage.Const 8.283185307) ];
  printVal f6 ([] : Syntax.TargetLanguage.context);
  Format.printf "@.@.";

  (* forward mode tests *)
  let f7 =
    SourceLanguage.Apply1
      ( Operators.Sin,
        SourceLanguage.Var (Syntax.Vars.fresh (), SourceLanguage.Real) )
  in
  let f8 = ForwardMode.forwardAD f7 in
  let f9 = Rewrite.Optimisations.fullOpti f8 in
  Format.printf
    "Term:@.%a@.Forward derivative of term:@.%a@.Reduced derivative of \
     term:@.%a@.@.@."
    SourceLanguage.pp f7 TargetLanguage.pp f8 TargetLanguage.pp f9;

  let f6 = Syntax.Generator.sourceSynGen 5 [] in
  let f7 = Anf.SourceAnf.anf f6 in
  let f8 = ForwardMode.forwardAD f7 in
  let f9 = Rewrite.Optimisations.fullOpti f8 in
  Format.printf
    "Term:@.%a@.@.Anf Term:@.%a@.@.Forward derivative of term:@.%a@.@.Reduced \
     derivative of term:@.%a@.@.@."
    SourceLanguage.pp f6 SourceLanguage.pp f7 TargetLanguage.pp f8
    TargetLanguage.pp f9
