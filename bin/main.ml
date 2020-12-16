open Syntax
open Transforms

let _ =
  CCIO.File.(remove_noerr (make "out.txt"));
  let file = Unix.openfile "out.txt" [Unix.O_WRONLY; Unix.O_CREAT] 0o644 in  
  let oc = Unix.out_channel_of_descr file in
  set_binary_mode_out oc false;
  let out = Format.formatter_of_out_channel oc in
  Random.self_init ();
  let _x = 2 in
  Format.fprintf out "random term:@.%a@.end random term@.@.@." SourceLanguage.pp
    (Anf.SourceAnf.anf (Generator.sourceSynGen 10 []));

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
    Format.fprintf out "%a@." TargetLanguage.pp
      (TargetLanguage.interpret expr context)
  in
  printVal (TargetLanguage.Const 7.) [];
  printVal f1 [];
  printVal f3 [];
  printVal f4 [];
  printVal f5 [ ((x1, TargetLanguage.Real), TargetLanguage.Const 0.) ];
  printVal f5 [ ((x1, TargetLanguage.Real), TargetLanguage.Const 2.) ];
  printVal f5 [ ((x1, TargetLanguage.Real), TargetLanguage.Const 8.283185307) ];
  printVal f6 ([] : Syntax.TargetLanguage.context);
  Format.fprintf out "@.@.";

  (* forward mode tests *)
  let f7 =
    SourceLanguage.Apply1
      ( Operators.Sin,
        SourceLanguage.Var (Syntax.Vars.fresh (), SourceLanguage.Real) )
  in
  let f8 = ForwardMode.forwardAD f7 in
  let f9 = Rewrite.Optimisations.fullOpti f8 in
  Format.fprintf out
    "Term:@.%a@.Forward derivative of term:@.%a@.Reduced derivative of \
     term:@.%a@.@.@."
    SourceLanguage.pp f7 TargetLanguage.pp f8 TargetLanguage.pp f9;

  let f6 = Syntax.Generator.sourceSynGen 5 [] in
  let f7 = Anf.SourceAnf.anf f6 in
  let f8 = ForwardMode.forwardAD f7 in
  let f9 = Rewrite.Optimisations.fullOpti f8 in
  Format.fprintf out
    "Term:@.%a@.@.Anf Term:@.%a@.@.Forward derivative of term:@.%a@.@.Reduced \
     derivative of term:@.%a@.@.@."
    SourceLanguage.pp f6 SourceLanguage.pp f7 TargetLanguage.pp f8
    TargetLanguage.pp f9;

  (* reverse mode tests *)
  let x11 = ("x", 1) in
  let var11 = SourceLanguage.Var (x11, Real) in
  let f11 = SourceLanguage.Apply1 (Exp, var11) in
  let cst1 = [ TargetLanguage.Const 0.; TargetLanguage.Const 1. ] in
  let f12 =
    Transforms.ReverseMode.semiNaiveReverseAD [ (x11, SourceLanguage.Real) ] f11
  in
  let f13 =
    match f12 with
    | TargetLanguage.Tuple [ _; x ] -> TargetLanguage.App (x, cst1)
    | _ -> failwith "f12 wrong format"
  in
  let f14 = Rewrite.Optimisations.fullOpti f13 in

  Format.fprintf out
    "variable:@.%a@.term:@.%a@.reverse derivative macro of \
     term:@.%a@.derivative of term:@.%a@.fully reduced term:@.%a@.@.@."
    SourceLanguage.pp var11 SourceLanguage.pp f11 TargetLanguage.pp f12
    TargetLanguage.pp f13 TargetLanguage.pp f14;

  let x12 = ("x", 2) in
  let var12 = SourceLanguage.Var (x12, SourceLanguage.Real) in
  let f21 = SourceLanguage.Apply2 (Operators.Plus, var11, var12) in
  let f22 = Anf.SourceAnf.anf f21 in
  let f23 =
    Transforms.ReverseMode.semiNaiveReverseAD
      [ (x11, SourceLanguage.Real); (x12, SourceLanguage.Real) ]
      f21
  in
  let cst2 =
    [
      TargetLanguage.Const 0.; TargetLanguage.Const 0.; TargetLanguage.Const 1.;
    ]
  in
  let f24 =
    match f23 with
    | TargetLanguage.Tuple [ _; x ] -> TargetLanguage.App (x, cst2)
    | _ -> failwith "f12 wrong format"
  in
  let f25 = Rewrite.Optimisations.fullOpti f24 in

  Format.fprintf out
    "term:@.%a@.anf term:@.%a@.reverse derivative macro of \
     term:@.%a@.derivative of term:@.%a@.fully reduced term:@.%a@.@.@."
    SourceLanguage.pp f21 SourceLanguage.pp f22 TargetLanguage.pp f23
    TargetLanguage.pp f24 TargetLanguage.pp f25;

  let g6 = Syntax.Generator.sourceSynGen 10 [] in
  let g7 = Anf.SourceAnf.anf g6 in
  let g8 = Transforms.ReverseMode.grad [] g7 in
  let g9 = Rewrite.Optimisations.fullOpti g8 in
  Format.fprintf out
    "Term:@.%a@.@.Anf Term:@.%a@.@.Reverse derivative macro of \
     term:@.%a@.@.Reduced reverse derivative macro of term:@.%a@.@.@."
    SourceLanguage.pp g6 SourceLanguage.pp g7 TargetLanguage.pp g8
    TargetLanguage.pp g9;

  let g6 =
    SourceLanguage.Apply1
      ( Operators.Minus,
        SourceLanguage.Apply1 (Operators.Cos, SourceLanguage.Const 3.) )
  in
  let g7 = Anf.SourceAnf.anf g6 in
  let g8 =
    Transforms.ReverseMode.semiNaiveReverseAD [ (x12, SourceLanguage.Real) ] g7
  in
  let g9 = Rewrite.Optimisations.fullOpti g8 in
  Format.fprintf out
    "Term:@.%a@.@.Anf Term:@.%a@.@.Reverse derivative macro of \
     term:@.%a@.@.Reduced reverse derivative macro of term:@.%a@.@.@."
    SourceLanguage.pp g6 SourceLanguage.pp g7 TargetLanguage.pp g8
    TargetLanguage.pp g9;

  
  let g6 =
      SourceLanguage.Let
        ( ("z", 1),
          SourceLanguage.Real,
          SourceLanguage.Apply2
            ( Times,
              SourceLanguage.Var (x2, SourceLanguage.Real),
              SourceLanguage.Apply2
                ( Plus,
                  SourceLanguage.Var (x1, SourceLanguage.Real),
                  SourceLanguage.Var (x2, SourceLanguage.Real) ) ),
          SourceLanguage.Var (("z", 1), SourceLanguage.Real) )
  in
  let g7 = Anf.SourceAnf.weakAnf g6 in
  let g8 = Transforms.ReverseMode.grad [ (x1, Real); (x2, Real) ] g7 in  
  let g9 = Rewrite.Optimisations.fullOpti g8 in
  Format.fprintf out
    "Term:@.%a@.@.Anf Term:@.%a@.@.Reverse derivative macro of \
     term:@.%a@.@.Reduced reverse derivative macro of term:@.%a@.@.@."
    SourceLanguage.pp g6 SourceLanguage.pp g7 TargetLanguage.pp g8
    TargetLanguage.pp g9;

  let g6 =
    SourceLanguage.Let
      ( ("z", 1),
        SourceLanguage.Real,
        SourceLanguage.Var (x1, SourceLanguage.Real),
        SourceLanguage.Var (("z", 1), SourceLanguage.Real) )
  in
  let g7 = Anf.SourceAnf.weakAnf g6 in
  let g8 = Transforms.ReverseMode.grad [ (x1, Real) ] g7 in
  let g9 = Rewrite.Optimisations.fullOpti g8 in
  Format.fprintf out
    "Term:@.%a@.@.Weak anf Term:@.%a@.@.Reverse derivative macro of \
     term:@.%a@.@.Reduced reverse derivative macro of term:@.%a@.@.@."
    SourceLanguage.pp g6 SourceLanguage.pp g7 TargetLanguage.pp g8
    TargetLanguage.pp g9;

  let g6 =
    SourceLanguage.Apply2
      ( Operators.Times,
        SourceLanguage.Apply2
          ( Operators.Plus,
            SourceLanguage.Var (x1, SourceLanguage.Real),
            SourceLanguage.Var (x2, SourceLanguage.Real) ),
        SourceLanguage.Apply2
          ( Operators.Plus,
            SourceLanguage.Var (x1, SourceLanguage.Real),
            SourceLanguage.Var (x2, SourceLanguage.Real) ) )
  in
  let g7 = Anf.SourceAnf.anf g6 in
  let g8 = Transforms.ReverseMode.grad [ (x1, Real); (x2, Real) ] g7 in
  let g9 = Rewrite.Optimisations.fullOpti g8 in
  let g10 = Rewrite.Optimisations.lambdaRem g8 in
  let g11 = Rewrite.Optimisations.forwSubst g10 in
  let g12 = Rewrite.Optimisations.oneCaseRem g11 in
  let g13 =  Rewrite.Optimisations.letComm g12 in
  let g14 = Rewrite.Optimisations.forwSubst g13 in
  let g15 = Rewrite.Optimisations.lambdaRem g14 in
  let g16 = Rewrite.Optimisations.simpleAlgSimpl g15 in
  let g17 = Rewrite.Optimisations.forwSubst g16 in
  let g18 = Rewrite.Optimisations.zeroSimpl g17 in
  let g19 = Rewrite.Optimisations.simpleAlgSimpl g18 in
  let g20 = Rewrite.Optimisations.forwSubst g19 in
  let g21 =  Rewrite.Optimisations.deadVarElim g20 in
  Format.fprintf out
    "Term:@.%a@.
      Weak anf Term:@.%a@.
      Reverse derivative macro of term:@.%a@.
      Reduced reverse derivative macro of term:@.%a@.@.
      LambdaRemoval of term:@.%a@.
      ForwardSubstitution of term:@.%a@.
      OneCaseRemoval of term:@.%a@.
      LetCommutativity of term:@.%a@.
      ForwardSubstitution of term:@.%a@.
      LambdaRemoval of term:@.%a@.
      SimpleAlgebraicSimpl of term:@.%a@.
      ForwardSubstitution of term:@.%a@.
      ZeroSimpl of term:@.%a@.
      SimpleAlgebraicSimpl of term:@.%a@.
      ForwardSubstitution of term:@.%a@.
      DeadVarElim of term:@.%a@.@.@."
    SourceLanguage.pp g6 SourceLanguage.pp g7 TargetLanguage.pp g8
    TargetLanguage.pp g9 TargetLanguage.pp g10 TargetLanguage.pp g11
    TargetLanguage.pp g12 TargetLanguage.pp g13 TargetLanguage.pp g14
    TargetLanguage.pp g15 TargetLanguage.pp g16 TargetLanguage.pp g17
    TargetLanguage.pp g18 TargetLanguage.pp g19  TargetLanguage.pp g20 
    TargetLanguage.pp g21;

  let g6 =
    SourceLanguage.Let
      ( ("z", 1),
        SourceLanguage.Real,
        SourceLanguage.Let
          ( ("z", 2),
            SourceLanguage.Real,
            SourceLanguage.Var (x1, SourceLanguage.Real),
            SourceLanguage.Var (("z", 2), SourceLanguage.Real) ),
        SourceLanguage.Var (("z", 1), SourceLanguage.Real) )
  in
  let g7 = Anf.SourceAnf.weakAnf g6 in
  let g8 = Transforms.ReverseMode.grad [ (x1, Real) ] g7 in
  let g9 = Rewrite.Optimisations.fullOpti g8 in
  Format.fprintf out
    "Term:@.%a@.@.Weak anf Term:@.%a@.@.Reverse derivative macro of \
     term:@.%a@.@.Reduced reverse derivative macro of term:@.%a@.@.@."
    SourceLanguage.pp g6 SourceLanguage.pp g7 TargetLanguage.pp g8
    TargetLanguage.pp g9;

  let var = ("x", 1) in
  let var2 = ("z", 1) in
  let f7 =
    SourceLanguage.Apply1 (Sin, SourceLanguage.Var (var, SourceLanguage.Real))
  in
  let f8 = Transforms.JetAD.Jets12.forward12AD f7 in
  let f9 =
    TargetLanguage.Tuple
      (Transforms.JetAD.Jets12.secondPartial
         [
           ( var,
             TargetLanguage.Real,
             TargetLanguage.Var (var2, TargetLanguage.Real) );
         ]
         f7)
  in
  let f10 = Rewrite.Optimisations.fullOpti f9 in
  Format.fprintf out
    "Term:@.%a@.Forward derivative of term:@.%a@.Gradient of \
     term:@.%a@.Reduced derivative of term:@.%a@.@.@."
    SourceLanguage.pp f7 TargetLanguage.pp f8 TargetLanguage.pp f9
    TargetLanguage.pp f10;

  let g6 =
    SourceLanguage.Apply2
      ( Times,
        SourceLanguage.Apply2
          ( Plus,
            SourceLanguage.Var (x1, SourceLanguage.Real),
            SourceLanguage.Var (x2, SourceLanguage.Real) ),
        SourceLanguage.Apply2
          ( Plus,
            SourceLanguage.Var (x1, SourceLanguage.Real),
            SourceLanguage.Var (x2, SourceLanguage.Real) ) )
  in
  let g7 =
    Transforms.JetAD.Jets12.hessian
      [
        (x1, TargetLanguage.Real, TargetLanguage.Var (x1, TargetLanguage.Real));
        (x2, TargetLanguage.Real, TargetLanguage.Var (x2, TargetLanguage.Real));
      ]
      g6
  in
  Format.fprintf out "Term:@.%a@.@.Reduced hession of term:@.%a@.@.@."
    SourceLanguage.pp g6 TargetLanguage.pp
    g7.(0).(0);
  Unix.close file
