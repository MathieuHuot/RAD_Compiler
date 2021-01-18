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
  Format.fprintf out "random term:@.%a@.end random term@.@.@." Source.pp
    (Anf.SourceAnf.anf (Generator.sourceSynGen 10 []));

  (* Some terms for tests *)
  let x1 = ("x", 1) in
  let x2 = ("x", 2) in
  let var1 = Target.Var (x1, Target.Type.Real) in
  let var2 = Target.Var (x2, Target.Type.Real) in
  let f1 = Target.Apply1 (Cos, Target.Const 7.) in
  let _f2 =
    Target.Let
      ( x1,
        Target.Type.Real,
        Target.Apply2 (Plus, Target.Const 5., var2),
        Target.Apply1 (Sin, var1) )
  in
  let f3 =
    Target.Apply2
      (Plus, Target.Const 7., Target.Const 8.)
  in
  let f4 = Target.Apply1 (Exp, Target.Const 6.) in
  let f5 = Target.Apply1 (Sin, var1) in
  let f6 = Target.Apply1 (Cos, Target.Const 0.716814692820) in
  let _f7 =
    Target.Apply1
      (Sin, Target.Var (Var.fresh (), Target.Type.Real))
  in

  (* Interpreters tests*)
  let printVal expr context =
    Format.fprintf out "%a@." Target.pp
      (Target.interpret expr context)
  in
  printVal (Target.Const 7.) [];
  printVal f1 [];
  printVal f3 [];
  printVal f4 [];
  printVal f5 [ ((x1, Target.Type.Real), Target.Const 0.) ];
  printVal f5 [ ((x1, Target.Type.Real), Target.Const 2.) ];
  printVal f5 [ ((x1, Target.Type.Real), Target.Const 8.283185307) ];
  printVal f6 ([] : Syntax.Target.context);
  Format.fprintf out "@.@.";

  (* forward mode tests *)
  let f7 =
    Source.Apply1
      ( Operators.Sin,
        Source.Var (Syntax.Var.fresh (), Source.Type.Real) )
  in
  let f8 = ForwardMode.forwardAD f7 in
  let f9 = Rewrite.Optimisations.fullOpti f8 in
  Format.fprintf out
    "Term:@.%a@.Forward derivative of term:@.%a@.Reduced derivative of \
     term:@.%a@.@.@."
    Source.pp f7 Target.pp f8 Target.pp f9;

  let f6 = Syntax.Generator.sourceSynGen 5 [] in
  let f7 = Anf.SourceAnf.anf f6 in
  let f8 = ForwardMode.forwardAD f7 in
  let f9 = Rewrite.Optimisations.fullOpti f8 in
  Format.fprintf out
    "Term:@.%a@.@.Anf Term:@.%a@.@.Forward derivative of term:@.%a@.@.Reduced \
     derivative of term:@.%a@.@.@."
    Source.pp f6 Source.pp f7 Target.pp f8
    Target.pp f9;

  (* reverse mode tests *)
  let x11 = ("x", 1) in
  let var11 = Source.Var (x11, Real) in
  let f11 = Source.Apply1 (Exp, var11) in
  let cst1 = [ Target.Const 0.; Target.Const 1. ] in
  let f12 =
    Transforms.ReverseMode.semiNaiveReverseAD [ (x11, Source.Type.Real) ] f11
  in
  let f13 =
    match f12 with
    | Target.Tuple [ _; x ] -> Target.App (x, cst1)
    | _ -> failwith "f12 wrong format"
  in
  let f14 = Rewrite.Optimisations.fullOpti f13 in

  Format.fprintf out
    "variable:@.%a@.term:@.%a@.reverse derivative macro of \
     term:@.%a@.derivative of term:@.%a@.fully reduced term:@.%a@.@.@."
    Source.pp var11 Source.pp f11 Target.pp f12
    Target.pp f13 Target.pp f14;

  let x12 = ("x", 2) in
  let var12 = Source.Var (x12, Source.Type.Real) in
  let f21 = Source.Apply2 (Operators.Plus, var11, var12) in
  let f22 = Anf.SourceAnf.anf f21 in
  let f23 =
    Transforms.ReverseMode.semiNaiveReverseAD
      [ (x11, Source.Type.Real); (x12, Source.Type.Real) ]
      f21
  in
  let cst2 =
    [
      Target.Const 0.; Target.Const 0.; Target.Const 1.;
    ]
  in
  let f24 =
    match f23 with
    | Target.Tuple [ _; x ] -> Target.App (x, cst2)
    | _ -> failwith "f12 wrong format"
  in
  let f25 = Rewrite.Optimisations.fullOpti f24 in

  Format.fprintf out
    "term:@.%a@.anf term:@.%a@.reverse derivative macro of \
     term:@.%a@.derivative of term:@.%a@.fully reduced term:@.%a@.@.@."
    Source.pp f21 Source.pp f22 Target.pp f23
    Target.pp f24 Target.pp f25;

  let g6 = Syntax.Generator.sourceSynGen 10 [] in
  let g7 = Anf.SourceAnf.anf g6 in
  let g8 = Transforms.ReverseMode.grad [] g7 in
  let g9 = Rewrite.Optimisations.fullOpti g8 in
  Format.fprintf out
    "Term:@.%a@.@.Anf Term:@.%a@.@.Reverse derivative macro of \
     term:@.%a@.@.Reduced reverse derivative macro of term:@.%a@.@.@."
    Source.pp g6 Source.pp g7 Target.pp g8
    Target.pp g9;
    
  let g10 = Transforms.ReverseMode.grad2 [] g7 in
  Format.fprintf out "Optimized grad of term:@.%a@.@.@."
  Target.pp g10;

  let g6 =
    Source.Apply1
      ( Operators.Minus,
        Source.Apply1 (Operators.Cos, Source.Const 3.) )
  in
  let g7 = Anf.SourceAnf.anf g6 in
  let g8 =
    Transforms.ReverseMode.semiNaiveReverseAD [ (x12, Source.Type.Real) ] g7
  in
  let g9 = Rewrite.Optimisations.fullOpti g8 in
  Format.fprintf out
    "Term:@.%a@.@.Anf Term:@.%a@.@.Reverse derivative macro of \
     term:@.%a@.@.Reduced reverse derivative macro of term:@.%a@.@.@."
    Source.pp g6 Source.pp g7 Target.pp g8
    Target.pp g9;

  
  let g6 =
      Source.Let
        ( ("z", 1),
          Source.Type.Real,
          Source.Apply2
            ( Times,
              Source.Var (x2, Source.Type.Real),
              Source.Apply2
                ( Plus,
                  Source.Var (x1, Source.Type.Real),
                  Source.Var (x2, Source.Type.Real) ) ),
          Source.Var (("z", 1), Source.Type.Real) )
  in
  let g7 = Anf.SourceAnf.weakAnf g6 in
  let g8 = Transforms.ReverseMode.grad [ (x1, Real); (x2, Real) ] g7 in  
  let g9 = Rewrite.Optimisations.fullOpti g8 in
  Format.fprintf out
    "Term:@.%a@.@.Anf Term:@.%a@.@.Reverse derivative macro of \
     term:@.%a@.@.Reduced reverse derivative macro of term:@.%a@.@.@."
    Source.pp g6 Source.pp g7 Target.pp g8
    Target.pp g9;

  let g6 =
    Source.Let
      ( ("z", 1),
        Source.Type.Real,
        Source.Var (x1, Source.Type.Real),
        Source.Var (("z", 1), Source.Type.Real) )
  in
  let g7 = Anf.SourceAnf.weakAnf g6 in
  let g8 = Transforms.ReverseMode.grad [ (x1, Real) ] g7 in
  let g9 = Rewrite.Optimisations.fullOpti g8 in
  Format.fprintf out
    "Term:@.%a@.@.Weak anf Term:@.%a@.@.Reverse derivative macro of \
     term:@.%a@.@.Reduced reverse derivative macro of term:@.%a@.@.@."
    Source.pp g6 Source.pp g7 Target.pp g8
    Target.pp g9;

  let g6 =
    Source.Apply2
      ( Operators.Times,
        Source.Apply2
          ( Operators.Plus,
            Source.Var (x1, Source.Type.Real),
            Source.Var (x2, Source.Type.Real) ),
        Source.Apply2
          ( Operators.Plus,
            Source.Var (x1, Source.Type.Real),
            Source.Var (x2, Source.Type.Real) ) )
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
    Source.pp g6 Source.pp g7 Target.pp g8
    Target.pp g9 Target.pp g10 Target.pp g11
    Target.pp g12 Target.pp g13 Target.pp g14
    Target.pp g15 Target.pp g16 Target.pp g17
    Target.pp g18 Target.pp g19  Target.pp g20 
    Target.pp g21;

  let g6 =
    Source.Let
      ( ("z", 1),
        Source.Type.Real,
        Source.Let
          ( ("z", 2),
            Source.Type.Real,
            Source.Var (x1, Source.Type.Real),
            Source.Var (("z", 2), Source.Type.Real) ),
        Source.Var (("z", 1), Source.Type.Real) )
  in
  let g7 = Anf.SourceAnf.weakAnf g6 in
  let g8 = Transforms.ReverseMode.grad [ (x1, Real) ] g7 in
  let g9 = Rewrite.Optimisations.fullOpti g8 in
  Format.fprintf out
    "Term:@.%a@.@.Weak anf Term:@.%a@.@.Reverse derivative macro of \
     term:@.%a@.@.Reduced reverse derivative macro of term:@.%a@.@.@."
    Source.pp g6 Source.pp g7 Target.pp g8
    Target.pp g9;

  let var = ("x", 1) in
  let var2 = ("z", 1) in
  let f7 =
    Source.Apply1 (Sin, Source.Var (var, Source.Type.Real))
  in
  let f8 = Transforms.JetAD.Jets12.forward12AD f7 in
  let f9 =
    Target.Tuple
      (Transforms.JetAD.Jets12.secondPartial
         [
           ( var,
             Target.Type.Real,
             Target.Var (var2, Target.Type.Real) );
         ]
         f7)
  in
  let f10 = Rewrite.Optimisations.fullOpti f9 in
  Format.fprintf out
    "Term:@.%a@.Forward derivative of term:@.%a@.Gradient of \
     term:@.%a@.Reduced derivative of term:@.%a@.@.@."
    Source.pp f7 Target.pp f8 Target.pp f9
    Target.pp f10;

  let g6 =
    Source.Apply2
      ( Times,
        Source.Apply2
          ( Plus,
            Source.Var (x1, Source.Type.Real),
            Source.Var (x2, Source.Type.Real) ),
        Source.Apply2
          ( Plus,
            Source.Var (x1, Source.Type.Real),
            Source.Var (x2, Source.Type.Real) ) )
  in
  let g7 =
    Transforms.JetAD.Jets12.hessian
      [
        (x1, Target.Type.Real, Target.Var (x1, Target.Type.Real));
        (x2, Target.Type.Real, Target.Var (x2, Target.Type.Real));
      ]
      g6
  in
  Format.fprintf out "Term:@.%a@.@.Reduced hession of term:@.%a@.@.@."
    Source.pp g6 Target.pp
    g7.(0).(0);
  Unix.close file
