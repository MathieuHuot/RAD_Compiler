open Containers
open Syntax

module T = struct
  open Target

  (* Term gen *)
  let arbitrary_closed_term =
    QCheck.make
      QCheck.Gen.(int_bound 20 >>= fun i -> TargetGen.gen [] i Type.Real)
      ~print:to_string ~shrink:TargetGen.shrink

  let arbitrary_term freeVar =
    QCheck.make
      QCheck.Gen.(int_bound 20 >>= fun i -> TargetGen.gen freeVar i Type.Real)
      ~print:to_string ~shrink:TargetGen.shrink

  (* Basic test *)
  let test_isWellTyped =
    QCheck.Test.make ~count:100 ~name:"isWellTyped" arbitrary_closed_term
      (fun term ->
        match inferType term with
        | Result.Ok _ -> true
        | Result.Error s -> failwith s)

  let test_equal =
    QCheck.Test.make ~count:100 ~name:"equal" arbitrary_closed_term (fun expr ->
        equal expr expr)

  let test_parse =
    QCheck.Test.make ~count:100 ~name:"parse" arbitrary_closed_term (fun expr ->
        match Parse.of_string (to_string expr) with
        | Result.Ok e -> equal expr e
        | Result.Error _ -> false)

  let test_interpret =
    QCheck.Test.make ~count:100 ~name:"interp" arbitrary_closed_term
      (fun expr -> match interpret expr [] with Const _ -> true | _ -> false)

  let test_anf =
    QCheck.Test.make ~count:100 ~name:"anf" arbitrary_closed_term (fun expr ->
        equal
          (interpret (Transforms.Anf.TargetAnf.anf expr) [])
          (interpret expr []))

  let test_weakAnf =
    QCheck.Test.make ~count:100 ~name:"weakAnf" arbitrary_closed_term
      (fun expr ->
        equal
          (interpret (Transforms.Anf.TargetAnf.weakAnf expr) [])
          (interpret expr []))

  let test_isInAnf_anf =
    QCheck.Test.make ~count:100 ~name:"isInAnf.anf" arbitrary_closed_term
      (fun expr -> Transforms.Anf.TargetAnf.(isInAnf (anf expr)))

  let test_isInWeakAnf_weakAnf =
    QCheck.Test.make ~count:100 ~name:"isInWeakAnf.weakAnf"
      arbitrary_closed_term (fun expr ->
        Transforms.Anf.TargetAnf.(isInWeakAnf (weakAnf expr)))

  let test_list =
    [
      test_isWellTyped;
      test_equal;
      test_parse;
      test_interpret;
      test_anf;
      test_weakAnf;
      test_isInWeakAnf_weakAnf;
    ]

  (* Test optimization *)
  let test_opti opti opti_name =
    QCheck.Test.make ~count:100 ~max_gen:500 ~name:("Opt " ^ opti_name)
      arbitrary_closed_term (fun expr ->
        let module AT = Target.Traverse (Strategy.All) in
        let e1 =
          interpret
            (match AT.map opti expr with
            | Rewriter.Success expr -> expr
            | Rewriter.Failure _ -> QCheck.assume_fail ())
            []
        in
        let e2 = interpret expr [] in
        if weakEqual e1 e2 then true
        else failwith (Printf.sprintf "%s\n\n%s" (to_string e1) (to_string e2)))

  let test_opti_freeVar opti opti_name =
    QCheck.Test.make ~count:100 ~max_gen:500 ~name:("Opt " ^ opti_name)
      (arbitrary_term (List.init 10 (fun i -> (("x", i), Type.Real))))
      (fun expr ->
        let module AT = Target.Traverse (Strategy.All) in
        let fv = freeVar expr in
        let e1 =
          match AT.map opti expr with
          | Rewriter.Success expr -> expr
          | Rewriter.Failure _ -> QCheck.assume_fail ()
        in
        let fv1 = freeVar e1 in
        VarSet.subset fv1 fv)

  let test_opti_list =
    List.map
      (fun (opti, opti_name) -> test_opti opti opti_name)
      Optimisation.T.opti_list

  let test_opti_freeVar_list =
    List.map
      (fun (opti, opti_name) -> test_opti_freeVar opti opti_name)
      Optimisation.T.opti_list

  let test_opti_repeat opti opti_name =
    QCheck.Test.make ~count:10 ~max_gen:50 ~name:("Opt " ^ opti_name)
      arbitrary_closed_term (fun expr ->
        let module TR = Target.Traverse (Strategy.Repeat) in
        let e1 =
          interpret
            (match TR.map opti expr with
            | Rewriter.Success expr -> expr
            | Rewriter.Failure _ -> QCheck.assume_fail ())
            []
        in
        let e2 = interpret expr [] in
        if weakEqual e1 e2 then true
        else failwith (Printf.sprintf "%s\n\n%s" (to_string e1) (to_string e2)))

  let test_opti_repeat_list =
    List.map
      (fun (opti, opti_name) -> test_opti_repeat opti opti_name)
      Optimisation.T.exact_opti_list
end

module S = struct
  open Source

  let arbitrary_closed_term =
    QCheck.make
      QCheck.Gen.(int_bound 20 >>= fun i -> SourceGen.gen [] i Type.Real)
      ~print:to_string ~shrink:SourceGen.shrink

  let arbitrary_term freeVar =
    QCheck.make
      QCheck.Gen.(int_bound 20 >>= fun i -> SourceGen.gen freeVar i Type.Real)
      ~print:to_string ~shrink:SourceGen.shrink

  (* Basic Tests *)
  let test_isWellTyped =
    QCheck.Test.make ~count:100 ~name:"isWellTyped" arbitrary_closed_term
      isWellTyped

  let test_equal =
    QCheck.Test.make ~count:100 ~name:"equal" arbitrary_closed_term (fun expr ->
        equal expr expr)

  let test_parse =
    QCheck.Test.make ~count:100 ~name:"parse" arbitrary_closed_term (fun expr ->
        match Parse.of_string (to_string expr) with
        | Result.Ok e -> equal expr e
        | Result.Error _ -> false)

  let test_interpret =
    QCheck.Test.make ~count:100 ~name:"interp" arbitrary_closed_term
      (fun expr ->
        ignore (interpret expr []);
        true)

  let test_anf =
    QCheck.Test.make ~count:100 ~name:"anf" arbitrary_closed_term (fun expr ->
        Float.equal
          (interpret (Transforms.Anf.SourceAnf.anf expr) [])
          (interpret expr []))

  let test_weakAnf =
    QCheck.Test.make ~count:100 ~name:"weakAnf" arbitrary_closed_term
      (fun expr ->
        Float.equal
          (interpret (Transforms.Anf.SourceAnf.weakAnf expr) [])
          (interpret expr []))

  let test_isInAnf_anf =
    QCheck.Test.make ~count:100 ~name:"isInAnf.anf" arbitrary_closed_term
      (fun expr -> Transforms.Anf.SourceAnf.(isInAnf (anf expr)))

  let test_isInWeakAnf_weakAnf =
    QCheck.Test.make ~count:100 ~name:"isInWeakAnf.weakAnf"
      arbitrary_closed_term (fun expr ->
        Transforms.Anf.SourceAnf.(isInWeakAnf (weakAnf expr)))

  let test_list =
    [
      test_isWellTyped;
      test_equal;
      test_parse;
      test_interpret;
      test_anf;
      test_weakAnf;
      test_isInWeakAnf_weakAnf;
    ]

  exception Fail

  (* Test AD *)

  let rec all_pairs = function
    | [] -> []
    | h :: t -> List.map (fun x -> (h, x)) t @ all_pairs t

  let test_grads grad1 grad1_name grad2 grad2_name =
    let freeVar = List.init 10 (fun i -> (("x", i), Type.Real)) in
    QCheck.Test.make ~count:100
      ~name:(Printf.sprintf "Grad %s %s" grad1_name grad2_name)
      (arbitrary_term freeVar) (fun expr ->
        let e1 = grad1 freeVar expr in
        let e2 = grad2 freeVar expr in
        try
          for _ = 0 to 100 do
            let context =
              List.map
                (fun (name, t) ->
                  ( (name, Target.Type.from_source t),
                    Target.Const Random.(run (float 1.)) ))
                freeVar
            in
            if
              not
                (Target.weakEqual
                   (Target.interpret e1 context)
                   (Target.interpret e2 context))
            then raise Fail
          done;
          true
        with Fail -> false)

  let test_grads_list =
    List.map
      (fun ((g1, n1), (g2, n2)) -> test_grads g1 n1 g2 n2)
      (all_pairs
         [
           (Transforms.ForwardMode.grad, "ForwardMode.grad");
           (Transforms.ReverseMode.grad, "ReverseMode.grad");
           (Transforms.ReverseMode.grad2, "ReverseMode.grad2");
           (Transforms.JetAD.CoJets12.grad, "JetAD.CoJets12.grad");
         ])
end

module O = struct
  module TR = Target.Traverse (Strategy.Repeat)
  module TO = Target.Traverse (Strategy.One)
  module TA = Target.Traverse (Strategy.All)

  let test_repeat opt =
    QCheck.Test.make ~count:10 ~name:"repeat" T.arbitrary_closed_term
      (fun expr ->
        let expr =
          match TR.map opt expr with Failure expr | Success expr -> expr
        in
        match TO.map opt expr with Failure _ -> true | Success _ -> false)

  let test_list =
    [
      test_repeat Optimisation.T.constantPropagation;
      test_repeat Optimisation.T.letCommutativity;
    ]
end

let () =
  let target = List.map QCheck_alcotest.to_alcotest T.test_list in
  let target_opti = List.map QCheck_alcotest.to_alcotest T.test_opti_list in
  let target_opti_freeVar =
    List.map QCheck_alcotest.to_alcotest T.test_opti_freeVar_list
  in
  let target_opti_repeat =
    List.map QCheck_alcotest.to_alcotest T.test_opti_repeat_list
  in
  let source = List.map QCheck_alcotest.to_alcotest S.test_list in
  let grads = List.map QCheck_alcotest.to_alcotest S.test_grads_list in
  let optimisation = List.map QCheck_alcotest.to_alcotest O.test_list in
  Alcotest.run "Main test"
    [
      ("Target Language", target);
      ("Opti Target Language", target_opti);
      ("Opti Free Var Target Language", target_opti_freeVar);
      ("Repeat Opti Target Language", target_opti_repeat);
      ("Source Language", source);
      ("New optimisation", optimisation);
      ("Grads", grads);
    ]
