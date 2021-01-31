open Containers
open Syntax

module T = struct
  open Target

  let arbitrary_closed_term =
    QCheck.make
      QCheck.Gen.(int_bound 20 >>= fun i -> TargetGen.gen [] i Type.Real)
      ~print:to_string ~shrink:TargetGen.shrink

  let arbitrary_term =
    QCheck.make
      QCheck.Gen.(
        int_bound 20 >>= fun i ->
        TargetGen.gen (List.init 10 (fun i -> (("x", i), Type.Real))) i Type.Real)
      ~print:to_string ~shrink:TargetGen.shrink

  let test_isWellTyped =
    QCheck.Test.make ~count:100 ~name:"isWellTyped" arbitrary_closed_term
      (fun term ->
        match inferType term with
        | Result.Ok _ -> true
        | Result.Error s -> failwith s)

  let test_equal =
    QCheck.Test.make ~count:100 ~name:"equal" arbitrary_closed_term (fun expr ->
        equal expr expr)

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
      test_interpret;
      test_anf;
      test_weakAnf;
      test_isInWeakAnf_weakAnf;
    ]

  let test_opti opti opti_name =
    QCheck.Test.make ~count:100 ~max_gen:500 ~name:("Opt " ^ opti_name)
      arbitrary_closed_term (fun expr ->
        let module AT = Target.Traverse(Strategy.All) in
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
      arbitrary_term (fun expr ->
        let module AT = Target.Traverse(Strategy.All) in
        let fv = freeVar expr in
        let e1 =
          match AT.map opti expr with
          | Rewriter.Success expr -> expr
          | Rewriter.Failure _ -> QCheck.assume_fail ()
        in
        let fv1 = freeVar e1 in
        VarSet.subset fv1 fv)

  let opti_list =
    let open Optimisation.T in
    [
      (lambdaRemoval, "LR");
      (forwardSubstitution, "FS");
      (letSimplification, "LS");
      (letCommutativity, "LC");
      (realFactorisation, "RF");
      (trigoSimplification, "TS");
      (zeroSimplification, "ZS");
      (simpleAlgebraicSimplifications, "SAS");
      (constantPropagation, "CP");
      (deadVarElim, "DVE");
    ]

  let test_opti_list =
    List.map (fun (opti, opti_name) -> test_opti opti opti_name) opti_list

  let test_opti_freeVar_list =
    List.map
      (fun (opti, opti_name) -> test_opti_freeVar opti opti_name)
      opti_list
end

module S = struct
  open Source

  let real = Type.Real

  let prod x y = Type.Prod (x, y)

  let type_gen depth =
    QCheck.Gen.(
      sized_size (int_bound depth)
      @@ fix (fun _self n ->
             match n with
             | 0 -> return Type.Real
             | _n ->
                 frequency
                   [
                     (*(2, map2 prod (self (n / 2)) (self (n / 2)));*)
                     (1, return Type.Real);
                   ]))

  let var x t = Var (x, t)

  let const x = Const x

  let apply1 op exp = Apply1 (op, exp)

  let apply2 op exp1 exp2 = Apply2 (op, exp1, exp2)

  let clet v t exp1 exp2 = Let (v, t, exp1, exp2)

  let find_by_ty ty = List.find_opt (fun (_, t) -> Type.equal t ty)

  let dist_to_type (targetTy : Type.t) (ty : Type.t) =
    match (targetTy, ty) with Type.Real, Type.Real -> Some 0 | _ -> None

  let random_closest_type targetTy tyList =
    let open QCheck.Gen in
    List.mapi
      (fun i ty ->
        match dist_to_type targetTy ty with
        | None -> None
        | Some d -> Some (ty, i, d))
      tyList
    |> CCList.keep_some
    |> function
    | [] -> None
    | (_, _, d) :: tl as l ->
        let d_min = List.fold_left (fun x (_, _, d) -> min x d) d tl in
        Some (generate1 (oneofl (List.filter (fun (_, _, d) -> d = d_min) l)))

  let rec complet_to_type _context n (targetTy : Type.t) (term : t)
      (ty : Type.t) =
    if Type.equal targetTy ty then Some term
    else if n <= 0 then None
    else
      match (targetTy, ty) with Type.Real, Type.Real -> Some term | _ -> None

  and get_from_context context n targetTy =
    List.filter_map
      (fun (v, t) ->
        match dist_to_type targetTy t with
        | None -> None
        | Some d -> Some (v, t, d))
      context
    |> function
    | [] -> None
    | (_, _, d) :: t as l -> (
        let d_min = List.fold_left (fun x (_, _, d) -> min x d) d t in
        match List.filter (fun (_, _, d) -> d = d_min) l with
        | [] -> None
        | l ->
            let v, t, _ = QCheck.Gen.(generate1 (oneofl l)) in
            complet_to_type context n targetTy (Var (v, t)) t)

  and term_gen context (n : int) targetTy =
    QCheck.Gen.(
      sized_size (return n) @@ fun i ->
      fix
        (fun self (n, context, targetTy) ->
          if n <= 0 then
            match targetTy with
            | Type.Real -> map const (float_bound_exclusive 1.)
            | Type.Prod (_x1, _x2) -> failwith "Prod: not implemented"
          else
            let let_gen =
              let newVar = Var.fresh () in
              let varType = generate1 (type_gen (n / 10)) in
              let newContext = (newVar, varType) :: context in
              map2
                (fun expr1 expr2 -> clet newVar varType expr1 expr2)
                (self (n / 4, context, varType))
                (self (3 * n / 4, newContext, targetTy))
            in
            let gen_list = [ let_gen ] in
            let gen_list =
              match get_from_context context n targetTy with
              | None -> gen_list
              | Some term -> return term :: gen_list
            in
            match targetTy with
            | Type.Real ->
                oneof
                  (map2 apply1 OperatorGen.gen1 (self (n - 1, context, Type.Real))
                  :: map3 apply2 OperatorGen.gen2
                       (self (n / 2, context, Type.Real))
                       (self (n / 2, context, Type.Real))
                  :: map const (float_bound_exclusive 1.)
                  :: gen_list)
            | _ -> oneof gen_list)
        (i, context, targetTy))

  let rec shrink_term expr =
    let open QCheck.Iter in
    match expr with
    | Var (_, _) | Const _ -> empty
    | Apply1 (op, expr) ->
        return expr
        <+> (shrink_term expr >|= apply1 op)
        <+> (OperatorGen.shrink1 op >|= fun op -> apply1 op expr)
    | Apply2 (op, expr1, expr2) ->
        of_list [ expr1; expr2 ]
        <+> (shrink_term expr1 >|= fun expr -> apply2 op expr expr2)
        <+> (shrink_term expr2 >|= fun expr -> apply2 op expr1 expr)
    | Let (x, t, expr1, expr2) ->
        shrink_term expr1
        >|= (fun expr -> clet x t expr expr2)
        <+> (shrink_term expr2 >|= fun expr -> clet x t expr1 expr)

  let arbitrary_closed_term =
    QCheck.make
      QCheck.Gen.(int_bound 20 >>= fun i -> term_gen [] i Type.Real)
      ~print:to_string ~shrink:shrink_term

  let arbitrary_term =
    QCheck.make
      QCheck.Gen.(
        int_bound 20 >>= fun i ->
        term_gen (List.init 10 (fun i -> (("x", i), Type.Real))) i Type.Real)
      ~print:to_string ~shrink:shrink_term

  let test_isWellTyped =
    QCheck.Test.make ~count:100 ~name:"isWellTyped" arbitrary_closed_term
      isWellTyped

  let test_equal =
    QCheck.Test.make ~count:100 ~name:"equal" arbitrary_closed_term (fun expr ->
        equal expr expr)

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
      test_interpret;
      test_anf;
      test_weakAnf;
      test_isInWeakAnf_weakAnf;
    ]
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
  let term = QCheck.Gen.generate1 (TargetGen.gen [] 10 Target.Type.Real) in
  Format.printf "%a@." Target.pp term

let () =
  let target = List.map QCheck_alcotest.to_alcotest T.test_list in
  let target_opti = List.map QCheck_alcotest.to_alcotest T.test_opti_list in
  let target_opti_freeVar =
    List.map QCheck_alcotest.to_alcotest T.test_opti_freeVar_list
  in
  let source = List.map QCheck_alcotest.to_alcotest S.test_list in
  let optimisation = List.map QCheck_alcotest.to_alcotest O.test_list in
  Alcotest.run "Main test"
    [
      ("Target Language", target);
      ("Opti Target Language", target_opti);
      ("Opti Free Var Target Language", target_opti_freeVar);
      ("Source Language", source);
      ("New optimisation", optimisation);
    ]
