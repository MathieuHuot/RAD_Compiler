open Containers
open Syntax

module VarSet = CCSet.Make (struct
  type t = Vars.t

  let compare x y = CCPair.compare CCString.compare CCInt.compare x y
end)

module Op = struct
  open Operators

  let power n = Power n

  let gen1 =
    QCheck.Gen.(
      oneof
        [
          return Cos;
          return Sin;
          return Exp;
          return (Minus : op1);
          map power (int_bound 5);
        ])

  let gen2 = QCheck.Gen.(oneofl [ Plus; Times; (Minus : op2) ])

  let shrink_op1 op =
    let open QCheck.Iter in
    match op with Power n -> QCheck.Shrink.int n >|= power | _ -> empty
end

module T = struct
  open TargetLanguage

  let real = Real

  let arrow t1 t2 = Arrow (t1, t2)

  let nprod l = NProd l

  let type_gen depth =
    QCheck.Gen.(
      sized_size (int_bound depth)
      @@ fix (fun self n ->
             match n with
             | 0 -> return Real
             | n ->
                 frequency
                   [
                     ( 2,
                       map2 arrow
                         (list_size (int_bound 20) (self (min (n / 20) 2)))
                         (self (n / 2)) );
                     ( 2,
                       int_range 0 20 >>= fun i ->
                       map nprod (list_size (return i) (self (n / max 1 i))) );
                     (1, return Real);
                   ]))

  let var x t = Var (x, t)

  let const x = Const x

  let apply1 op exp = Apply1 (op, exp)

  let apply2 op exp1 exp2 = Apply2 (op, exp1, exp2)

  let clet v t exp1 exp2 = Let (v, t, exp1, exp2)

  let func l exp = Fun (l, exp)

  let app exp l = App (exp, l)

  let tuple l = Tuple l

  let ncase exp1 l exp2 = NCase (exp1, l, exp2)

  let find_by_ty ty = List.find_opt (fun (_, t) -> equalTypes t ty)

  let rec dist_to_type (targetTy : targetType) (ty : targetType) =
    match (targetTy, ty) with
    | Real, Real -> Some 0
    | Real, Arrow (l, ty) ->
        CCOpt.(dist_to_type targetTy ty >|= ( + ) (List.length l))
    | Arrow (_, _), Real -> None
    | Arrow (l1, t1), Arrow (l2, t2) ->
        CCOpt.(
          dist_to_type t1 t2 >>= fun d ->
          List.map
            (fun t ->
              match List.filter_map (dist_to_type t) l2 with
              | [] -> None
              | h :: t -> Some (List.fold_left min h t))
            l1
          |> sequence_l
          >|= fun l -> List.fold_left ( + ) d l)
    | NProd l1, NProd l2 ->
        CCOpt.(
          List.map
            (fun t ->
              match List.filter_map (dist_to_type t) l2 with
              | [] -> None
              | h :: t -> Some (List.fold_left min h t))
            l1
          |> sequence_l
          >|= fun l -> List.fold_left ( + ) 0 l)
    | NProd l, _ ->
        CCOpt.(
          List.map (fun t -> dist_to_type t ty) l
          |> sequence_l >|= List.fold_left ( + ) 1)
    | _, NProd l -> (
        match List.filter_map (dist_to_type targetTy) l with
        | [] -> None
        | h :: t -> Some (1 + List.fold_left min h t))

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

  let rec complet_to_type context n (targetTy : targetType) (term : targetSyn)
      (ty : targetType) =
    if equalTypes targetTy ty then Some term
    else if n <= 0 then None
    else
      match (targetTy, ty) with
      | Real, Real -> Some term
      | Real, Arrow (l, ty) ->
          complet_to_type context
            (n - List.length l)
            targetTy
            (App
               ( term,
                 List.map
                   (fun t ->
                     QCheck.Gen.generate1
                       (term_gen context (n - List.length l) t))
                   l ))
            ty
      | NProd targetList, NProd termList ->
          CCOpt.(
            List.map
              (fun t ->
                match random_closest_type t termList with
                | None -> None
                | Some x -> Some (t, x))
              targetList
            |> sequence_l
            >>= fun l ->
            let newVars = List.map (fun t -> (Vars.fresh (), t)) termList in
            List.map
              (fun (targetTy, (_, i, _)) ->
                let v, t = CCList.get_at_idx_exn i newVars in
                complet_to_type context
                  (n - List.length targetList)
                  targetTy
                  (Var (v, t))
                  t)
              l
            |> sequence_l
            >|= fun l -> NCase (term, newVars, Tuple l))
      | _, NProd typeList ->
          CCOpt.(
            random_closest_type targetTy typeList >>= fun (t, i, _) ->
            let newVars = List.map (fun t -> (Vars.fresh (), t)) typeList in
            complet_to_type context (n - 1) targetTy
              (NCase
                 ( term,
                   newVars,
                   let v, ty = CCList.get_at_idx_exn i newVars in
                   Var (v, ty) ))
              t)
      | Arrow (_, _), Real -> None
      | Arrow (_l1, _t1), Arrow (_l2, _t2) -> None
      | NProd l, _ ->
          CCOpt.(
            List.map
              (fun t ->
                complet_to_type context (n / max 2 (List.length l)) t term ty)
              l
            |> sequence_l
            >|= fun l -> Tuple l)

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
            | Real -> map const (float_bound_exclusive 1.)
            | Arrow (tyList, retType) ->
                let argsList =
                  List.map (fun tv -> (Vars.fresh (), tv)) tyList
                in
                let newContext = argsList @ context in
                map
                  (fun expr -> func argsList expr)
                  (self (n / 2, newContext, retType))
            | NProd tyList ->
                map tuple
                  (flatten_l
                     (List.map
                        (fun t ->
                          self (n / max (List.length tyList) 1, context, t))
                        tyList))
          else
            let let_gen =
              let newVar = Vars.fresh () in
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
            | Real ->
                oneof
                  (map2 apply1 Op.gen1 (self (n - 1, context, Real))
                  :: map3 apply2 Op.gen2
                       (self (n / 2, context, Real))
                       (self (n / 2, context, Real))
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
        <+> (Op.shrink_op1 op >|= fun op -> apply1 op expr)
    | Apply2 (op, expr1, expr2) ->
        of_list [ expr1; expr2 ]
        <+> (shrink_term expr1 >|= fun expr -> apply2 op expr expr2)
        <+> (shrink_term expr2 >|= fun expr -> apply2 op expr1 expr)
    | Let (x, t, expr1, expr2) ->
        shrink_term expr1
        >|= (fun expr -> clet x t expr expr2)
        <+> (shrink_term expr2 >|= fun expr -> clet x t expr1 expr)
    | Fun (vars, expr) -> shrink_term expr >|= fun expr -> func vars expr
    | App (expr, exprs) ->
        shrink_term expr
        >|= (fun expr -> app expr exprs)
        <+> ( QCheck.Shrink.list_elems shrink_term exprs >|= fun exprs ->
              app expr exprs )
    | Tuple exprs -> QCheck.Shrink.list_elems shrink_term exprs >|= tuple
    | NCase (expr1, vars, expr2) ->
        shrink_term expr1
        >|= (fun expr -> ncase expr vars expr2)
        <+> (shrink_term expr2 >|= fun expr -> ncase expr1 vars expr)

  let arbitrary_closed_term =
    QCheck.make
      QCheck.Gen.(int_bound 20 >>= fun i -> term_gen [] i Real)
      ~print:to_string ~shrink:shrink_term

  let arbitrary_term =
    QCheck.make
      QCheck.Gen.(
        int_bound 20 >>= fun i ->
        term_gen (List.init 10 (fun i -> (("x", i), Real))) i Real)
      ~print:to_string ~shrink:shrink_term

  let test_isWellTyped =
    QCheck.Test.make ~count:1000 ~name:"isWellTyped" arbitrary_closed_term
      (fun term ->
        match typeTarget term with
        | Result.Ok _ -> true
        | Result.Error s -> failwith s)

  let test_equalTerms =
    QCheck.Test.make ~count:1000 ~name:"equalTerms" arbitrary_closed_term
      (fun expr -> equalTerms expr expr)

  let test_interpret =
    QCheck.Test.make ~count:1000 ~name:"interp" arbitrary_closed_term
      (fun expr -> match interpret expr [] with Const _ -> true | _ -> false)

  let test_anf =
    QCheck.Test.make ~count:1000 ~name:"anf" arbitrary_closed_term (fun expr ->
        equalTerms
          (interpret (Transforms.Anf.TargetAnf.anf expr) [])
          (interpret expr []))

  let test_weakAnf =
    QCheck.Test.make ~count:1000 ~name:"weakAnf" arbitrary_closed_term
      (fun expr ->
        equalTerms
          (interpret (Transforms.Anf.TargetAnf.weakAnf expr) [])
          (interpret expr []))

  let test_isInAnf_anf =
    QCheck.Test.make ~count:1000 ~name:"isInAnf.anf" arbitrary_closed_term
      (fun expr -> Transforms.Anf.TargetAnf.(isInAnf (anf expr)))

  let test_isInWeakAnf_weakAnf =
    QCheck.Test.make ~count:1000 ~name:"isInWeakAnf.weakAnf"
      arbitrary_closed_term (fun expr ->
        Transforms.Anf.TargetAnf.(isInWeakAnf (weakAnf expr)))

  let test_list =
    [
      test_isWellTyped;
      test_equalTerms;
      test_interpret;
      test_anf;
      test_weakAnf;
      test_isInWeakAnf_weakAnf;
    ]

  let test_opti opti opti_name =
    QCheck.Test.make ~count:1000 ~name:("Opt " ^ opti_name)
      arbitrary_closed_term (fun expr ->
        let e1 =
          interpret
            Rewrite.(
              Strategies.Strategy.run (Strategies.Strategy.tryStrat opti expr))
            []
        in
        let e2 = interpret expr [] in
        if weakEqualTerms e1 e2 then true
        else failwith (Printf.sprintf "%s\n\n%s" (to_string e1) (to_string e2)))

  let test_opti_freeVar opti opti_name =
    QCheck.Test.make ~count:1000 ~name:("Opt " ^ opti_name) arbitrary_term
      (fun expr ->
        let fv = freeVars expr |> VarSet.of_list in
        let e1 =
          Rewrite.(
            Strategies.Strategy.run (Strategies.Strategy.tryStrat opti expr))
        in
        let fv1 = freeVars e1 |> VarSet.of_list in
        VarSet.subset fv1 fv)

  let opti_list =
    [
      (Rewrite.Optimisations.LR.run, "LR");
      (Rewrite.Optimisations.FS.run, "FS");
      (Rewrite.Optimisations.LS.run, "LS");
      (Rewrite.Optimisations.LC.run, "LC");
      (Rewrite.Optimisations.RF.run, "RF");
      (Rewrite.Optimisations.TS.run, "TS");
      (Rewrite.Optimisations.ZS.run, "ZS");
      (Rewrite.Optimisations.SAS.run, "SAS");
      (Rewrite.Optimisations.CP.run, "CP");
      (Rewrite.Optimisations.DVE.run, "DVE");
    ]

  let test_opti_list =
    List.map (fun (opti, opti_name) -> test_opti opti opti_name) opti_list

  let test_opti_freeVar_list =
    List.map
      (fun (opti, opti_name) -> test_opti_freeVar opti opti_name)
      opti_list
end

let () =
  let target = List.map QCheck_alcotest.to_alcotest T.test_list in
  let target_opti = List.map QCheck_alcotest.to_alcotest T.test_opti_list in
  let target_opti_freeVar =
    List.map QCheck_alcotest.to_alcotest T.test_opti_freeVar_list
  in
  Alcotest.run "Main test"
    [
      ("Target Language", target);
      ("Opti Target Language", target_opti);
      ("Opti Free Vars Target Language", target_opti_freeVar);
    ]
