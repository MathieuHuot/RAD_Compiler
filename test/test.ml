open Syntax

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
          map power small_nat;
        ])

  let gen2 = QCheck.Gen.(oneofl [ Plus; Times; (Minus : op2) ])
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
                     (2, map2 arrow (self (n / 2)) (self (n / 2)));
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

  let partial_unfold_arrow l t =
    QCheck.Gen.(
      fix
        (fun self (l, t) ->
          match t with
          | Arrow (arg_ty, ret_ty) ->
              frequency
                [ (1, return (List.rev l, t)); (1, self (arg_ty :: l, ret_ty)) ]
          | _ -> return (List.rev l, t))
        (l, t))

  let closed_term_gen ty_gen =
    QCheck.Gen.(
      sized_size (int_range 1 20) @@ fun i ->
      fix
        (fun self (n, context, t) ->
          match t with
          | Real -> (
              match n with
              | 0 -> map const pfloat
              | n ->
                  let let_gen =
                    let newVar = Vars.fresh () in
                    let ty = generate1 (type_gen (max n 1)) in
                    let newContext = (newVar, ty) :: context in
                    map2
                      (fun expr1 expr2 -> clet (Vars.fresh ()) ty expr1 expr2)
                      (self (n / 2, newContext, ty))
                      (self (n / 2, newContext, t))
                  in
                  frequency
                    [
                      (2, map2 apply1 Op.gen1 (self (n - 1, context, Real)));
                      ( 2,
                        map3 apply2 Op.gen2
                          (self (n / 2, context, Real))
                          (self (n / 2, context, Real)) );
                      (2, let_gen);
                      (1, map const pfloat);
                    ])
          | Arrow (argTy, retTy) ->
              let argsTy, retType =
                generate1 (partial_unfold_arrow [ argTy ] retTy)
              in
              let argsList = List.map (fun tv -> (Vars.fresh (), tv)) argsTy in
              let newContext = argsList @ context in
              map
                (fun expr -> func argsList expr)
                (self (n / 2, newContext, retType))
          | NProd l ->
              map
                (fun l -> tuple l)
                (flatten_l
                   (List.map
                      (fun t -> self (n / max (List.length l) 1, context, t))
                      l)))
        (i, [], generate1 ty_gen))

  let rec shrink_term expr =
    let open QCheck.Iter in
    match expr with
    | Var (_, _) | Const _ -> empty
    | Apply1 (op, expr) -> return expr <+> (shrink_term expr >|= apply1 op)
    | Apply2 (op, expr1, expr2) ->
        of_list [ expr1; expr2 ]
        <+> (shrink_term expr1 >|= fun expr -> apply2 op expr expr2)
        <+> (shrink_term expr2 >|= fun expr -> apply2 op expr1 expr)
    | Let (x, t, expr1, expr2) ->
        of_list [ expr1; expr2 ]
        <+> (shrink_term expr1 >|= fun expr -> clet x t expr expr2)
        <+> (shrink_term expr2 >|= fun expr -> clet x t expr1 expr)
    | Fun (vars, expr) ->
        return expr <+> (shrink_term expr >|= fun expr -> func vars expr)
    | App (expr, exprs) ->
        return expr <+> of_list exprs
        <+> (shrink_term expr >|= fun expr -> app expr exprs)
        <+> ( QCheck.Shrink.list_elems shrink_term exprs >|= fun exprs ->
              app expr exprs )
    | Tuple exprs ->
        of_list exprs <+> (QCheck.Shrink.list_elems shrink_term exprs >|= tuple)
    | NCase (expr1, vars, expr2) ->
        of_list [ expr1; expr2 ]
        <+> (shrink_term expr1 >|= fun expr -> ncase expr vars expr2)
        <+> (shrink_term expr2 >|= fun expr -> ncase expr1 vars expr)

  let arbitrary_closed_term =
    QCheck.make (closed_term_gen QCheck.Gen.(return Real)) ~print:to_string

  (*~shrink:shrink_term*)

  let test_isWellTyped =
    QCheck.Test.make ~count:1000 ~name:"isWellTyped" arbitrary_closed_term
      isWellTyped

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
      test_isInAnf_anf;
      test_isInWeakAnf_weakAnf;
    ]

  let test_opti opti opti_name =
    QCheck.Test.make ~count:1000 ~name:("Opt " ^ opti_name)
      arbitrary_closed_term (fun expr ->
        equalTerms
          (interpret
             Rewrite.(
               Strategies.Strategy.run (Strategies.Strategy.tryStrat opti expr))
             [])
          (interpret expr []))

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
end

let () =
  let target = List.map QCheck_alcotest.to_alcotest T.test_list in
  let target_opti = List.map QCheck_alcotest.to_alcotest T.test_opti_list in
  Alcotest.run "Main test"
    [ ("Target Language", target); ("Opti Target Language", target_opti) ]
