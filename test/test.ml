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

  let type_gen =
    QCheck.Gen.(
      sized_size small_nat
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

  let closed_term_gen =
    QCheck.Gen.(
      sized_size (int_range 1 20) @@ fun i st ->
      fix
        (fun self (n, t) ->
          match t with
          | Real -> (
              match n with
              | 0 -> map const pfloat
              | n ->
                  let let_gen =
                    type_gen >>= fun ty ->
                    map2
                      (fun expr1 expr2 -> clet (Vars.fresh ()) ty expr1 expr2)
                      (self (n / 2, ty))
                      (self (n / 2, t))
                  in
                  frequency
                    [
                      (2, map2 apply1 Op.gen1 (self (n - 1, Real)));
                      ( 2,
                        map3 apply2 Op.gen2
                          (self (n / 2, Real))
                          (self (n / 2, Real)) );
                      (2, let_gen);
                      (1, map const pfloat);
                    ])
          | Arrow (_, _) ->
              let args, ret_type = unfold_arrow t in
              map
                (fun expr ->
                  func (List.map (fun tv -> (Vars.fresh (), tv)) args) expr)
                (self (n / 2, ret_type))
          | NProd l ->
              map
                (fun l -> tuple l)
                (flatten_l
                   (List.map (fun t -> self (n / (List.length l + 1), t)) l)))
        (i, type_gen st)
        st)

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

  let arbitrary_closed_term = QCheck.make closed_term_gen ~print:to_string

  (*~shrink:shrink_term*)

  let test =
    QCheck.Test.make ~count:10000 ~name:"closed_term_no_free_var"
      arbitrary_closed_term isWellTyped
end

let () =
  let target = List.map QCheck_alcotest.to_alcotest [ T.test ] in
  Alcotest.run "Main test" [ ("Target Language", target) ]
