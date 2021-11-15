open Syntax
open HeapType
open Formula
open Expression

module Log = (val Logs.src_log Logging.chomp_src : Logs.LOG)

let rec chomp_t1_arith (bind : Syntax.var) (b0 : int) (expr : Expression.arith)
    =
  match expr with
  | Length (b, pkt) as l ->
    if bind = b && [%compare.equal: packet] pkt PktIn then
      Plus (l, Num 1)
    else
      l
  | Plus (t1, t2) -> Plus (chomp_t1_arith bind b0 t1, chomp_t1_arith bind b0 t2)
  | Num _ as e -> e

let rec chomp_t1_bv (bind : Syntax.var) (b0 : int) (expr : Expression.bv) =
  match expr with
  | Slice (Packet (b, PktIn), l, r) as slice ->
    if b = bind then
      if r <= 1 then
        Bv (Cons (B b0, Nil))
      else if l = 0 then
        Concat (Bv (Cons (B b0, Nil)), Slice (Packet (b, PktIn), 0, r - 1))
      else if l <> 0 then
        Slice (Packet (b, PktIn), l - 1, r - 1)
      else
        slice
    else
      slice
  | Packet (b, pkt) as packet ->
    if bind = b && [%compare.equal: packet] pkt PktIn then
      Concat (Bv (Cons (B b0, Nil)), packet)
    else
      packet
  | Minus (t1, t2) ->
    Minus (chomp_t1_bv bind b0 t1, chomp_t1_bv bind b0 t2)
    (* TODO: Check if this is correct.*)
  | Concat (t1, t2) -> Concat (chomp_t1_bv bind b0 t1, chomp_t1_bv bind b0 t2)
  | (Slice (Packet (_, PktOut), _, _) | Slice (Instance (_, _), _, _) | Bv _) as
    t ->
    t

let chomp_t1 (expr : Expression.t) (bind : Syntax.var) (b0 : int) =
  match expr with
  | ArithExpr e -> ArithExpr (chomp_t1_arith bind b0 e)
  | BvExpr e -> BvExpr (chomp_t1_bv bind b0 e)

let rec chomp_e1 (expr : Formula.t) (binder : var) (b0 : int) =
  match expr with
  | Eq (t1, t2) -> Eq (chomp_t1 t1 binder b0, chomp_t1 t2 binder b0)
  | Gt (t1, t2) -> Gt (chomp_t1 t1 binder b0, chomp_t1 t2 binder b0)
  | And (e1, e2) -> And (chomp_e1 e1 binder b0, chomp_e1 e2 binder b0)
  | Or (e1, e2) -> Or (chomp_e1 e1 binder b0, chomp_e1 e2 binder b0)
  | Implies (e1, e2) -> Implies (chomp_e1 e1 binder b0, chomp_e1 e2 binder b0)
  | Neg e -> Neg (chomp_e1 e binder b0)
  | (True | False | IsValid (_, _)) as e -> e

and chomp_ref1 (hty : HeapType.t) binder b0 =
  match hty with
  | Sigma (x, hty1, hty2) ->
    Sigma (x, chomp_ref1 hty1 binder b0, chomp_ref1 hty2 (binder + 1) b0)
  | Choice (hty1, hty2) ->
    Choice (chomp_ref1 hty1 binder b0, chomp_ref1 hty2 binder b0)
  | Refinement (x, hty, e) ->
    Refinement (x, chomp_ref1 hty binder b0, chomp_e1 e (binder + 1) b0)
  | Substitution (hty1, x, hty2) ->
    let hty1' = chomp_ref1 hty1 (binder + 1) b0 in
    let hty2' = chomp_ref1 hty2 binder b0 in
    Substitution (hty1', x, hty2')
  | (Nothing | Top) as hty' -> hty'

let rec chomp1 (hty : HeapType.t) ctx b0 =
  match hty with
  | Sigma (x, hty1, hty2) ->
    let left = Sigma (x, chomp1 hty1 ctx b0, chomp_ref1 hty2 0 b0) in
    let ctx' = Env.add_binding ctx x (Env.VarBind hty1) in
    let right =
      let ref = Eq (ArithExpr (Length (0, PktIn)), ArithExpr (Num 0)) in
      let y = Env.pick_fresh_name ctx' x in
      Sigma (x, Refinement (y, hty1, ref), chomp1 hty2 ctx' b0)
    in
    Choice (left, right)
  | Choice (hty1, hty2) -> Choice (chomp1 hty1 ctx b0, chomp1 hty2 ctx b0)
  | Refinement (x, hty, e) -> Refinement (x, chomp1 hty ctx b0, chomp_e1 e 0 b0)
  | Substitution (hty1, x, hty2) ->
    let ctx' = Env.add_binding ctx x (Env.VarBind hty2) in
    let hty1' = chomp1 hty1 ctx' b0 in
    Substitution (hty1', x, hty2)
  | (Nothing | Top) as hty' -> hty'

let rec heap_tref1_bv (expr : Expression.bv) b0 binder inst n =
  match expr with
  | Bv (Cons (B b1, bv)) when b0 = b1 ->
    let result =
      Concat
        ( Slice
            ( Instance (binder, inst),
              Instance.sizeof inst - n,
              Instance.sizeof inst - n + 1 ),
          heap_tref1_bv (Bv bv) b0 binder inst n )
    in
    Simplify.fold_concat result
  | Bv (Cons (b, bv)) ->
    let result =
      Concat (Bv (Cons (b, Nil)), heap_tref1_bv (Bv bv) b0 binder inst n)
    in
    Simplify.fold_concat result
  | Concat (t1, t2) ->
    let t1' = heap_tref1_bv t1 b0 binder inst n |> Simplify.fold_concat in
    let t2' = heap_tref1_bv t2 b0 binder inst n |> Simplify.fold_concat in
    Concat (t1', t2')
  | Minus (t1, t2) ->
    let t1' = heap_tref1_bv t1 b0 binder inst n |> Simplify.fold_concat in
    let t2' = heap_tref1_bv t2 b0 binder inst n |> Simplify.fold_concat in
    Minus (t1', t2')
  | (Bv Nil | Slice (_, _, _) | Packet (_, _)) as t -> t

let heap_tref1 (t : Expression.t) b0 binder inst n =
  let open Expression in
  match t with
  | BvExpr e -> BvExpr (heap_tref1_bv e b0 binder inst n)
  | (ArithExpr (Num _) | ArithExpr (Length (_, _)) | ArithExpr (Plus (_, _))) as
    t ->
    t

let rec heap_eref1 (expr : Formula.t) b0 binder inst n =
  match expr with
  | Eq (tm1, tm2) ->
    let tm1' = heap_tref1 tm1 b0 binder inst n |> Simplify.simplify_expr in
    let tm2' = heap_tref1 tm2 b0 binder inst n |> Simplify.simplify_expr in
    Eq (tm1', tm2')
  | Gt (tm1, tm2) ->
    let tm1' = heap_tref1 tm1 b0 binder inst n |> Simplify.simplify_expr in
    let tm2' = heap_tref1 tm2 b0 binder inst n |> Simplify.simplify_expr in
    Gt (tm1', tm2')
  | Neg e' -> Neg (heap_eref1 e' b0 binder inst n)
  | And (e1, e2) ->
    And (heap_eref1 e1 b0 binder inst n, heap_eref1 e2 b0 binder inst n)
  | Or (e1, e2) ->
    Or (heap_eref1 e1 b0 binder inst n, heap_eref1 e2 b0 binder inst n)
  | Implies (e1, e2) ->
    Implies (heap_eref1 e1 b0 binder inst n, heap_eref1 e2 b0 binder inst n)
  | (True | False | IsValid (_, _)) as e -> e

and heap_ref1 (hty : HeapType.t) (b0 : int) (binder : var) (inst : Instance.t)
    (n : int) =
  match hty with
  | Sigma (x, hty1, hty2) ->
    let hty1' = heap_ref1 hty1 b0 binder inst n in
    let hty2' = heap_ref1 hty2 b0 (binder + 1) inst n in
    Sigma (x, hty1', hty2')
  | Choice (hty1, hty2) ->
    let hty1' = heap_ref1 hty1 b0 binder inst n in
    let hty2' = heap_ref1 hty2 b0 binder inst n in
    Choice (hty1', hty2')
  | Refinement (x, hty, e) ->
    let hty' = heap_ref1 hty b0 binder inst n in
    let e' = heap_eref1 e b0 (binder + 1) inst n in
    Refinement (x, hty', e')
  | Substitution (hty1, x, hty2) ->
    let hty1' = heap_ref1 hty1 b0 (binder + 1) inst n in
    let hty2' = heap_ref1 hty2 b0 binder inst n in
    Substitution (hty1', x, hty2')
  | (Nothing | Top) as hty' -> hty'

let rec chomp_rec (hty : HeapType.t) (ctx : Env.context) (n : int)
    (binder : int) (inst : Instance.t) (b0 : int) (header_table : HeaderTable.t)
    =
  if n = 0 then
    hty
  else
    let hty' = heap_ref1 (chomp1 hty ctx b0) b0 binder inst n in
    chomp_rec hty' ctx (n - 1) binder inst (b0 + 1) header_table

let chomp (hty : HeapType.t) (ctx : Env.context) (inst : Instance.t)
    (header_table : HeaderTable.t) =
  chomp_rec hty ctx (Instance.sizeof inst) 0 inst 0 header_table

module Optimized (P : Prover.S) = struct
  open Core_kernel
  open Result.Let_syntax

  let rec remove_false_branches (header_type : HeapType.t) (ctx : Env.context)
      (header_table : HeaderTable.t) =
    match header_type with
    | Nothing -> return Nothing
    | Top -> return Top
    | Sigma (x, hty1, hty2) ->
      let ctx' = Env.add_binding ctx x (Env.VarBind hty1) in
      let%bind hty1' = remove_false_branches hty1 ctx header_table in
      let%map hty2' = remove_false_branches hty2 ctx' header_table in
      Sigma (x, hty1', hty2')
    | Choice (hty1, hty2) ->
      let%bind hty1_is_nothing =
        is_semantically_nothing header_table ctx hty1
      in
      if hty1_is_nothing then (
        Log.debug (fun m ->
            m
              "@[<v>Header type@ %a@ is equivalent to nothing. It will be removed from choice.@]"
              (Pretty.pp_header_type ctx)
              hty1);
        remove_false_branches hty2 ctx header_table
      ) else
        let%bind hty2_is_nothing =
          is_semantically_nothing header_table ctx hty2
        in
        if hty2_is_nothing then (
          Log.debug (fun m ->
              m
                "@[<v>Header type@ %a@ is equivalent to nothing. It will be removed from choice.@]"
                (Pretty.pp_header_type ctx)
                hty2);
          remove_false_branches hty1 ctx header_table
        ) else (
          Log.debug (fun m ->
              m
                "Both choices are not equal to nothing, will return a choice type.");
          let%bind hty1' = remove_false_branches hty1 ctx header_table in
          let%map hty2' = remove_false_branches hty2 ctx header_table in
          Choice (hty1', hty2')
        )
    | Refinement
        ( _,
          Refinement
            (y, hty, Eq (ArithExpr (Length (0, PktIn)), ArithExpr (Num 0))),
          Eq (ArithExpr (Length (0, PktIn)), ArithExpr (Num 0)) ) ->
      let%map hty' = remove_false_branches hty ctx header_table in
      Refinement (y, hty', Eq (ArithExpr (Length (0, PktIn)), ArithExpr (Num 0)))
    | Refinement (x, hty, e) ->
      let%map hty' = remove_false_branches hty ctx header_table in
      Refinement (x, hty', Simplify.simplify_form e)
    | Substitution (hty1, x, hty2) ->
      let ctx' = Env.add_binding ctx x (Env.VarBind hty2) in
      let%bind hty1' = remove_false_branches hty1 ctx' header_table in
      let%map hty2' = remove_false_branches hty2 ctx header_table in
      Substitution (hty1', x, hty2')

  and is_semantically_nothing header_table ctx hty =
    Log.debug (fun m ->
        m
          "Simplify header type@ %a@ Checking if type is a subtype of nothing..."
          Pretty.pp_header_type_raw hty);
    Log.debug (fun m -> m "@[<v>Context:@ %a@]" Pretty.pp_context ctx);
    P.check_subtype hty Nothing ctx header_table

  let rec chomp_rec (hty : HeapType.t) (ctx : Env.context) (n : int)
      (binder : int) (inst : Instance.t) (b0 : int)
      (header_table : HeaderTable.t) =
    if n = 0 then
      return hty
    else
      let hty' = heap_ref1 (chomp1 hty ctx b0) b0 binder inst n in
      let%bind simplified = remove_false_branches hty' ctx header_table in
      Log.debug (fun m ->
          m "@[<v>Chomped Header type before simplification:@ %a@]"
            Pretty.pp_header_type_raw hty');
      Log.debug (fun m ->
          m "@[<v>Chomped Header type after simplification:@ %a@]"
            Pretty.pp_header_type_raw simplified);
      Log.debug (fun m ->
          m "@[<v>Context for chomped header type:@ %a@]" Pretty.pp_context ctx);
      chomp_rec simplified ctx (n - 1) binder inst (b0 + 1) header_table

  let chomp (hty : HeapType.t) (ctx : Env.context) (inst : Instance.t)
      (header_table : HeaderTable.t) =
    chomp_rec hty ctx (Instance.sizeof inst) 0 inst 0 header_table
end
