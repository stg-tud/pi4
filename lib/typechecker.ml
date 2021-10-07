open Core_kernel
open Result
open Let_syntax
open Syntax
open Expression
open HeapType
open Term

module Log = (val Logs.src_log Logging.typechecker_src : Logs.LOG)

module TypecheckingResult = struct
  type t =
    | TypeError of string
    | Success
  [@@deriving compare, sexp]

  let is_error = function
    | TypeError _ -> true
    | Success -> false

  let pp (pp : Format.formatter) (result : t) =
    match result with
    | Success -> Fmt.pf pp "Success"
    | TypeError e -> Fmt.pf pp "TypeError: %s" e
end

let incr_binder x cutoff n =
  if x >= cutoff then
    x + n
  else
    x

let shift_sliceable (sliceable : Sliceable.t) cutoff n =
  match sliceable with
  | Packet (x, pkt) ->
    let x' = incr_binder x cutoff n in
    Sliceable.Packet (x', pkt)
  | Instance (x, inst) ->
    let x' = incr_binder x cutoff n in
    Sliceable.Instance (x', inst)

let rec shift_term (term : Term.t) cutoff n =
  let open Term in
  match term with
  | Num n -> Num n
  | Length (x, pkt) ->
    let x' = incr_binder x cutoff n in
    Length (x', pkt)
  | Plus (tm1, tm2) -> Plus (shift_term tm1 cutoff n, shift_term tm2 cutoff n)
  | Minus (tm1, tm2) ->
    Minus (shift_term tm1 cutoff n, shift_term tm2 cutoff n)
  | Bv _ as bv -> bv
  | Concat (tm1, tm2) ->
    Concat (shift_term tm1 cutoff n, shift_term tm2 cutoff n)
  | Slice (s, l, r) -> Slice (shift_sliceable s cutoff n, l, r)
  | Packet (x, pkt) ->
    let x' = incr_binder x cutoff n in
    Packet (x', pkt)

let rec shift_expr (expr : Expression.t) (cutoff : int) (n : int) =
  match expr with
  | True -> True
  | False -> False
  | IsValid (x, inst) ->
    let x' = incr_binder x cutoff n in
    IsValid (x', inst)
  | TmEq (tm1, tm2) -> TmEq (shift_term tm1 cutoff n, shift_term tm2 cutoff n)
  | TmGt (tm1, tm2) -> TmGt (shift_term tm1 cutoff n, shift_term tm2 cutoff n)
  | Neg e -> Neg (shift_expr e cutoff n)
  | And (e1, e2) -> And (shift_expr e1 cutoff n, shift_expr e2 cutoff n)
  | Or (e1, e2) -> Or (shift_expr e1 cutoff n, shift_expr e2 cutoff n)
  | Implies (e1, e2) -> Implies (shift_expr e1 cutoff n, shift_expr e2 cutoff n)

(* Shift all free variables with binder >= cutoff by n *)
let rec shift_header_type (hty : HeapType.t) (cutoff : int) (n : int) =
  let open HeapType in
  match hty with
  | Nothing -> Nothing
  | Empty -> Empty
  | Top -> Top
  | Choice (hty1, hty2) ->
    Choice (shift_header_type hty1 cutoff n, shift_header_type hty2 cutoff n)
  | Sigma (x, hty1, hty2) ->
    Sigma
      (x, shift_header_type hty1 cutoff n, shift_header_type hty2 (cutoff + 1) n)
  | Refinement (x, hty, e) ->
    Refinement (x, shift_header_type hty cutoff n, shift_expr e (cutoff + 1) n)
  | Substitution (hty1, x, hty2) ->
    Substitution
      (shift_header_type hty1 (cutoff + 1) n, x, shift_header_type hty2 cutoff n)

let tybv_concat (ty1 : ty) (ty2 : ty) =
  match (ty1, ty2) with
  | BitVec (StaticSize n), BitVec (StaticSize m) ->
    Ok (BitVec (StaticSize (n + m)))
  | BitVec MaxLen, BitVec _
  | BitVec _, BitVec MaxLen ->
    Ok (BitVec MaxLen)
  | _ -> Error "Arguments to '@' must be of type BitVec"

let eq_size = [%compare.equal: size]

let rec typeof_tm (term : Term.t) =
  match term with
  | Num _ -> Ok Nat
  | Length (_, _) -> Ok Nat
  | Plus (n, m) -> (
    let%bind tyn = typeof_tm n
    and tym = typeof_tm m in
    match (tyn, tym) with
    | Nat, Nat -> Ok Nat
    | _ -> Error "Arguments to '+' must be of type Nat")
  | Minus (tm1, tm2) -> (
    let%bind tytm1 = typeof_tm tm1
    and tytm2 = typeof_tm tm2 in
    match (tytm1, tytm2) with
    | BitVec s1, BitVec s2 ->
      if eq_size s1 s2 then
        Ok (BitVec s1)
      else
        Error "Arguments to '-' must have the same type"
    | _ -> Error "Arguments to '-' must be of type BitVec")
  | Bv Nil -> Ok (BitVec (StaticSize 0))
  | Bv bv -> Ok (BitVec (StaticSize (BitVector.sizeof bv)))
  | Concat (tm1, tm2) ->
    let%bind tybv1 = typeof_tm tm1
    and tybv2 = typeof_tm tm2 in
    tybv_concat tybv1 tybv2
  | Slice (_, l, r) -> Ok (BitVec (StaticSize (r - l)))
  | Packet (_, _) -> Ok (BitVec MaxLen)

let rec typeof_exp (expr : Expression.t) =
  match expr with
  | True -> return Bool
  | False -> return Bool
  | IsValid (_, _) -> return Bool
  | TmEq (tm1, tm2) ->
    let%bind tytm1 = typeof_tm tm1
    and tytm2 = typeof_tm tm2 in
    if [%compare.equal: ty] tytm1 tytm2 then
      return Bool
    else
      Error
        (Fmt.str "@[The terms must have the same type (%a/%a)@]"
           (Pretty.pp_type []) tytm1 (Pretty.pp_type []) tytm2)
  | TmGt (tm1, tm2) -> (
    let%bind tytm1 = typeof_tm tm1
    and tytm2 = typeof_tm tm2 in
    match (tytm1, tytm2) with
    | Nat, Nat -> return Bool
    | BitVec _, BitVec _ -> return Bool
    | _ -> Error "The terms must have the same type")
  | Neg e -> typeof_exp e
  | And (e1, e2)
  | Or (e1, e2)
  | Implies (e1, e2) ->
    let%map _ = typeof_exp e1
    and _ = typeof_exp e2 in
    Bool

let refresh_binder (x : string) (ctx : Env.context) =
  let x', _ = String.lsplit2 x ~on:'\'' |> Option.value ~default:(x, "") in
  Env.pick_fresh_name ctx x'

let rec refresh_binders (hty : HeapType.t) (ctx : Env.context) =
  match hty with
  | Nothing -> Nothing
  | Empty -> Empty
  | Top -> Top
  | Sigma (x, hty1, hty2) ->
    let x' = refresh_binder x ctx in
    let ctx' = Env.add_binding ctx x' (Env.VarBind hty1) in
    Sigma (x', refresh_binders hty1 ctx, refresh_binders hty2 ctx')
  | Choice (hty1, hty2) ->
    Choice (refresh_binders hty1 ctx, refresh_binders hty2 ctx)
  | Refinement (x, hty, e) ->
    let x' = refresh_binder x ctx in
    let ctx' = Env.add_binding ctx x' (Env.VarBind hty) in
    Refinement (x', refresh_binders hty ctx', e)
  | Substitution (hty1, x, hty2) ->
    let x' = refresh_binder x ctx in
    let ctx' = Env.add_binding ctx x' (Env.VarBind hty2) in
    Substitution (refresh_binders hty1 ctx', x', refresh_binders hty2 ctx)

module type S = sig
  val check_type : command -> ty -> HeaderTable.t -> TypecheckingResult.t
end

module type Checker = sig
  val compute_type :
    command ->
    string * HeapType.t ->
    Env.context ->
    HeaderTable.t ->
    (HeapType.t, string) result

  val check_subtype :
    HeapType.t ->
    HeapType.t ->
    Env.context ->
    HeaderTable.t ->
    (bool, string) result
end

module HeapTypeOps (P : Prover.S) = struct
  let includes (hty : HeapType.t) (inst : Instance.t)
      (header_table : HeaderTable.t) (ctx : Env.context) =
    Log.debug (fun m ->
        m "@[<v>Checking if instance '%s' is included in type@ %a@]"
          Instance.(inst.name)
          (Pretty.pp_header_type ctx)
          hty);
    let x = Env.pick_fresh_name ctx "x" in
    let refined = HeapType.Refinement (x, hty, IsValid (0, inst)) in
    P.check_subtype hty refined ctx header_table
end

module type Chomp = sig
  include Checker

  val chomp1 : HeapType.t -> Env.context -> int -> HeapType.t

  val chomp_e1 : Expression.t -> Syntax.var -> int -> Expression.t

  val chomp_ref1 : HeapType.t -> var -> int -> HeapType.t

  val chomp_t1 : Term.t -> Syntax.var -> int -> Term.t

  val heap_tref1 : Term.t -> int -> var -> Instance.t -> int -> Term.t
end

module CompleteChecker (C : Encoding.Config) : Chomp = struct
  module P = Prover.Make (Encoding.FixedWidthBitvectorEncoding (C))
  include HeapTypeOps (P)

  let rec chomp_t1 (tm : Term.t) (bind : Syntax.var) (b0 : int) =
    match tm with
    | Length (b, pkt) as l ->
      if bind = b && [%compare.equal: packet] pkt PktIn then
        Plus (l, Num 1)
      else
        l
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
    | Plus (t1, t2) -> Plus (chomp_t1 t1 bind b0, chomp_t1 t2 bind b0)
    | Minus (t1, t2) ->
      Minus (chomp_t1 t1 bind b0, chomp_t1 t2 bind b0)
      (* TODO: Check if this is correct.*)
    | Concat (t1, t2) -> Concat (chomp_t1 t1 bind b0, chomp_t1 t2 bind b0)
    | ( Slice (Packet (_, PktOut), _, _)
      | Slice (Instance (_, _), _, _)
      | Num _ | Bv _ ) as t ->
      t

  let rec chomp_e1 (expr : Expression.t) (binder : var) (b0 : int) =
    match expr with
    | TmEq (t1, t2) -> TmEq (chomp_t1 t1 binder b0, chomp_t1 t2 binder b0)
    | TmGt (t1, t2) -> TmGt (chomp_t1 t1 binder b0, chomp_t1 t2 binder b0)
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
    | (Nothing | Empty | Top) as hty' -> hty'

  let rec chomp1 (hty : HeapType.t) ctx b0 =
    match hty with
    | Sigma (x, hty1, hty2) ->
      let left = Sigma (x, chomp1 hty1 ctx b0, chomp_ref1 hty2 0 b0) in
      let ctx' = Env.add_binding ctx x (Env.VarBind hty1) in
      let right =
        let ref = TmEq (Length (0, PktIn), Num 0) in
        let y = Env.pick_fresh_name ctx' x in
        Sigma (x, Refinement (y, hty1, ref), chomp1 hty2 ctx' b0)
      in
      Choice (left, right)
    | Choice (hty1, hty2) -> Choice (chomp1 hty1 ctx b0, chomp1 hty2 ctx b0)
    | Refinement (x, hty, e) ->
      Refinement (x, chomp1 hty ctx b0, chomp_e1 e 0 b0)
    | Substitution (hty1, x, hty2) ->
      let ctx' = Env.add_binding ctx x (Env.VarBind hty2) in
      let hty1' = chomp1 hty1 ctx' b0 in
      Substitution (hty1', x, hty2)
    | (Nothing | Empty | Top) as hty' -> hty'

  let rec heap_tref1 (t : Term.t) b0 binder inst n =
    match t with
    | Bv (Cons (B b1, bv)) when b0 = b1 ->
      let result =
        Concat
          ( Slice
              ( Instance (binder, inst),
                Instance.sizeof inst - n,
                Instance.sizeof inst - n + 1 ),
            heap_tref1 (Bv bv) b0 binder inst n )
      in
      Simplify.simplify_term result
    | Bv (Cons (b, bv)) ->
      let result =
        Concat (Bv (Cons (b, Nil)), heap_tref1 (Bv bv) b0 binder inst n)
      in
      Simplify.simplify_term result
    | Concat (t1, t2) ->
      let t1' = heap_tref1 t1 b0 binder inst n |> Simplify.simplify_term in
      let t2' = heap_tref1 t2 b0 binder inst n |> Simplify.simplify_term in
      Concat (t1', t2')
    | Minus (t1, t2) ->
      let t1' = heap_tref1 t1 b0 binder inst n |> Simplify.simplify_term in
      let t2' = heap_tref1 t2 b0 binder inst n |> Simplify.simplify_term in
      Minus (t1', t2')
      (* TODO: Check if this is correct.*)
    | ( Bv Nil
      | Num _
      | Length (_, _)
      | Plus (_, _)
      | Slice (_, _, _)
      | Packet (_, _) ) as t ->
      t

  let rec heap_eref1 (expr : Expression.t) b0 binder inst n =
    match expr with
    | TmEq (tm1, tm2) ->
      let tm1' = heap_tref1 tm1 b0 binder inst n |> Simplify.simplify_term in
      let tm2' = heap_tref1 tm2 b0 binder inst n |> Simplify.simplify_term in
      TmEq (tm1', tm2')
    | TmGt (tm1, tm2) ->
      let tm1' = heap_tref1 tm1 b0 binder inst n |> Simplify.simplify_term in
      let tm2' = heap_tref1 tm2 b0 binder inst n |> Simplify.simplify_term in
      TmGt (tm1', tm2')
    | Neg e' -> Neg (heap_eref1 e' b0 binder inst n)
    | And (e1, e2) ->
      And (heap_eref1 e1 b0 binder inst n, heap_eref1 e2 b0 binder inst n)
    | Or (e1, e2) ->
      Or (heap_eref1 e1 b0 binder inst n, heap_eref1 e2 b0 binder inst n)
    | Implies (e1, e2) ->
      Implies (heap_eref1 e1 b0 binder inst n, heap_eref1 e2 b0 binder inst n)
    | (True | False | IsValid (_, _)) as e -> e

  and heap_ref1 (hty : HeapType.t) (b0 : int) (binder : int) (inst : Instance.t)
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
    | (Nothing | Empty | Top) as hty' -> hty'

  let rec remove_false_branches (header_type : HeapType.t) (ctx : Env.context)
      (header_table : HeaderTable.t) =
    match header_type with
    | Nothing -> return Nothing
    | Empty -> return Empty
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
          Refinement (y, hty, TmEq (Length (0, PktIn), Num 0)),
          TmEq (Length (0, PktIn), Num 0) ) ->
      let%map hty' = remove_false_branches hty ctx header_table in
      Refinement (y, hty', TmEq (Length (0, PktIn), Num 0))
    | Refinement (x, hty, e) ->
      let%map hty' = remove_false_branches hty ctx header_table in
      Refinement (x, hty', Simplify.simplify_expr e)
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
    Log.debug (fun m ->
        m "@[<v>Chomping header type:@ %a@]" Pretty.pp_header_type_raw hty);
    Log.debug (fun m ->
        m "@[<v>Context used for chomping:@ %a@]" Pretty.pp_context ctx);
    chomp_rec hty ctx (Instance.sizeof inst) 0 inst 0 header_table

  let rec compute_type (cmd : command)
      ((hty_var, hty_arg) : string * HeapType.t) (ctx : Env.context)
      (header_table : HeaderTable.t) =
    let open HeapType in
    match cmd with
    | Add inst ->
      Log.debug (fun m -> m "@[<v>Typechecking add(%s)...@]" inst.name);
      let y = Env.pick_fresh_name ctx "y" in
      let v = Env.pick_fresh_name ctx "v" in
      let%map hty_out =
        let w = Env.pick_fresh_name ctx "w" in
        let hty_inst =
          Refinement
            ( v,
              HeapType.instance inst header_table w,
              And
                ( TmEq (Length (0, PktIn), Num 0),
                  TmEq (Length (0, PktOut), Num 0) ) )
        in
        let z = Env.pick_fresh_name ctx "z" in
        let hty_in =
          Refinement
            ( z,
              shift_header_type hty_arg 0 1,
              Syntax.heap_equality 0 1 header_table )
        in
        return (Sigma (y, hty_in, hty_inst))
      in
      Simplify.fold_refinements hty_out
    | Ascription (cmd, x, ascb_hty_in, ascb_hty_out) ->
      Log.debug (fun m ->
          m "@[<v>Typechecking %a@ as@ (%s:%a) -> %a...@]" Pretty.pp_command cmd
            x (Pretty.pp_header_type []) ascb_hty_in
            (Pretty.pp_header_type [ (x, Env.VarBind ascb_hty_in) ])
            ascb_hty_out);
      Log.debug (fun m ->
          m "Checking if input type is a subtype of the ascribed input type...");

      Log.debug (fun m ->
          m "Ascribed input type: %a" Pretty.pp_header_type_raw ascb_hty_in);
      Log.debug (fun m -> m "Input type: %a" Pretty.pp_header_type_raw hty_arg);
      Log.debug (fun m ->
          m "Context used for input type: %a" Pretty.pp_context ctx);

      let%bind input_is_subtype =
        P.check_subtype hty_arg ascb_hty_in ctx header_table
      in
      if input_is_subtype then (
        let%bind chty_out =
          compute_type cmd (x, ascb_hty_in) ctx header_table
        in
        Log.debug (fun m ->
            m
              "Checking if computed output type is a subtype of the ascribed output type...");
        let%bind output_is_subtype =
          P.check_subtype chty_out ascb_hty_out
            [ (x, Env.VarBind ascb_hty_in) ]
            header_table
        in
        if output_is_subtype then
          return ascb_hty_out
        else
          Error
            "The computed output type must be a subtype of the ascribed output type"
      ) else
        Error
          "The argument input type must be a subtype of the ascribed input type"
    | Extract inst ->
      Log.debug (fun m -> m "@[<v>Typechecking extract(%s)...@]" inst.name);
      Log.debug (fun m ->
          m "@[<v>Input type:@ %a@]" Pretty.pp_header_type_raw hty_arg);
      Log.debug (fun m -> m "@[<v>Input context:@ %a@]" Pretty.pp_context ctx);
      Log.debug (fun m ->
          m
            "@[<v>Checking if pkt_in of@ %a@ provides enough bits in context@ %a...@]"
            Pretty.pp_header_type_raw
            (refresh_binders hty_arg ctx)
            Pretty.pp_context ctx);
      let x = Env.pick_fresh_name ctx "x" in
      let refined_pkt_length =
        Refinement
          (x, hty_arg, TmGt (Length (0, PktIn), Num (Instance.sizeof inst - 1)))
      in
      let%bind has_enough_bits =
        P.check_subtype hty_arg refined_pkt_length ctx header_table
      in
      if has_enough_bits then (
        let y = Env.pick_fresh_name ctx "y" in
        let z = Env.pick_fresh_name ctx "z" in
        let phi =
          And (TmEq (Length (0, PktIn), Num 0), TmEq (Length (0, PktOut), Num 0))
        in
        let var_inst = Env.pick_fresh_name ctx "v" in
        let hty_inst = HeapType.instance inst header_table var_inst in
        let tyinst = Refinement (z, hty_inst, phi) in
        Log.debug (fun m ->
            m "Input type before chomping:@ %a" Pretty.pp_header_type_raw
              hty_arg);

        let%bind ctx_chomp = return ((y, Env.VarBind tyinst) :: ctx) in

        let%bind chomped =
          chomp (shift_header_type hty_arg 0 1) ctx_chomp inst header_table
        in
        Log.debug (fun m ->
            m "Raw input type after chomping:@ %a" Pretty.pp_header_type_raw
              chomped);
        Log.debug (fun m ->
            m "Input type after chomping:@ %a"
              (Pretty.pp_header_type ctx_chomp)
              chomped);
        Log.debug (fun m -> m "Chomp context:@ %a" Pretty.pp_context ctx_chomp);

        let chomped = shift_header_type chomped 1 1 in

        (* Check that all instances except inst are equal *)
        let insts_equal =
          HeaderTable.to_list header_table |> Syntax.inst_equality 2 0
        in
        (* Check that pkt_out is equal *)
        let pkt_out_equal = Syntax.packet_equality PktOut 2 0 in
        (* Check that inst[0:sizeof(inst)]@(result of chomp).pkt_in =
           x.pkt_in *)
        let pkt_in_equal =
          And
            ( TmEq
                ( Concat
                    ( Slice (Instance (1, inst), 0, Instance.sizeof inst),
                      Packet (0, PktIn) ),
                  Packet (2, PktIn) ),
              TmEq
                ( Plus (Length (0, PktIn), Num (Instance.sizeof inst)),
                  Length (2, PktIn) ) )
        in
        let u = Env.pick_fresh_name ctx "u" in
        let chomped_eq =
          Refinement
            (u, chomped, And (insts_equal, And (pkt_out_equal, pkt_in_equal)))
        in
        return (Sigma (y, tyinst, chomped_eq))
      ) else
        Error
          (Printf.sprintf
             "Tried to chomp off %d bits, but 'pkt_in' does not provide enough bits."
             (Instance.sizeof inst))
    | If (e, c1, c2) -> (
      Log.debug (fun m ->
          m "@[<v>Typechecking@ @[<v 2>if(%a) {@ %a } else {@ %a @ }...@]@]"
            (Pretty.pp_expr [ ("_", NameBind) ])
            e Pretty.pp_command c1 Pretty.pp_command c2);
      Log.debug (fun m ->
          m "@[<v>Input type:@ %a@]" (Pretty.pp_header_type ctx) hty_arg);
      Log.debug (fun m -> m "@[<v>Input context:@ %a@]" Pretty.pp_context ctx);
      let%bind tye = typeof_exp e in
      match tye with
      | Bool ->
        let x = Env.pick_fresh_name ctx "x" in
        let y = Env.pick_fresh_name ctx "y" in
        Log.debug (fun m -> m "@[<v>Typechecking 'then' branch...@]");
        let hty_in_then =
          Simplify.fold_refinements (Refinement (x, hty_arg, e))
        in
        let%bind tyc1 =
          compute_type c1 (hty_var, hty_in_then) ctx header_table
        in
        Log.debug (fun m -> m "@[<v>Typechecking 'else' branch...@]");
        let%bind tyc2 =
          compute_type c2
            (hty_var, Refinement (y, hty_arg, Neg e))
            ctx header_table
        in
        return (Choice (tyc1, tyc2))
      | _ -> Error "Expression must be of type Bool")
    | Assign (inst, left, right, tm) ->
      Log.debug (fun m ->
          m "@[<v>Typechecking %s.[%d:%d]:=%a...@]" inst.name left right
            (Pretty.pp_term ctx) tm);
      Log.debug (fun m ->
          m "@[<v>Input type:@ %a@]" (Pretty.pp_header_type ctx) hty_arg);
      Log.debug (fun m -> m "@[<v>Input context:@ %a@]" Pretty.pp_context ctx);
      let parts = List.rev (String.split ~on:'_' inst.name) in
      let%bind version =
        List.hd parts
        |> Option.map ~f:(fun v -> int_of_string v)
        |> Result.of_option ~error:"Can't extract instance version"
      in
      let%bind inst_name =
        List.tl parts
        |> Option.map ~f:(fun l -> String.concat ~sep:"_" (List.rev l))
        |> Result.of_option ~error:"Can't extract instance name"
      in
      if version = 0 then
        Error "Instance must be valid to be modified"
      else (
        Log.debug (fun m -> m "Inst: %a" Pretty.pp_instance inst);
        (* if not (Instance.slice_matches_field inst left right) then Error
           (Printf.sprintf "Invalid slice [%d:%d] on instance %s" left right
           inst.name) else *)
        let prev_inst_name = Ssa.append_version inst_name (version - 1) in
        let%bind prev_inst = HeaderTable.lookup_instance prev_inst_name header_table in
        Log.debug (fun m -> m "Prev Inst: %a" Pretty.pp_instance prev_inst);
        Log.debug (fun m ->
            m
              "@[<v>Checking if instance %s is included in
             type@ %a...@]"
              prev_inst.name
              (Pretty.pp_header_type ctx)
              hty_arg);
        let%bind incl = includes hty_arg prev_inst header_table ctx in
        if not incl then
          Error
            (Printf.sprintf "Instance '%s' not included in header type."
               inst.name)
        else
          let inst_size = Instance.sizeof inst in

          (* let%bind slice = Term.field_to_slice inst f 0 in *)

          (* Ensure that all instances != inst are equal *)
          let insts_equal =
            HeaderTable.to_list header_table
            |> List.filter ~f:(fun i ->
                   not ([%compare.equal: Instance.t] inst i))
            |> Syntax.inst_equality 1 0
          in
          (* For instance inst, ensure that all bits except for the assigned
             ones are equal *)
          let fields_equal =
            if left > 0 then
              TmEq
                ( Term.Slice (Instance (0, inst), 0, left),
                  Term.Slice (Instance (1, inst), 0, left) )
            else
              insts_equal
          in
          let fields_equal =
            if inst_size - right > 0 then
              let eq_right =
                TmEq
                  ( Term.Slice (Instance (0, inst), right, inst_size),
                    Term.Slice (Instance (1, inst), right, inst_size) )
              in
              And (fields_equal, eq_right)
            else
              fields_equal
          in

          let y = Env.pick_fresh_name ctx "y" in

          return
            (Refinement
               ( y,
                 shift_header_type hty_arg 0 1,
                 And
                   ( TmEq (Term.Slice (Instance (0, inst), left, right), tm),
                     And
                       ( fields_equal,
                         (* Ensure that pkt_in/pkt_out are equal *)
                         And
                           ( Syntax.packet_equality PktIn 1 0,
                             Syntax.packet_equality PktOut 1 0 ) ) ) ))
      )
    | Reset ->
      Log.debug (fun m -> m "@[<v>Typechecking reset...@]");
      let y = Env.pick_fresh_name ctx "y" in
      let z = Env.pick_fresh_name ctx "z" in
      let w = Env.pick_fresh_name ctx "w" in
      let empty = HeapType.empty header_table w in
      let lhs =
        Refinement
          ( y,
            empty,
            And
              ( TmEq (Length (0, PktOut), Num 0),
                And
                  ( TmEq (Packet (0, PktIn), Packet (1, PktOut)),
                    TmEq (Length (0, PktIn), Length (1, PktOut)) ) ) )
      in
      let rhs =
        Refinement
          ( y,
            empty,
            And
              ( TmEq (Length (0, PktOut), Num 0),
                And
                  ( TmEq (Packet (0, PktIn), Packet (2, PktIn)),
                    TmEq (Length (0, PktIn), Length (2, PktIn)) ) ) )
      in
      let concat = Sigma (z, lhs, rhs) in
      return concat
    | Remit inst ->
      Log.debug (fun m -> m "@[<v>Typechecking remit(%s)...@]" inst.name);
      let%bind incl = includes hty_arg inst header_table ctx in
      if not incl then
        Error
          (Printf.sprintf "Instance '%s' not included in header type" inst.name)
      else
        let x = Env.pick_fresh_name ctx "x" in
        let y = Env.pick_fresh_name ctx "y" in
        let var_empty = Env.pick_fresh_name ctx "w" in
        let empty = HeapType.empty header_table var_empty in
        let inst_size = Instance.sizeof inst in
        let ref =
          And
            ( And
                ( TmEq (Length (0, PktIn), Num 0),
                  TmEq (Length (0, PktOut), Num inst_size) ),
              TmEq
                ( Slice (Packet (0, PktOut), 0, inst_size),
                  Slice (Instance (2, inst), 0, inst_size) ) )
        in
        let u = Env.pick_fresh_name ctx "u" in
        let hty_in_eq =
          Refinement
            ( u,
              shift_header_type hty_arg 0 1,
              Syntax.heap_equality 1 0 header_table )
        in
        let sigma = Sigma (x, hty_in_eq, Refinement (y, empty, ref)) in
        return sigma
    | Seq (c1, c2) ->
      Log.debug (fun m ->
          m "@[<v>Typechecking sequence:@ c1:@[<v>@ %a @]@ c2:@[<v>@ %a@]@]"
            Pretty.pp_command c1 Pretty.pp_command c2);
      Log.debug (fun m ->
          m "@[<v>Input type:@ %a@]" (Pretty.pp_header_type ctx) hty_arg);
      Log.debug (fun m -> m "@[<v>Input context:@ %a@]" Pretty.pp_context ctx);
      let%bind tyc1 = compute_type c1 (hty_var, hty_arg) ctx header_table in

      let ctx' =
        if Types.contains_free_vars tyc1 then
          match c1 with
          | Ascription (_, x, ascb_hty_in, _) ->
            Env.add_binding ctx x (Env.VarBind ascb_hty_in)
          | _ -> Env.add_binding ctx hty_var (Env.VarBind hty_arg)
        else
          ctx
      in
      Log.debug (fun m ->
          m "@[<v>Computed output type for c1 = %a:@ %a@]" Pretty.pp_command c1
            (Pretty.pp_header_type ctx')
            tyc1);
      Log.debug (fun m ->
          m "@[<v>Context used for output type of c1:@ %a@]" Pretty.pp_context
            ctx');
      let y = Env.pick_fresh_name ctx' "y" in
      let%bind tyc2 = compute_type c2 (y, tyc1) ctx' header_table in
      let ctx'' =
        match c2 with
        | Ascription (_, var, ascb_hty_in, _) ->
          Env.add_binding ctx' var (Env.VarBind ascb_hty_in)
        | _ -> Env.add_binding ctx' y (Env.VarBind tyc1)
      in
      Log.debug (fun m ->
          m "@[<v>Computed output type for c2 = %a:@ %a@]" Pretty.pp_command c2
            (Pretty.pp_header_type ctx'')
            tyc2);
      Log.debug (fun m ->
          m "@[<v>Context used for output type of c2:@ %a" Pretty.pp_context
            ctx'');

      let hty_subst = Substitution (tyc2, y, tyc1) in
      Log.debug (fun m ->
          m "Resulting substitution type:@ %a"
            (Pretty.pp_header_type ctx')
            hty_subst);
      Log.debug (fun m ->
          m "Context for substitution type:@ %a" Pretty.pp_context ctx');
      return hty_subst
    | Skip ->
      Log.debug (fun m -> m "@[<v>Typechecking skip...@]");
      let y = Env.pick_fresh_name ctx "y" in
      return
        (Refinement
           ( y,
             shift_header_type hty_arg 0 1,
             Syntax.heap_equality 1 0 header_table ))

  let check_subtype = P.check_subtype
end

module SimpleChecker : Checker = struct
  module P = Prover.Make (Encoding.SimpleEncoding)
  include HeapTypeOps (P)

  let rec compute_type (cmd : command)
      ((hty_var, hty_arg) : string * HeapType.t) (ctx : Env.context)
      (header_table : HeaderTable.t) =
    let open HeapType in
    match cmd with
    | Add inst ->
      Log.debug (fun m -> m "@[<v>Typechecking add(%s)...@]" inst.name);
      let y = Env.pick_fresh_name ctx "y" in
      let v = Env.pick_fresh_name ctx "v" in
      let%map hty_out =
        let hty_inst = HeapType.instance inst header_table v in
        let z = Env.pick_fresh_name ctx "z" in
        let hty_in =
          Refinement
            ( z,
              shift_header_type hty_arg 0 1,
              Syntax.inst_equality 1 0 (HeaderTable.to_list header_table) )
        in
        return (Sigma (y, hty_in, hty_inst))
      in
      hty_out
    | Ascription (cmd, x, ascb_hty_in, ascb_hty_out) ->
      Log.debug (fun m ->
          m "@[<v>Typechecking %a@ as@ %a -> %a...@]" Pretty.pp_command cmd
            (Pretty.pp_header_type []) ascb_hty_in
            (Pretty.pp_header_type [ (x, Env.VarBind ascb_hty_in) ])
            ascb_hty_out);
      let%bind input_is_subtype =
        P.check_subtype hty_arg ascb_hty_in ctx header_table
      in
      if input_is_subtype then
        let%bind chty_out =
          compute_type cmd (x, ascb_hty_in) ctx header_table
        in
        let%bind output_is_subtype =
          P.check_subtype chty_out ascb_hty_out
            [ (x, Env.VarBind ascb_hty_in) ]
            header_table
        in
        if output_is_subtype then
          return ascb_hty_out
        else
          Error
            "The computed output type must be a subtype of the ascribed output type"
      else
        Error
          "The argument input type must be a subtype of the ascribed input type"
    | Extract inst ->
      Log.debug (fun m -> m "@[<v>Typechecking extract(%s)...@]" inst.name);
      Log.debug (fun m ->
          m "@[<v>Input type:@ %a@]" Pretty.pp_header_type_raw hty_arg);
      Log.debug (fun m -> m "@[<v>Input context:@ %a@]" Pretty.pp_context ctx);

      let y = Env.pick_fresh_name ctx "y" in
      let z = Env.pick_fresh_name ctx "z" in

      let var_inst = Env.pick_fresh_name ctx "v" in
      let hty_inst = HeapType.instance inst header_table var_inst in

      (* Check that all instances except inst are equal *)
      let insts_equal =
        HeaderTable.to_list header_table |> Syntax.inst_equality 2 0
      in
      let hty_in_eq =
        Refinement (z, shift_header_type hty_arg 0 2, insts_equal)
      in
      return (Sigma (y, hty_inst, hty_in_eq))
    | If (e, c1, c2) -> (
      Log.debug (fun m ->
          m "@[<v>Typechecking@ @[<v 2>if(%a) {@ %a } else {@ %a @ }...@]@]"
            (Pretty.pp_expr [ ("_", NameBind) ])
            e Pretty.pp_command c1 Pretty.pp_command c2);
      Log.debug (fun m ->
          m "@[<v>Input type:@ %a@]" Pretty.pp_header_type_raw hty_arg);
      Log.debug (fun m -> m "@[<v>Input context:@ %a@]" Pretty.pp_context ctx);
      let%bind tye = typeof_exp e in
      match tye with
      | Bool ->
        let x = Env.pick_fresh_name ctx "x" in
        let y = Env.pick_fresh_name ctx "y" in
        Log.debug (fun m -> m "@[<v>Typechecking 'then' branch...@]");
        let%bind tyc1 =
          compute_type c1 (hty_var, Refinement (x, hty_arg, e)) ctx header_table
        in
        Log.debug (fun m -> m "@[<v>Typechecking 'else' branch...@]");
        let%bind tyc2 =
          compute_type c2
            (hty_var, Refinement (y, hty_arg, Neg e))
            ctx header_table
        in
        return (Choice (tyc1, tyc2))
      | _ -> Error "Expression must be of type Bool")
    | Assign (inst, left, right, tm) ->
      Log.debug (fun m ->
          m "@[<v>Typechecking %s.[%d:%d]:=%a...@]" inst.name left right
            (Pretty.pp_term ctx) tm);
      Log.debug (fun m ->
          m "@[<v>Input type:@ %a@]" Pretty.pp_header_type_raw hty_arg);
      Log.debug (fun m -> m "@[<v>Input context:@ %a@]" Pretty.pp_context ctx);
      let inst_name, version = String.lsplit2_exn ~on:'_' inst.name in
      let vnum = int_of_string version in
      if vnum = 0 then
        Error "Instance must be valid to be modified"
      else (
        Log.debug (fun m -> m "Inst: %a" Pretty.pp_instance inst);
        (* if not (Instance.slice_matches_field inst left right) then Error
           (Printf.sprintf "Invalid slice [%d:%d] on instance %s" left right
           inst.name) else *)
        let inst_prev = Ssa.append_version inst_name (vnum - 1) in
        let%bind _ = HeaderTable.lookup_instance inst_prev header_table in
        let incl = true in
        if not incl then
          Error
            (Printf.sprintf "Instance '%s' not included in header type."
               inst.name)
        else
          let inst_size = Instance.sizeof inst in

          (* Ensure that all instances != inst are equal *)
          let insts_equal =
            HeaderTable.to_list header_table
            |> List.filter ~f:(fun i ->
                   not ([%compare.equal: Instance.t] inst i))
            |> Syntax.inst_equality 1 0
          in
          let fields_equal =
            if left > 0 then
              TmEq
                ( Term.Slice (Instance (0, inst), 0, left),
                  Term.Slice (Instance (1, inst), 0, left) )
            else
              insts_equal
          in
          let fields_equal =
            if inst_size - right > 0 then
              let eq_right =
                TmEq
                  ( Term.Slice (Instance (0, inst), right, inst_size),
                    Term.Slice (Instance (1, inst), right, inst_size) )
              in
              And (fields_equal, eq_right)
            else
              fields_equal
          in
          let y = Env.pick_fresh_name ctx "y" in
          return
            (Refinement
               ( y,
                 shift_header_type hty_arg 0 1,
                 And
                   ( TmEq (Term.Slice (Instance (0, inst), left, right), tm),
                     fields_equal ) ))
      )
    | Reset ->
      Log.debug (fun m -> m "@[<v>Typechecking reset...@]");
      let y = Env.pick_fresh_name ctx "y" in
      return (HeapType.empty header_table y)
    | Remit inst ->
      Log.debug (fun m -> m "@[<v>Typechecking remit(%s)...@]" inst.name);
      let%bind incl = includes hty_arg inst header_table ctx in
      if not incl then
        Error
          (Printf.sprintf "Instance '%s' not included in header type" inst.name)
      else
        let x = Env.pick_fresh_name ctx "x" in
        return
          (Refinement
             ( x,
               shift_header_type hty_arg 0 1,
               Syntax.heap_equality 1 0 header_table ))
    | Seq (c1, c2) ->
      Log.debug (fun m ->
          m "@[<v>Typechecking sequence:@ c1:@[<v>@ %a @]@ c2:@[<v>@ %a@]@]"
            Pretty.pp_command c1 Pretty.pp_command c2);
      Log.debug (fun m ->
          m "@[<v>Input type:@ %a@]" Pretty.pp_header_type_raw hty_arg);
      Log.debug (fun m -> m "@[<v>Input context:@ %a@]" Pretty.pp_context ctx);
      let%bind tyc1 = compute_type c1 (hty_var, hty_arg) ctx header_table in

      let ctx' =
        if Types.contains_free_vars tyc1 then
          match c1 with
          | Ascription (_, x, ascb_hty_in, _) ->
            Env.add_binding ctx x (Env.VarBind ascb_hty_in)
          | _ -> Env.add_binding ctx hty_var (Env.VarBind hty_arg)
        else
          ctx
      in
      Log.debug (fun m ->
          m "@[<v>Raw computed output type for c1 = %a:@ %a@]" Pretty.pp_command
            c1 Pretty.pp_header_type_raw tyc1);
      Log.debug (fun m ->
          m "@[<v>Computed output type for c1 = %a:@ %a@]" Pretty.pp_command c1
            (Pretty.pp_header_type ctx')
            tyc1);
      Log.debug (fun m ->
          m "@[<v>Context used for output type of c1:@ %a@]" Pretty.pp_context
            ctx');
      let y = Env.pick_fresh_name ctx' "y" in
      let%bind tyc2 = compute_type c2 (y, tyc1) ctx' header_table in
      Log.debug (fun m ->
          m "@[<v>Raw computed output type for c2 = %a:@ %a@]" Pretty.pp_command
            c2 Pretty.pp_header_type_raw tyc2);
      Log.debug (fun m ->
          m "@[<v>Context used for output type of c2:@ %a" Pretty.pp_context
            ctx');

      let hty_subst = Substitution (tyc2, y, tyc1) in
      Log.debug (fun m ->
          m "Raw substitution type:@ %a" Pretty.pp_header_type_raw hty_subst);
      Log.debug (fun m ->
          m "Substitution type:@ %a" (Pretty.pp_header_type ctx') hty_subst);
      Log.debug (fun m ->
          m "Context for substitution type:@ %a" Pretty.pp_context ctx');
      return hty_subst
    | Skip ->
      Log.debug (fun m -> m "@[<v>Typechecking skip...@]");
      let y = Env.pick_fresh_name ctx "y" in
      return
        (Refinement
           ( y,
             shift_header_type hty_arg 0 1,
             Syntax.inst_equality 1 0 (HeaderTable.to_list header_table) ))

  let check_subtype = P.check_subtype
end

module Make (C : Checker) : S = struct
  let check_type (cmd : command) (ty : ty) (header_table : HeaderTable.t) =
    match ty with
    | Pi (x, annot_tyin, annot_tyout) -> (
      let result =
        let%bind { command = cmd_ssa;
                   header_table = ht_ssa;
                   input_type = annot_tyin_ssa;
                   output_type = annot_tyout_ssa
                 } =
          Ssa.to_ssa header_table cmd (x, annot_tyin) annot_tyout
        in
        Log.debug (fun m ->
            m "@[<v>Program in SSA form:@ %a@]@." Pretty.pp_command cmd_ssa);
        Log.debug (fun m ->
            m "@[<v>Input type in SSA form:@ %a@]@." (Pretty.pp_header_type [])
              annot_tyin_ssa);
        Log.debug (fun m ->
            m "@[<v>Output type in SSA form:@ %a@]@."
              (Pretty.pp_header_type [ (x, NameBind) ])
              annot_tyout_ssa);
        Log.debug (fun m ->
            m "@[<v>Header table in SSA form:@ %a@]@." Pretty.pp_header_table
              ht_ssa);
        let%bind tycout =
          C.compute_type cmd_ssa (x, annot_tyin_ssa) [] ht_ssa
        in
        let ctx = [ (x, Env.VarBind annot_tyin_ssa) ] in
        Log.debug (fun m ->
            m
              "@[<v>Type computed by type checker:@ (%s:@[<v>@ %a@]@ )@ →@ %a@ @]@."
              x (Pretty.pp_header_type []) annot_tyin_ssa
              (Pretty.pp_header_type ctx)
              (Simplify.fold_refinements tycout));
        let%bind res = C.check_subtype tycout annot_tyout_ssa ctx ht_ssa in
        if res then
          return res
        else
          Error
            "Expected the computed output header type to be a subtype of the annotated output header type"
      in
      match result with
      | Ok _ -> TypecheckingResult.Success
      | Error e -> TypecheckingResult.TypeError e)
    | _ -> TypecheckingResult.TypeError "Annotated type must be a Pi type"
end

module MakeSSAChecker (C : Checker) : S = struct
  let check_type (cmd : command) (ty : ty) (header_table : HeaderTable.t) =
    match ty with
    | Pi (x, annot_tyin, annot_tyout) -> (
      let result =
        let%bind tycout =
          C.compute_type cmd (x, annot_tyin) [] header_table
        in
        let ctx = [ (x, Env.VarBind annot_tyin) ] in
        Log.debug (fun m ->
            m
              "@[<v>Type computed by type checker:@ (%s:@[<v>@ %a@]@ )@ →@ %a@ @]@."
              x (Pretty.pp_header_type []) annot_tyin
              (Pretty.pp_header_type ctx)
              (Simplify.fold_refinements tycout));
        let%bind res = C.check_subtype tycout annot_tyout ctx header_table in
        if res then
          return res
        else
          Error
            "Expected the computed output header type to be a subtype of the annotated output header type"
      in
      match result with
      | Ok _ -> TypecheckingResult.Success
      | Error e -> TypecheckingResult.TypeError e)
    | _ -> TypecheckingResult.TypeError "Annotated type must be a Pi type"
end
