open Core
open Result
open Let_syntax
open Syntax
open Formula
open HeapType
open Expression
module Log = (val Logs.src_log Logging.typechecker_src : Logs.LOG)

module TypecheckingResult = struct
  type t =
    | TypeError of string
    | Success
  [@@deriving compare, sexp]

  let is_error = function TypeError _ -> true | Success -> false

  let pp (pp : Format.formatter) (result : t) =
    match result with
    | Success -> Fmt.pf pp "Success"
    | TypeError e -> Fmt.pf pp "TypeError: %s" e
end

let incr_binder x cutoff n = if x >= cutoff then x + n else x

let shift_sliceable (sliceable : Sliceable.t) cutoff n =
  match sliceable with
  | Packet (x, pkt) ->
    let x' = incr_binder x cutoff n in
    Sliceable.Packet (x', pkt)
  | Instance (x, inst) ->
    let x' = incr_binder x cutoff n in
    Sliceable.Instance (x', inst)

let rec shift_arith_expr (expr : Expression.arith) (cutoff : int) (n : int) =
  match expr with
  | Num n -> Num n
  | Length (x, pkt) ->
    let x' = incr_binder x cutoff n in
    Length (x', pkt)
  | Plus (tm1, tm2) ->
    Plus (shift_arith_expr tm1 cutoff n, shift_arith_expr tm2 cutoff n)

let rec shift_bv_expr (expr : Expression.bv) (cutoff : int) (n : int) =
  match expr with
  | Minus (tm1, tm2) ->
    Minus (shift_bv_expr tm1 cutoff n, shift_bv_expr tm2 cutoff n)
  | Bv _ as bv -> bv
  | Concat (tm1, tm2) ->
    Concat (shift_bv_expr tm1 cutoff n, shift_bv_expr tm2 cutoff n)
  | Slice (s, l, r) -> Slice (shift_sliceable s cutoff n, l, r)
  | Packet (x, pkt) ->
    let x' = incr_binder x cutoff n in
    Packet (x', pkt)

let shift_expr (expr : Expression.t) cutoff n =
  match expr with
  | ArithExpr e -> ArithExpr (shift_arith_expr e cutoff n)
  | BvExpr e -> BvExpr (shift_bv_expr e cutoff n)

let rec shift_form (form : Formula.t) (cutoff : int) (n : int) =
  match form with
  | True -> True
  | False -> False
  | IsValid (x, inst) ->
    let x' = incr_binder x cutoff n in
    IsValid (x', inst)
  | Eq (tm1, tm2) -> Eq (shift_expr tm1 cutoff n, shift_expr tm2 cutoff n)
  | Gt (tm1, tm2) -> Gt (shift_expr tm1 cutoff n, shift_expr tm2 cutoff n)
  | Neg e -> Neg (shift_form e cutoff n)
  | And (e1, e2) -> And (shift_form e1 cutoff n, shift_form e2 cutoff n)
  | Or (e1, e2) -> Or (shift_form e1 cutoff n, shift_form e2 cutoff n)
  | Implies (e1, e2) -> Implies (shift_form e1 cutoff n, shift_form e2 cutoff n)

(* Shift all free variables with binder >= cutoff by n *)
let rec shift_header_type (hty : HeapType.t) (cutoff : int) (n : int) =
  let open HeapType in
  match hty with
  | Nothing -> Nothing
  | Top -> Top
  | Choice (hty1, hty2) ->
    Choice (shift_header_type hty1 cutoff n, shift_header_type hty2 cutoff n)
  | Sigma (x, hty1, hty2) ->
    Sigma
      (x, shift_header_type hty1 cutoff n, shift_header_type hty2 (cutoff + 1) n)
  | Refinement (x, hty, e) ->
    Refinement (x, shift_header_type hty cutoff n, shift_form e (cutoff + 1) n)
  | Substitution (hty1, x, hty2) ->
    Substitution
      (shift_header_type hty1 (cutoff + 1) n, x, shift_header_type hty2 cutoff n)

let tybv_concat (ty1 : ty) (ty2 : ty) =
  match (ty1, ty2) with
  | BitVec (StaticSize n), BitVec (StaticSize m) ->
    Ok (BitVec (StaticSize (n + m)))
  | BitVec MaxLen, BitVec _ | BitVec _, BitVec MaxLen -> Ok (BitVec MaxLen)
  | _ -> Error (`TypeError "Arguments to '@' must be of type BitVec")

let eq_size = [%compare.equal: size]

let refresh_binder (x : string) (ctx : Env.context) =
  let x', _ = String.lsplit2 x ~on:'\'' |> Option.value ~default:(x, "") in
  Env.pick_fresh_name ctx x'

let rec refresh_binders (hty : HeapType.t) (ctx : Env.context) =
  match hty with
  | Nothing -> Nothing
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

let other_instances (header_table : HeaderTable.t) (inst : Instance.t) =
  HeaderTable.to_list header_table
  |> List.filter ~f:(fun i -> not ([%compare.equal: Instance.t] i inst))

module type S = sig
  val check_type :
    ?enable_includes_cache:bool ->
    Command.t ->
    pi_type ->
    HeaderTable.t ->
    TypecheckingResult.t
end

module type Checker = sig
  val init : unit -> unit

  val compute_type :
    Command.t ->
    string * HeapType.t ->
    Env.context ->
    HeaderTable.t ->
    ( HeapType.t,
      [> `TypeError of string
      | `EncodingError of string
      | `VariableLookupError of string
      ] )
    result

  val check_subtype :
    HeapType.t ->
    HeapType.t ->
    Env.context ->
    HeaderTable.t ->
    ( bool,
      [> `TypeError of string
      | `EncodingError of string
      | `VariableLookupError of string
      ] )
    result
end

module IncludesCache = struct
  let enabled = ref false
  let data = ref (Map.empty (module Instance))
  let clear = data := Map.empty (module Instance)

  let update inst valid =
    Log.debug (fun m ->
        m "Updated include_cache: %a %b" Pretty.pp_instance inst valid);
    data := Map.set !data ~key:inst ~data:valid

  let rec populate_from_form form is_neg =
    match form with
    | And (f_l, f_r) ->
      populate_from_form f_l is_neg;
      populate_from_form f_r is_neg
    | IsValid (_, i) -> update i (not is_neg)
    | Neg (IsValid (_, i)) -> update i is_neg
    | _ -> ()

  let rec invalidate lst =
    match lst with
    | [] -> ()
    | x :: xs ->
      update x false;
      invalidate xs

  let lookup inst = Map.find !data inst

  let merge c1 c2 =
    data :=
      Map.merge c1 c2 ~f:(fun ~key:_ merge_elem ->
          match merge_elem with
          | `Both (v1, v2) ->
            if v1 && v2 then Some true
            else if (not v1) && not v2 then Some false
            else None
          | `Left _ -> None
          | `Right _ -> None)
end

module HeapTypeOps (P : Prover.S) = struct
  module Cache = IncludesCache

  let includes (header_table : HeaderTable.t) (ctx : Env.context)
      (hty : HeapType.t) (inst : Instance.t) =
    let check_includes () =
      Log.debug (fun m ->
          m "@[<v>Checking if instance '%s' is included in type@ %a@]"
            Instance.(inst.name)
            (Pretty.pp_header_type ctx)
            hty);
      let x = Env.pick_fresh_name ctx "x" in
      let refined = HeapType.Refinement (x, Top, IsValid (0, inst)) in
      let result = P.check_subtype hty refined ctx header_table in
      Result.iter result ~f:(fun does_incl ->
          Cache.data := Map.set !Cache.data ~key:inst ~data:does_incl);
      result
    in
    if !Cache.enabled then (
      match Cache.lookup inst with
      | Some result ->
        Log.debug (fun m -> m "@[INSTANCE CACHE: HIT (%s)@]" inst.name);
        return result
      | None ->
        Log.debug (fun m -> m "@[INSTANCE CACHE: MISS (%s)@]" inst.name);
        check_includes ())
    else check_includes ()

  let excludes (header_table : HeaderTable.t) (ctx : Env.context)
      (hty : HeapType.t) (inst : Instance.t) =
    let check_excludes () =
      Log.debug (fun m ->
          m "@[<v>Checking if instance '%s' is excluded from type@ %a@]"
            Instance.(inst.name)
            (Pretty.pp_header_type ctx)
            hty);
      let x = Env.pick_fresh_name ctx "x" in
      let refined = HeapType.Refinement (x, Top, Neg (IsValid (0, inst))) in
      let result = P.check_subtype hty refined ctx header_table in
      Result.iter result ~f:(fun does_incl ->
          Cache.data := Map.set !Cache.data ~key:inst ~data:does_incl);
      result
    in
    if !Cache.enabled then (
      match Cache.lookup inst with
      | Some result ->
        Log.debug (fun m -> m "@[INSTANCE CACHE: HIT (%s)@]" inst.name);
        return (not result)
      | None ->
        Log.debug (fun m -> m "@[INSTANCE CACHE: MISS (%s)@]" inst.name);
        check_excludes ())
    else check_excludes ()

  let packet_length_gte_n (header_table : HeaderTable.t) (ctx : Env.context)
      (n : int) (hty : HeapType.t) =
    let x = Env.pick_fresh_name ctx "x" in
    let refined_pkt_length =
      Refinement
        (x, Top, Gt (ArithExpr (Length (0, PktIn)), ArithExpr (Num (n - 1))))
    in
    P.check_subtype hty refined_pkt_length ctx header_table
end

module ExprChecker (P : Prover.S) = struct
  module HOps = HeapTypeOps (P)

  let rec check_arith_expr (header_table : HeaderTable.t) (ctx : Env.context)
      (hty : HeapType.t) (expr : Expression.arith) =
    match expr with
    | Num _ -> Ok Nat
    | Length (_, _) -> Ok Nat
    | Plus (n, m) -> (
      let%bind tyn = check_arith_expr header_table ctx hty n
      and tym = check_arith_expr header_table ctx hty m in
      match (tyn, tym) with
      | Nat, Nat -> Ok Nat
      | _ -> Error (`TypeError "Arguments to '+' must be of type Nat"))

  let rec check_bv_expr (header_table : HeaderTable.t) (ctx : Env.context)
      (hty : HeapType.t) (expr : Expression.bv) =
    match expr with
    | Minus (tm1, tm2) -> (
      let%bind tytm1 = check_bv_expr header_table ctx hty tm1
      and tytm2 = check_bv_expr header_table ctx hty tm2 in
      match (tytm1, tytm2) with
      | BitVec s1, BitVec s2 ->
        if eq_size s1 s2 then Ok (BitVec s1)
        else Error (`TypeError "Arguments to '-' must have the same type")
      | _ -> Error (`TypeError "Arguments to '-' must be of type BitVec"))
    | Bv Nil -> Ok (BitVec (StaticSize 0))
    | Bv bv -> Ok (BitVec (StaticSize (BitVector.sizeof bv)))
    | Concat (tm1, tm2) ->
      let%bind tybv1 = check_bv_expr header_table ctx hty tm1
      and tybv2 = check_bv_expr header_table ctx hty tm2 in
      tybv_concat tybv1 tybv2
    | Slice (Instance (_, inst), l, r) ->
      let%bind incl = HOps.includes header_table ctx hty inst in
      if incl then return (BitVec (StaticSize (r - l)))
      else
        Error
          (`TypeError
            (Fmt.str
               "Instance %s must be included in input type to typecheck term \
                instance slice '%s[%d:%d]'"
               inst.name inst.name l r))
    | Slice (Packet (_, _), l, r) -> Ok (BitVec (StaticSize (r - l)))
    | Packet (_, _) -> Ok (BitVec MaxLen)

  let check_expr (header_table : HeaderTable.t) (ctx : Env.context)
      (hty : HeapType.t) (expr : Expression.t) =
    match expr with
    | ArithExpr e -> check_arith_expr header_table ctx hty e
    | BvExpr e -> check_bv_expr header_table ctx hty e
end

module FormChecker (P : Prover.S) = struct
  module HOps = HeapTypeOps (P)
  module EC = ExprChecker (P)

  let rec check_form (header_table : HeaderTable.t) (ctx : Env.context)
      (hty : HeapType.t) (expr : Formula.t) =
    match expr with
    | True -> return Bool
    | False -> return Bool
    | IsValid (_, _) ->
      (* We must not perform includes checks, if the expression checks for
         validity *)
      return Bool
      (* let%bind incl = HOps.includes header_table ctx hty inst in if incl then
         return Bool else Error (`TypeError (Fmt.str "Instance %s must be
         included in input type to typecheck expression '%s.valid'" inst.name
         inst.name)) *)
    | Eq (tm1, tm2) ->
      let%bind tytm1 = EC.check_expr header_table ctx hty tm1
      and tytm2 = EC.check_expr header_table ctx hty tm2 in
      if [%compare.equal: ty] tytm1 tytm2 then return Bool
      else
        Error
          (`TypeError
            (Fmt.str "@[The terms must have the same type (%a/%a)@]"
               Pretty.pp_type tytm1 Pretty.pp_type tytm2))
    | Gt (tm1, tm2) -> (
      let%bind tytm1 = EC.check_expr header_table ctx hty tm1
      and tytm2 = EC.check_expr header_table ctx hty tm2 in
      match (tytm1, tytm2) with
      | Nat, Nat -> return Bool
      | BitVec _, BitVec _ -> return Bool
      | _ -> Error (`TypeError "The terms must have the same type"))
    | Neg e -> check_form header_table ctx hty e
    | And (e1, e2) | Or (e1, e2) | Implies (e1, e2) ->
      let%map _ = check_form header_table ctx hty e1
      and _ = check_form header_table ctx hty e2 in
      Bool
end

module CompleteChecker (C : Encoding.Config) : Checker = struct
  module P = Prover.Make (Encoding.FixedWidthBitvectorEncoding (C))
  module FC = FormChecker (P)
  module C = Chomp.Optimized (P)
  include HeapTypeOps (P)

  let init () = ()

  let rec compute_type (cmd : Command.t)
      ((hty_var, hty_arg) : string * HeapType.t) (ctx : Env.context)
      (header_table : HeaderTable.t) =
    let open HeapType in
    match cmd with
    | Add inst ->
      Log.debug (fun m -> m "@[<v>Typechecking add(%s)...@]" inst.name);
      let%bind excl = excludes header_table ctx hty_arg inst in
      if not excl then
        Error
          (`TypeError
            (Fmt.str "Instance %s must be excluded from input type." inst.name))
      else
        let y = Env.pick_fresh_name ctx "y" in
        let v = Env.pick_fresh_name ctx "v" in
        let inst_size = Instance.sizeof inst in
        let%map hty_out =
          let w = Env.pick_fresh_name ctx "w" in
          let hty_inst =
            Refinement
              ( v,
                HeapType.instance inst header_table w,
                Formula.ands
                  [ Eq (ArithExpr (Length (0, PktIn)), ArithExpr (Num 0));
                    Eq (ArithExpr (Length (0, PktOut)), ArithExpr (Num 0));
                    Eq
                      ( BvExpr (Slice (Instance (0, inst), 0, inst_size)),
                        BvExpr (Bv (BitVector.zero inst_size)) )
                  ] )
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
              "Checking if computed output type is a subtype of the ascribed \
               output type...");
        let%bind output_is_subtype =
          P.check_subtype chty_out ascb_hty_out
            [ (x, Env.VarBind ascb_hty_in) ]
            header_table
        in
        if output_is_subtype then return ascb_hty_out
        else
          Error
            (`TypeError
              "The computed output type must be a subtype of the ascribed \
               output type"))
      else
        Error
          (`TypeError
            "The argument input type must be a subtype of the ascribed input \
             type")
    | Extract inst ->
      Log.debug (fun m -> m "@[<v>Typechecking extract(%s)...@]" inst.name);
      Log.debug (fun m ->
          m "@[<v>Input type:@ %a@]" Pretty.pp_header_type_raw hty_arg);
      Log.debug (fun m -> m "@[<v>Input context:@ %a@]" Pretty.pp_context ctx);
      Log.debug (fun m ->
          m
            "@[<v>Checking if pkt_in of@ %a@ provides enough bits in context@ \
             %a...@]"
            Pretty.pp_header_type_raw
            (refresh_binders hty_arg ctx)
            Pretty.pp_context ctx);
      let x = Env.pick_fresh_name ctx "x" in
      let refined_pkt_length =
        Refinement
          ( x,
            hty_arg,
            Gt
              ( ArithExpr (Length (0, PktIn)),
                ArithExpr (Num (Instance.sizeof inst - 1)) ) )
      in
      let%bind has_enough_bits =
        P.check_subtype hty_arg refined_pkt_length ctx header_table
      in
      if has_enough_bits then (
        let y = Env.pick_fresh_name ctx "y" in
        let z = Env.pick_fresh_name ctx "z" in
        let phi =
          And
            ( Eq (ArithExpr (Length (0, PktIn)), ArithExpr (Num 0)),
              Eq (ArithExpr (Length (0, PktOut)), ArithExpr (Num 0)) )
        in
        let var_inst = Env.pick_fresh_name ctx "v" in
        let hty_inst = HeapType.instance inst header_table var_inst in
        let tyinst = Refinement (z, hty_inst, phi) in
        Log.debug (fun m ->
            m "Input type before chomping:@ %a" Pretty.pp_header_type_raw
              hty_arg);

        let%bind ctx_chomp = return ((y, Env.VarBind tyinst) :: ctx) in

        let%bind chomped =
          C.chomp (shift_header_type hty_arg 0 1) ctx_chomp inst header_table
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
        let pkt_out_equal = Syntax.packet_equality 2 0 PktOut in
        (* Check that inst[0:sizeof(inst)]@(result of chomp).pkt_in =
           x.pkt_in *)
        let pkt_in_equal =
          And
            ( Eq
                ( BvExpr
                    (Concat
                       ( Slice (Instance (1, inst), 0, Instance.sizeof inst),
                         Packet (0, PktIn) )),
                  BvExpr (Packet (2, PktIn)) ),
              Eq
                ( ArithExpr
                    (Plus (Length (0, PktIn), Num (Instance.sizeof inst))),
                  ArithExpr (Length (2, PktIn)) ) )
        in
        let u = Env.pick_fresh_name ctx "u" in
        let chomped_eq =
          Refinement
            (u, chomped, And (insts_equal, And (pkt_out_equal, pkt_in_equal)))
        in
        return (Sigma (y, tyinst, chomped_eq)))
      else
        Error
          (`TypeError
            (Printf.sprintf
               "Tried to chomp off %d bits, but 'pkt_in' does not provide \
                enough bits."
               (Instance.sizeof inst)))
    | If (e, c1, c2) -> (
      Log.debug (fun m ->
          m "@[<v>Typechecking@ @[<v 2>if(%a) {@ %a } else {@ %a @ }...@]@]"
            (Pretty.pp_form [ ("_", NameBind) ])
            e Pretty.pp_command c1 Pretty.pp_command c2);
      Log.debug (fun m ->
          m "@[<v>Input type:@ %a@]" (Pretty.pp_header_type ctx) hty_arg);
      Log.debug (fun m -> m "@[<v>Input context:@ %a@]" Pretty.pp_context ctx);
      let%bind tye = FC.check_form header_table ctx hty_arg e in
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
            (hty_var, Refinement (x, hty_arg, Neg e))
            ctx header_table
        in
        return
          (Choice
             ( Refinement (y, tyc1, shift_form e 0 1),
               Refinement (y, tyc2, shift_form (Neg e) 0 1) ))
      | _ -> Error (`TypeError "Expression must be of type Bool"))
    | Assign (inst, left, right, tm) ->
      Log.debug (fun m ->
          m "@[<v>Typechecking %s.[%d:%d]:=%a...@]" inst.name left right
            (Pretty.pp_expr ctx) tm);
      Log.debug (fun m ->
          m "@[<v>Input type:@ %a@]" (Pretty.pp_header_type ctx) hty_arg);
      Log.debug (fun m -> m "@[<v>Input context:@ %a@]" Pretty.pp_context ctx);
      (* if not (Instance.slice_matches_field inst left right) then Error
         (Printf.sprintf "Invalid slice [%d:%d] on instance %s" left right
         inst.name) else *)
      let%bind incl = includes header_table ctx hty_arg inst in
      if not incl then
        Error
          (`TypeError
            (Printf.sprintf "Instance '%s' not included in header type."
               inst.name))
      else
        let inst_size = Instance.sizeof inst in

        (* Ensure that all instances != inst are equal *)
        let insts_equal =
          HeaderTable.to_list header_table
          |> List.filter ~f:(fun i -> not ([%compare.equal: Instance.t] inst i))
          |> Syntax.inst_equality 1 0
        in
        (* For instance inst, ensure that all bits except for the assigned ones
           are equal *)
        let fields_equal =
          if left > 0 then
            Eq
              ( BvExpr (Slice (Instance (0, inst), 0, left)),
                BvExpr (Slice (Instance (1, inst), 0, left)) )
          else insts_equal
        in
        let fields_equal =
          if inst_size - right > 0 then
            let eq_right =
              Eq
                ( BvExpr (Slice (Instance (0, inst), right, inst_size)),
                  BvExpr (Slice (Instance (1, inst), right, inst_size)) )
            in
            And (fields_equal, eq_right)
          else fields_equal
        in

        let y = Env.pick_fresh_name ctx "y" in

        return
          (Refinement
             ( y,
               Top,
               And
                 ( Eq
                     ( BvExpr (Slice (Instance (0, inst), left, right)),
                       shift_expr tm 0 1 ),
                   And
                     ( fields_equal,
                       (* Ensure that pkt_in/pkt_out are equal *)
                       And
                         ( Syntax.packet_equality 1 0 PktIn,
                           Syntax.packet_equality 1 0 PktOut ) ) ) ))
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
              ( Eq (ArithExpr (Length (0, PktOut)), ArithExpr (Num 0)),
                And
                  ( Eq (BvExpr (Packet (0, PktIn)), BvExpr (Packet (1, PktOut))),
                    Eq
                      ( ArithExpr (Length (0, PktIn)),
                        ArithExpr (Length (1, PktOut)) ) ) ) )
      in
      let rhs =
        Refinement
          ( y,
            empty,
            And
              ( Eq (ArithExpr (Length (0, PktOut)), ArithExpr (Num 0)),
                And
                  ( Eq (BvExpr (Packet (0, PktIn)), BvExpr (Packet (2, PktIn))),
                    Eq
                      ( ArithExpr (Length (0, PktIn)),
                        ArithExpr (Length (2, PktIn)) ) ) ) )
      in
      let concat = Sigma (z, lhs, rhs) in
      return concat
    | Remit inst ->
      Log.debug (fun m -> m "@[<v>Typechecking remit(%s)...@]" inst.name);
      let%bind incl = includes header_table ctx hty_arg inst in
      if not incl then
        Error
          (`TypeError
            (Printf.sprintf "Instance '%s' not included in heap type" inst.name))
      else
        let x = Env.pick_fresh_name ctx "x" in
        let y = Env.pick_fresh_name ctx "y" in
        let var_empty = Env.pick_fresh_name ctx "w" in
        let empty = HeapType.empty header_table var_empty in
        let inst_size = Instance.sizeof inst in
        let ref =
          And
            ( And
                ( Eq (ArithExpr (Length (0, PktIn)), ArithExpr (Num 0)),
                  Eq (ArithExpr (Length (0, PktOut)), ArithExpr (Num inst_size))
                ),
              Eq
                ( BvExpr (Slice (Packet (0, PktOut), 0, inst_size)),
                  BvExpr (Slice (Instance (2, inst), 0, inst_size)) ) )
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
    | Remove inst ->
      let%bind incl = includes header_table ctx hty_arg inst in
      if not incl then
        Error
          (`TypeError
            (Printf.sprintf "Instance '%s' not included in heap type" inst.name))
      else
        let y = Env.pick_fresh_name ctx "y" in
        let pred =
          Formula.ands
            [ other_instances header_table inst |> Syntax.inst_equality 0 1;
              Syntax.packet_equality 0 1 PktIn;
              Syntax.packet_equality 0 1 PktOut;
              Neg (IsValid (0, inst))
            ]
        in
        return (Refinement (y, Top, pred))
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
        else ctx
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
      return (Refinement (y, Top, Syntax.heap_equality 1 0 header_table))

  let check_subtype = P.check_subtype
end

module SemanticChecker (C : Encoding.Config) : Checker = struct
  module P = Prover.Make (Encoding.FixedWidthBitvectorEncoding (C))
  module FC = FormChecker (P)
  module EC = ExprChecker (P)
  include HeapTypeOps (P)

  let init () =
    Cache.enabled := true;
    Cache.clear

  let rec compute_type (cmd : Command.t)
      ((hty_var, hty_arg) : string * HeapType.t) (ctx : Env.context)
      (header_table : HeaderTable.t) =
    let open HeapType in
    match cmd with
    | Add inst ->
      Log.debug (fun m -> m "@[<v>Typechecking add(%s)...@]" inst.name);
      Log.debug (fun m ->
          m "@[<v>Input type:@ %a@]" (Pretty.pp_header_type ctx) hty_arg);
      let%bind excl = excludes header_table ctx hty_arg inst in
      if not excl then
        Error
          (`TypeError
            (Fmt.str "Instance %s must be excluded from input type." inst.name))
      else
        let y = Env.pick_fresh_name ctx "y" in
        let other_insts_unchanged =
          other_instances header_table inst |> Syntax.inst_equality 0 1
        in
        let inst_size = Instance.sizeof inst in
        let pred =
          Formula.ands
            [ IsValid (0, inst);
              Syntax.packet_equality 0 1 PktIn;
              Syntax.packet_equality 0 1 PktOut;
              other_insts_unchanged;
              Eq
                ( BvExpr (Slice (Instance (0, inst), 0, inst_size)),
                  BvExpr (Bv (BitVector.zero inst_size)) )
            ]
        in
        let _ = if !Cache.enabled then Cache.update inst true else () in
        return (Refinement (y, Top, pred))
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
              "Checking if computed output type is a subtype of the ascribed \
               output type...");
        let%bind output_is_subtype =
          P.check_subtype chty_out ascb_hty_out
            [ (x, Env.VarBind ascb_hty_in) ]
            header_table
        in
        if output_is_subtype then return ascb_hty_out
        else
          Error
            (`TypeError
              "The computed output type must be a subtype of the ascribed \
               output type"))
      else
        Error
          (`TypeError
            "The argument input type must be a subtype of the ascribed input \
             type")
    | Extract inst ->
      Log.debug (fun m -> m "@[<v>Typechecking extract(%s)...@]" inst.name);
      Log.debug (fun m ->
          m "@[<v>Input type:@ %a@]" Pretty.pp_header_type_raw hty_arg);
      Log.debug (fun m -> m "@[<v>Input context:@ %a@]" Pretty.pp_context ctx);
      Log.debug (fun m ->
          m
            "@[<v>Checking if pkt_in of@ %a@ provides enough bits in context@ \
             %a...@]"
            Pretty.pp_header_type_raw
            (refresh_binders hty_arg ctx)
            Pretty.pp_context ctx);
      let inst_size = Instance.sizeof inst in
      let%bind has_enough_bits =
        packet_length_gte_n header_table ctx inst_size hty_arg
      in
      if has_enough_bits then
        let y = Env.pick_fresh_name ctx "y" in
        let pred =
          Formula.ands
            [ IsValid (0, inst);
              Eq
                ( BvExpr
                    (Concat
                       ( Slice (Instance (0, inst), 0, inst_size),
                         Packet (0, PktIn) )),
                  BvExpr (Packet (1, PktIn)) );
              Eq
                ( ArithExpr (Plus (Length (0, PktIn), Num inst_size)),
                  ArithExpr (Length (1, PktIn)) );
              other_instances header_table inst |> Syntax.inst_equality 0 1;
              packet_equality 0 1 PktOut
            ]
        in
        let _ = if !Cache.enabled then Cache.update inst true else () in
        return (Refinement (y, Top, pred))
      else
        Error
          (`TypeError
            (Printf.sprintf
               "Tried to chomp off %d bits, but 'pkt_in' does not provide \
                enough bits."
               (Instance.sizeof inst)))
    | If (e, c1, c2) -> (
      Log.debug (fun m ->
          m "@[<v>Typechecking@ @[<v 2>if(%a) {@ %a } else {@ %a @ }...@]@]"
            (Pretty.pp_form [ ("_", NameBind) ])
            e Pretty.pp_command c1 Pretty.pp_command c2);
      Log.debug (fun m ->
          m "@[<v>Input type:@ %a@]" (Pretty.pp_header_type ctx) hty_arg);
      Log.debug (fun m -> m "@[<v>Input context:@ %a@]" Pretty.pp_context ctx);
      let cache_snapshot = !Cache.data in
      let%bind tye = FC.check_form header_table ctx hty_arg e in
      let _ = if !Cache.enabled then Cache.populate_from_form e false else () in
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
        let ctx_then = Env.add_binding ctx hty_var (Env.VarBind hty_in_then) in
        Log.debug (fun m ->
            m "@[<v>Computed type for then-branch:@ %a@]"
              (Pretty.pp_header_type ctx_then)
              tyc1);
        Log.debug (fun m -> m "@[<v>Typechecking 'else' branch...@]");
        let hty_in_else =
          Simplify.fold_refinements (Refinement (x, hty_arg, Neg e))
        in
        let cache_then = !Cache.data in
        let _ = if !Cache.enabled then Cache.data := cache_snapshot else () in
        let%bind tyc2 =
          compute_type c2 (hty_var, hty_in_else) ctx header_table
        in
        let ctx_else = Env.add_binding ctx hty_var (Env.VarBind hty_in_else) in
        Log.debug (fun m ->
            m "@[<v>Computed type for else-branch:@ %a@]"
              (Pretty.pp_header_type ctx_else)
              tyc2);
        let _ =
          if !Cache.enabled then Cache.merge cache_then !Cache.data else ()
        in
        return
          (Choice
             ( Refinement (y, tyc1, shift_form e 0 1),
               Refinement (y, tyc2, shift_form (Neg e) 0 1) ))
      | _ -> Error (`TypeError "Expression must be of type Bool"))
    | Assign (inst, left, right, tm) ->
      Log.debug (fun m ->
          m "@[<v>Typechecking %s.[%d:%d]:=%a...@]" inst.name left right
            (Pretty.pp_expr ctx) tm);
      Log.debug (fun m ->
          m "@[<v>Input type:@ %a@]" (Pretty.pp_header_type ctx) hty_arg);
      Log.debug (fun m -> m "@[<v>Input context:@ %a@]" Pretty.pp_context ctx);

      let%bind tyr = EC.check_expr header_table ctx hty_arg tm in
      let expr_typechecks =
        match tyr with
        | BitVec (StaticSize size) ->
          assert (size = right - left);
          size = right - left
        | _ -> false
      in

      if not expr_typechecks then
        Error
          (`TypeError
            (Printf.sprintf
               "Assigned expression must have the same shape as the header \
                field."))
      else
        let%bind incl = includes header_table ctx hty_arg inst in
        if not incl then
          Error
            (`TypeError
              (Printf.sprintf "Instance '%s' not included in header type."
                 inst.name))
        else
          let inst_size = Instance.sizeof inst in

          (* Ensure that all instances != inst are equal *)
          let insts_equal =
            other_instances header_table inst |> Syntax.inst_equality 0 1
          in

          (* For instance inst, ensure that all bits except for the assigned
             ones are equal *)
          let fields_equal =
            if left = 0 then
              if (* ι[0:r] *)
                 inst_size - right > 0 then
                (* right < sizeof(ι) *)
                Eq
                  ( BvExpr (Slice (Instance (0, inst), right, inst_size)),
                    BvExpr (Slice (Instance (1, inst), right, inst_size)) )
              else (* right = sizeof(ι) *)
                True
            else if (* ι[n:r] where n > 0 *)
                    inst_size - right > 0 then
              (* ι[n:m] where n > 0 ∧ m < r *)
              And
                ( Eq
                    ( BvExpr (Slice (Instance (0, inst), 0, left)),
                      BvExpr (Slice (Instance (1, inst), 0, left)) ),
                  Eq
                    ( BvExpr (Slice (Instance (0, inst), right, inst_size)),
                      BvExpr (Slice (Instance (1, inst), right, inst_size)) ) )
            else
              (* ι[n:m] where n > 0 ∧ m = r *)
              Eq
                ( BvExpr (Slice (Instance (0, inst), 0, left)),
                  BvExpr (Slice (Instance (1, inst), 0, left)) )
          in

          let y = Env.pick_fresh_name ctx "y" in
          let pred =
            Formula.ands
              [ Syntax.packet_equality 0 1 PktIn;
                Syntax.packet_equality 0 1 PktOut;
                insts_equal;
                fields_equal;
                Eq
                  ( BvExpr (Slice (Instance (0, inst), left, right)),
                    shift_expr tm 0 1 );
                Or
                  ( And (Neg (IsValid (0, inst)), Neg (IsValid (1, inst))),
                    And (IsValid (0, inst), IsValid (1, inst)) )
              ]
          in

          return (Refinement (y, Top, pred))
    | Reset ->
      Log.debug (fun m -> m "@[<v>Typechecking reset...@]");
      let y = Env.pick_fresh_name ctx "y" in
      let pred =
        Formula.ands
          [ Eq (ArithExpr (Length (0, PktOut)), ArithExpr (Num 0));
            Eq
              ( BvExpr (Packet (0, PktIn)),
                BvExpr (Concat (Packet (1, PktOut), Packet (1, PktIn))) );
            Eq
              ( ArithExpr (Length (0, PktIn)),
                ArithExpr (Plus (Length (1, PktOut), Length (1, PktIn))) );
            HeaderTable.to_list header_table
            |> List.fold ~init:True ~f:(fun acc i ->
                   And (Neg (IsValid (0, i)), acc))
          ]
      in
      let _ =
        if !Cache.enabled then
          Cache.invalidate (HeaderTable.to_list header_table)
        else ()
      in
      return (Refinement (y, Top, pred))
    | Remit inst ->
      Log.debug (fun m -> m "@[<v>Typechecking remit(%s)...@]" inst.name);
      let%bind incl = includes header_table ctx hty_arg inst in
      if not incl then
        Error
          (`TypeError
            (Printf.sprintf "Instance '%s' not included in header type"
               inst.name))
      else
        let y = Env.pick_fresh_name ctx "y" in
        let inst_size = Instance.sizeof inst in
        let pred =
          Formula.ands
            [ HeaderTable.to_list header_table |> Syntax.inst_equality 0 1;
              Syntax.packet_equality 0 1 PktIn;
              Eq
                ( BvExpr (Packet (0, PktOut)),
                  BvExpr
                    (Concat
                       ( Packet (1, PktOut),
                         Slice (Instance (1, inst), 0, inst_size) )) );
              Eq
                ( ArithExpr (Length (0, PktOut)),
                  ArithExpr (Plus (Length (1, PktOut), Num inst_size)) )
            ]
        in
        return (Refinement (y, Top, pred))
    | Remove inst ->
      let%bind incl = includes header_table ctx hty_arg inst in
      if not incl then
        Error
          (`TypeError
            (Printf.sprintf "Instance '%s' not included in heap type" inst.name))
      else
        let y = Env.pick_fresh_name ctx "y" in
        let pred =
          Formula.ands
            [ other_instances header_table inst |> Syntax.inst_equality 0 1;
              Syntax.packet_equality 0 1 PktIn;
              Syntax.packet_equality 0 1 PktOut;
              Neg (IsValid (0, inst))
            ]
        in
        let _ = if !Cache.enabled then Cache.update inst false else () in
        return (Refinement (y, Top, pred))
    | Seq (c1, c2) -> (
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
        else ctx
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
      match (c1, c2) with
      | Ascription _, _ | _, Ascription _ -> return hty_subst
      | _ ->
        let hty_subst = Substitution.simplify hty_subst C.maxlen in
        return hty_subst)
    | Skip ->
      Log.debug (fun m -> m "@[<v>Typechecking skip...@]");
      Log.debug (fun m ->
          m "@[<v>Input type:@ %a@]" (Pretty.pp_header_type ctx) hty_arg);
      let y = Env.pick_fresh_name ctx "y" in
      return (Refinement (y, Top, Syntax.heap_equality 0 1 header_table))

  let check_subtype = P.check_subtype
end

module Make (C : Checker) : S = struct
  let check_type ?(enable_includes_cache = true) (cmd : Command.t)
      (ty : pi_type) (header_table : HeaderTable.t) =
    match ty with
    | Pi (x, annot_tyin, annot_tyout) -> (
      let _ = if enable_includes_cache then C.init () else () in
      let result =
        let%bind tycout = C.compute_type cmd (x, annot_tyin) [] header_table in
        let ctx = [ (x, Env.VarBind annot_tyin) ] in
        Log.debug (fun m ->
            m
              "@[<v>Type computed by type checker:@ (%s:@[<v>@ %a@]@ )@ →@ %a@ \
               @]@."
              x (Pretty.pp_header_type []) annot_tyin
              (Pretty.pp_header_type ctx)
              (Simplify.fold_refinements tycout));
        let%bind res = C.check_subtype tycout annot_tyout ctx header_table in
        Log.debug (fun m ->
            m "@[Checking if %a <: ∅@]" (Pretty.pp_header_type ctx) tycout);
        let%bind tycout_nothing =
          C.check_subtype tycout Nothing ctx header_table
        in
        if not tycout_nothing then
          if res then return res
          else
            Error
              (`TypeError
                "Expected the computed output header type to be a subtype of \
                 the annotated output header type")
        else Error (`TypeError "Computed output type is equivalent to Nothing")
      in
      match result with
      | Ok _ -> TypecheckingResult.Success
      | Error (`EncodingError e)
      | Error (`TypeError e)
      | Error (`VariableLookupError e) ->
        TypecheckingResult.TypeError e)
end
