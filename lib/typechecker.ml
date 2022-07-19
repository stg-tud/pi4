open Core_kernel
open Result
open Let_syntax
open Syntax
open Formula
open HeapType
open Expression
module Log = (val Logs.src_log Logging.typechecker_src : Logs.LOG)
module CLog = (val Logs.src_log Logging.cache_src : Logs.LOG)

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

let get_min_or_none x y = 
match x, y with
| Some c1, Some c2 -> 
  if c1 < c2 then
    Some c1
  else
    Some c2
| None, Some c
| Some c, None -> 
  Some (c)
| _ -> None

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

let rec get_pkt_len (hty : HeapType.t) pkt = 
  let handle_rslt r1 r2 = 
    match r1, r2 with
    | Ok(Some(l)), Ok(None)
    | Ok(None), Ok(Some(l)) -> Ok(Some(l))
    | Ok(Some(_)), Ok(Some(_)) -> Error(`AmbigousLengthError)
    | Error e, Ok _
    | Ok _ , Error e -> Error e
    | _ -> Ok(None)
  in
  let rec pkt_in_len_exp (form : Formula.t) = 
    match pkt with
    | PktIn -> (
      match form with
      | And(f1, f2)
      | Or(f1, f2) -> 
        handle_rslt (pkt_in_len_exp f1) (pkt_in_len_exp f2)
      | Eq(ArithExpr(Length(_, PktIn)), ArithExpr(Num (i))) ->
        Ok(Some(i))
      | Gt(ArithExpr(Length(_, PktIn)), ArithExpr(Num (i))) ->
        Ok(Some(i + 1))
      | _ -> 
        Ok(None))
    | PktOut -> 
      match form with
      | And(f1, f2)
      | Or(f1, f2) -> 
        handle_rslt (pkt_in_len_exp f1) (pkt_in_len_exp f2)
      | Eq(ArithExpr(Length(_, PktOut)), ArithExpr(Num (i))) ->
        Ok(Some(i))
      | Gt(ArithExpr(Length(_, PktOut)), ArithExpr(Num (i))) ->
        Ok(Some(i + 1))
      | _ -> 
        Ok(None) 
  in
  match hty with 
  | Nothing
  | Sigma _
  | Top -> Ok(None)
  | Substitution(hty1, _, hty2)
  | Choice(hty1, hty2) -> 
    handle_rslt (get_pkt_len hty1 pkt) (get_pkt_len hty2 pkt)
  | Refinement(_, hty, e) -> 
    handle_rslt (get_pkt_len hty pkt) (pkt_in_len_exp e)
  
    

module type S = sig
  val check_type : 
    Command.t -> 
    ?smpl_subs:bool -> 
    ?incl_cache:bool ->
    ?len_cache:bool ->
    ?dynamic_maxlen:bool ->
    pi_type -> 
    HeaderTable.t -> 
    TypecheckingResult.t
end

module type Checker = sig
  
  val set_maxlen :
    var -> unit

  val reset_cache :
  unit -> unit
  val compute_type :
    Command.t ->
    ?smpl_subs:bool ->
    ?init_pkt_in:(var)option ->
    ?init_pkt_out:(var)option ->
    ?incl_cache:bool ->
    ?len_cache:bool ->
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

module HeapTypeOps (P : Prover.S) = struct
  let enable_includes_cache = ref false
  let enable_len_cache = ref false
  let includes_cache = ref (Map.empty(module Instance))

  (* Represents the min length of PktIn at runtime *)
  let pkt_in_chache = ref (None)

  (* Represents the min length of PktOut at runtime *)
  let pkt_out_chache = ref (None)

  let clear_len_caches = 
    pkt_in_chache := None;
    pkt_out_chache := None

  let clear_includes_cache = 
    includes_cache := Map.empty(module Instance)
    
  let clear_caches = 
    Log.debug(fun m -> m "Cleared caches");
    clear_len_caches;
    clear_includes_cache

  let update_includes_cache (inst : Instance.t) (valid : bool)= 
    Log.debug(fun m -> m "Updated include_cache: %a %b" Pretty.pp_instance inst valid );
    includes_cache := Map.set !includes_cache ~key:inst ~data:valid

  let rec set_includes_cache_if form neg = 
    match form with
    | And(f_l, f_r) -> 
      set_includes_cache_if f_l neg;
      set_includes_cache_if f_r neg;
    | IsValid(_, i) -> update_includes_cache i (not neg);
    | Neg(IsValid(_, i)) -> update_includes_cache i neg;
    | _ -> ()

  let rec invalidate_includes_cache lst =
    match lst with
    | [] -> ()
    | h :: t -> update_includes_cache h false; invalidate_includes_cache t
  
  let merge_cache c1 c2 =
    Log.debug(fun m -> m "Mergingn includes caches");
    let rec mc l = 
      match l with
      | [] -> ()
      | (k, v) :: t -> 
        let rslt = Map.find c2 k in
        match rslt with
        | Some (v2) -> 
          if (v && v2) || (not(v) && not(v2)) then
            update_includes_cache k v
          else 
            ();
          mc t
        | _ -> mc t
    in
    
    let lst_1 = Map.to_alist c1 in
    mc lst_1

  let subs_pkt_in_cache v =
    match !pkt_in_chache with
    | Some x -> 
      Log.debug(fun m -> m "Len Cache in (subs) = %i" (x - v));
      if x - v < 0 then 
        pkt_in_chache := None
      else 
        pkt_in_chache := Some(x - v)
    | _ -> ()
  
  let add_pkt_in_cache v =
    match !pkt_in_chache with
    | Some x -> 
      Log.debug(fun m -> m "Len Cache in (add) = %i" (x + v));
      pkt_in_chache := Some(x + v)
    | _ -> 
      pkt_in_chache := Some(v)

  let set_pkt_in_cache v = 
    Log.debug(fun m -> m "Len Cache in (set) = %i" v);
    pkt_in_chache := Some(v)
  
  let add_pkt_out_cache v =
    match !pkt_out_chache with
    | Some x -> 
      Log.debug(fun m -> m "Len Cache out (add) %i + %i  = %i" x v (x + v));
      pkt_out_chache := Some(x + v)
    | _ -> 
      pkt_out_chache := Some(v)

  let set_pkt_out_cache v = 
    Log.debug(fun m -> m "Len Cache out (set) = %i" v);
    pkt_out_chache := Some(v)

  let includes (header_table : HeaderTable.t) (ctx : Env.context)
      (hty : HeapType.t) (inst : Instance.t) =
    Log.debug (fun m ->
        m "@[<v>Checking if instance '%s' is included in type@ %a@]"
          Instance.(inst.name)
          (Pretty.pp_header_type ctx)
          hty);
    
    let check_includes () =
      let x = Env.pick_fresh_name ctx "x" in
      let refined = HeapType.Refinement (x, Top, IsValid (0, inst)) in
      let check_rslt = P.check_subtype hty refined ctx header_table in
      match check_rslt with
      | Ok a -> 
        Log.debug(fun m -> m "CHECK: %b" a);
        includes_cache := Map.set !includes_cache ~key:inst ~data:a;
        check_rslt
      | _ -> 
        check_rslt
    in

    if !enable_includes_cache then
      let rslt = Map.find !includes_cache inst in
      match rslt with
      | Some a -> 
        CLog.debug(fun m -> m "@[INSTANCE CACHE: HIT@]");
        Ok(a)
      | None -> 
        CLog.debug(fun m -> m "@[INSTANCE CACHE: MISS@]");
        check_includes ()
    else
      check_includes ()

  let excludes (header_table : HeaderTable.t) (ctx : Env.context)
      (hty : HeapType.t) (inst : Instance.t) =
    Log.debug (fun m ->
        m "@[<v>Checking if instance '%s' is excluded from type@ %a@]"
          Instance.(inst.name)
          (Pretty.pp_header_type ctx)
          hty);

    let check_excludes () =
      let x = Env.pick_fresh_name ctx "x" in
      let refined = HeapType.Refinement (x, Top, Neg (IsValid (0, inst))) in
      let check_rslt = P.check_subtype hty refined ctx header_table in
      match check_rslt with
      | Ok a -> 
        includes_cache := Map.set !includes_cache ~key:inst ~data:a;
        check_rslt
      | _ -> 
        check_rslt
    in

    if !enable_includes_cache then
      let rslt = Map.find !includes_cache inst in
      match rslt with
      | Some a -> 
        CLog.debug(fun m -> m "@[INSTANCE CACHE: HIT@]");
        Ok(not a)
      | None -> 
        CLog.debug(fun m -> m "@[INSTANCE CACHE: MISS@]");
        check_excludes ()
    else
      check_excludes ()

  let packet_length_gte_n (header_table : HeaderTable.t) (ctx : Env.context)
      (n : int) (hty : HeapType.t) =
    let check_lenght () = 
      let x = Env.pick_fresh_name ctx "x" in
      let refined_pkt_length =
      Refinement
        (x, Top, Gt (ArithExpr (Length (0, PktIn)), ArithExpr (Num (n - 1))))
      in
      P.check_subtype hty refined_pkt_length ctx header_table
    in

    if !enable_len_cache then
      match !pkt_in_chache with
      | Some cache -> 
        CLog.debug(fun m -> m "@[LENGTH CACHE: HIT@]");
        if n <= cache then
          Ok(true)
        else 
          check_lenght ()
      | _ -> 
        CLog.debug(fun m -> m "@[LENGTH CACHE: MISS@]");
        check_lenght () 
    else
      check_lenght ()
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
      Log.debug(fun m -> m "BV_SLICE CHECK: %b" incl);
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
      else begin
        Log.debug(fun m -> m "The terms must have the same type (%a/%a)" Pretty.pp_type tytm1 Pretty.pp_type tytm2);
        Error
          (`TypeError
            (Fmt.str "@[The terms must have the same type (%a/%a)@]"
               Pretty.pp_type tytm1 Pretty.pp_type tytm2))
      end
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

module SemanticChecker (C : Encoding.Config) : Checker = struct
  module P = Prover.Make (Encoding.FixedWidthBitvectorEncoding (C))
  module FC = FormChecker (P)
  include HeapTypeOps (P)

  let reset_cache () =
   clear_caches

  let set_maxlen len =
    P.set_maxlen len

  let rec compute_type (cmd_in : Command.t)
      ?(smpl_subs = false)
      ?(init_pkt_in = None)
      ?(init_pkt_out = None)
      ?(incl_cache = false) 
      ?(len_cache = false) 
      ((hty_var_in, hty_arg_in) : string * HeapType.t) (ctx_in : Env.context)
      (header_table_in : HeaderTable.t)=
    let open HeapType in 

    let rec compute cmd (hty_var, hty_arg) ctx header_table = 
      match cmd with
      | Command.Add inst ->
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
          update_includes_cache inst true;
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
        Log.debug (fun m -> m "Input type: %a" (Pretty.pp_header_type ctx) hty_arg);
        Log.debug (fun m ->
            m "Context used for input type: %a" Pretty.pp_context ctx);

        let%bind input_is_subtype =
          P.check_subtype hty_arg ascb_hty_in ctx header_table
        in

        if input_is_subtype then (
          let%bind chty_out =
            clear_len_caches;
            if !enable_len_cache then
              let pkt_in_len = get_pkt_len ascb_hty_in PktIn in
              let pkt_out_len = get_pkt_len ascb_hty_in PktOut in
              match pkt_in_len, pkt_out_len with
              | Ok(l_in), Ok (l_out) -> 
                compute_type cmd 
                  ~smpl_subs:smpl_subs 
                  ~init_pkt_in:l_in 
                  ~init_pkt_out:l_out
                  ~incl_cache:incl_cache
                  ~len_cache:len_cache
                  (x, ascb_hty_in) ctx header_table
              | Ok(l_in), _ -> 
                compute_type cmd 
                ~smpl_subs:smpl_subs
                ~init_pkt_in:l_in
                ~incl_cache:incl_cache
                ~len_cache:len_cache
                (x, ascb_hty_in) ctx header_table
              | _ ->  
                compute_type cmd 
                ~smpl_subs:smpl_subs
                ~incl_cache:incl_cache
                ~len_cache:len_cache
                (x, ascb_hty_in) ctx header_table
            else
              compute_type cmd 
              ~smpl_subs:smpl_subs
              ~incl_cache:incl_cache
              ~len_cache:len_cache
              (x, ascb_hty_in) ctx header_table
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
          update_includes_cache inst true;
          subs_pkt_in_cache inst_size;
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
        let%bind tye = FC.check_form header_table ctx hty_arg e in
        let cache_snapshot = !includes_cache in
        let pkt_in_cache_snapshot = !pkt_in_chache in
        let pkt_out_cache_snapshot = !pkt_out_chache in
        set_includes_cache_if e false;
        match tye with
        | Bool ->
          let x = Env.pick_fresh_name ctx "x" in
          let y = Env.pick_fresh_name ctx "y" in
          Log.debug (fun m -> m "@[<v>Typechecking 'then' branch...@]");
          let hty_in_then =
            Simplify.fold_refinements (Refinement (x, hty_arg, e))
          in
          let%bind tyc1 =
            compute c1 (hty_var, hty_in_then) ctx header_table
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
          let cache_1 = !includes_cache in
          (* cache rollback to eliminate side effect from if branch *)
          includes_cache := cache_snapshot;
          let tyc1_pkt_in_cache = !pkt_in_chache in
          let tyc1_pkt_out_cache = !pkt_out_chache in
          pkt_in_chache := pkt_in_cache_snapshot;
          pkt_out_chache := pkt_out_cache_snapshot;
          set_includes_cache_if e true;
          let%bind tyc2 =
            compute c2 (hty_var, hty_in_else) ctx header_table
          in
          let ctx_else = Env.add_binding ctx hty_var (Env.VarBind hty_in_else) in
          Log.debug (fun m ->
              m "@[<v>Computed type for else-branch:@ %a@]"
                (Pretty.pp_header_type ctx_else)
                tyc2);
          let cache_2 = !includes_cache in
          (* Merge caches *)
          clear_includes_cache;
          merge_cache cache_1 cache_2;
          pkt_in_chache := get_min_or_none tyc1_pkt_in_cache !pkt_in_chache;
          pkt_out_chache := get_min_or_none tyc1_pkt_out_cache !pkt_out_chache;

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
        let%bind incl = includes header_table ctx hty_arg inst in
        Log.debug(fun m -> m "ASSIGN INCL CHECK: %b" incl);
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

          (* For instance inst, ensure that all bits except for the assigned ones
            are equal *)
          (* let fields_equal = if left > 0 then Eq ( BvExpr (Slice (Instance (0,
            inst), 0, left)), BvExpr (Slice (Instance (1, inst), 0, left)) ) else
            True in let fields_equal = if inst_size - right > 0 then let eq_right
            = Eq ( BvExpr (Slice (Instance (0, inst), right, inst_size)), BvExpr
            (Slice (Instance (1, inst), right, inst_size)) ) in And
            (fields_equal, eq_right) else fields_equal in *)

          let fields_eq_left = 
            if left = 0 then
              True
            else
              Eq
                ( BvExpr (Slice (Instance (0, inst), 0, left)),
                  BvExpr (Slice (Instance (1, inst), 0, left)) )
          in
          let fields_eq_right =
            if inst_size - right > 0 then
              Eq
                ( BvExpr (Slice (Instance (0, inst), right, inst_size)),
                  BvExpr (Slice (Instance (1, inst), right, inst_size)) )
            else
              True
          in

          let y = Env.pick_fresh_name ctx "y" in
          let pred =
            Formula.ands
              [ Syntax.packet_equality 0 1 PktIn;
                Syntax.packet_equality 0 1 PktOut;
                insts_equal;
                fields_eq_left;
                Eq
                  ( BvExpr (Slice (Instance (0, inst), left, right)),
                    shift_expr tm 0 1 );
                fields_eq_right;
                Or
                  ( And (Neg (IsValid (0, inst)), Neg (IsValid (1, inst))),
                    And (IsValid (0, inst), IsValid (1, inst)) )
              ]
          in

          return (Refinement (y, Top, pred))
      | Reset ->
        Log.debug (fun m -> m "@[<v>Typechecking reset...@]");
        
        invalidate_includes_cache (HeaderTable.to_list header_table);

        ( 
          match !pkt_out_chache with
          | Some l -> add_pkt_in_cache l
          | None -> ()
        );
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
        return (Refinement (y, Top, pred))
      | Remit inst ->
        Log.debug (fun m -> m "@[<v>Typechecking remit(%s)...@]" inst.name);
        let%bind incl = includes header_table ctx hty_arg inst in
        Log.debug(fun m -> m "REMIT CHECK: %b" incl);
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
                IsValid(1, inst);
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
          add_pkt_out_cache inst_size;
          Log.debug (fun m -> m "@[<v>%a...@]" Pretty.pp_form_raw  pred);
          return (Refinement (y, Top, pred))
      | Remove inst ->
        let%bind incl = includes header_table ctx hty_arg inst in
        Log.debug(fun m -> m "REMOVE CHECK: %b" incl);
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
          update_includes_cache inst false;
          return (Refinement (y, Top, pred))
      | Seq (c1, c2) ->
        Log.debug (fun m ->
            m "@[<v>Typechecking sequence:@ c1:@[<v>@ %a @]@ c2:@[<v>@ %a@]@]"
              Pretty.pp_command c1 Pretty.pp_command c2);
        Log.debug (fun m ->
            m "@[<v>Input type:@ %a@]" (Pretty.pp_header_type ctx) hty_arg);
        Log.debug (fun m -> m "@[<v>Input context:@ %a@]" Pretty.pp_context ctx);
        let%bind tyc1 = compute c1 (hty_var, hty_arg) ctx header_table in

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
        let%bind tyc2 = compute c2 (y, tyc1) ctx' header_table in
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

        if smpl_subs then
          match c1, c2 with
          | Ascription _ , _
          | _, Ascription _ -> return hty_subst
          | _ ->
            let hty_subst = Substitution.simplify hty_subst !C.maxlen in
            return hty_subst
        else 
          return hty_subst


      | Skip ->
        Log.debug (fun m -> m "@[<v>Typechecking skip...@]");
        Log.debug (fun m ->
            m "@[<v>Input type:@ %a@]" (Pretty.pp_header_type ctx) hty_arg);
        let y = Env.pick_fresh_name ctx "y" in
        return (Refinement (y, Top, Syntax.heap_equality 0 1 header_table))
    in

    clear_caches;
    Log.debug(fun m -> m "Set enable_includes_cache to %b" incl_cache);
    enable_includes_cache := incl_cache;
    Log.debug(fun m -> m "Set len_cache to %b" len_cache);
    enable_len_cache := len_cache;
    Log.debug(fun m -> m "Substitution folding enabled: %b" smpl_subs);

    (
      match init_pkt_in with 
      | Some v -> set_pkt_in_cache v
      | _ -> ()
    );
    (
      match init_pkt_out with 
      | Some v -> set_pkt_out_cache v
      | _ -> ()
    );
    compute cmd_in (hty_var_in, hty_arg_in) ctx_in header_table_in
    
  let check_subtype = P.check_subtype
end

module Make (C : Checker) : S = struct
  let check_type 
    (cmd : Command.t) 
    ?(smpl_subs = true) 
    ?(incl_cache = true) 
    ?(len_cache = true) 
    ?(dynamic_maxlen = true)
    (ty : pi_type) 
    (header_table : HeaderTable.t) =
    match ty with
    | Pi (x, annot_tyin, annot_tyout) -> (
      C.reset_cache ();
      if dynamic_maxlen then
        let maxlen = HeaderTable.max_header_size header_table + 1 in
        Log.debug(fun m -> m "Dynamically setting maxlen to %i" maxlen);
        C.set_maxlen maxlen
      else
        C.set_maxlen 12000;
      let result =
        let%bind tycout = 
          if len_cache then
            let pkt_in_len = get_pkt_len annot_tyin PktIn in
            let pkt_out_len = get_pkt_len annot_tyin PktOut in
            match pkt_in_len, pkt_out_len with
            | Ok(l_in), Ok (l_out) -> 
              C.compute_type cmd 
                ~smpl_subs:smpl_subs 
                ~init_pkt_in:l_in 
                ~init_pkt_out:l_out 
                ~incl_cache:incl_cache
                ~len_cache:true
                (x, annot_tyin) [] header_table
            | Ok(l_in), _ -> 
              C.compute_type cmd 
                ~smpl_subs:smpl_subs 
                ~init_pkt_in:l_in
                ~incl_cache:incl_cache
                ~len_cache:true 
                (x, annot_tyin) [] header_table
            | _ -> 
              C.compute_type cmd 
                ~smpl_subs:smpl_subs
                ~incl_cache:incl_cache
                ~len_cache:true 
                (x, annot_tyin) [] header_table
          else
            C.compute_type cmd 
            ~smpl_subs:smpl_subs
            ~incl_cache:incl_cache
            ~len_cache:false 
            (x, annot_tyin) [] header_table

        in
        let ctx = [ (x, Env.VarBind annot_tyin) ] in
        Log.debug (fun m ->
            m
              "@[<v>Type computed by type checker:@ (%s:@[<v>@ %a@]@ )@ →@ %a@ \
               @]@."
              x (Pretty.pp_header_type []) annot_tyin
              (Pretty.pp_header_type ctx)
              (Simplify.fold_refinements tycout));
        let%bind res = C.check_subtype tycout annot_tyout ctx header_table in
        Log.debug (fun m -> m "%b" res );
        if res then return res
        else
          Error
            (`TypeError
              "Expected the computed output header type to be a subtype of the \
               annotated output header type")
      in
      match result with
      | Ok _ -> TypecheckingResult.Success
      | Error (`EncodingError e)
      | Error (`TypeError e)
      | Error (`VariableLookupError e) ->
        TypecheckingResult.TypeError e)
end
