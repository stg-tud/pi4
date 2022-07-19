open Core_kernel
open Result.Let_syntax
open Syntax
open Z3
module Log = (val Logs.src_log Logging.encoding_src : Logs.LOG)

let id_access var inst = Smtlib.Id (String.concat ~sep:"." [ var; inst ])

let id_valid var inst =
  Smtlib.Id (String.concat ~sep:"." [ var; inst; "valid" ])

let id_pkt_length var pkt =
  Smtlib.Id (String.concat ~sep:"." [ var; pkt; "length" ])

let const_access var inst = Smtlib.Const (id_access var inst)
let const_valid var inst = Smtlib.Const (id_valid var inst)
let const_pkt_len var pkt = Smtlib.Const (id_pkt_length var pkt)
let const_pkt_in var = const_access var "pkt_in"
let const_pkt_out var = const_access var "pkt_out"
let const_pkt_in_len var = const_pkt_len var "pkt_in"
let const_pkt_out_len var = const_pkt_len var "pkt_out"
let true_ = Smtlib.bool_to_term true
let false_ = Smtlib.bool_to_term false

let zero_extend i term =
  Smtlib.(App (Id (Printf.sprintf "(_ zero_extend %d)" i), [ term ]))

let ands ?(init = true_) l =
  List.reduce l ~f:Smtlib.and_ |> Option.value ~default:init

let rec freshen_binders (hty : HeapType.t) (pick_unique_name : string -> string)
    : HeapType.t =
  let open HeapType in
  match hty with
  | Nothing -> Nothing
  | Top -> Top
  | Sigma (x, hty1, hty2) ->
    let x' = pick_unique_name x in
    Sigma
      ( x',
        freshen_binders hty1 pick_unique_name,
        freshen_binders hty2 pick_unique_name )
  | Choice (hty1, hty2) ->
    Choice
      ( freshen_binders hty1 pick_unique_name,
        freshen_binders hty2 pick_unique_name )
  | Refinement (x, hty, e) ->
    let x' = pick_unique_name x in
    Refinement (x', freshen_binders hty pick_unique_name, e)
  | Substitution (hty1, x, hty2) ->
    let x' = pick_unique_name x in
    Substitution
      ( freshen_binders hty1 pick_unique_name,
        x',
        freshen_binders hty2 pick_unique_name )

let min_bit_width maxlen =
  let open Owl_base in
  int_of_float (Maths.log2 (float_of_int maxlen) +. 1.)

let rec to_string_aux (bv : Syntax.BitVector.t) =
  let open Syntax.BitVector in
  match bv with
  | Nil -> Ok ""
  | Cons (b, v) -> (
    match b with
    | Zero -> to_string_aux v >>| Printf.sprintf "0%s"
    | One -> to_string_aux v >>| Printf.sprintf "1%s"
    | _ -> Error (`EncodingError "Dont know how to encode bit variables"))

let bv_to_string v =
  let%map bs = to_string_aux v in
  Printf.sprintf "0b%s" bs

let bv_to_smt v size =
  let l = Syntax.BitVector.sizeof v in
  if l = 0 then Error (`EncodingError "Cannot encode an empty bitvector")
  else
    let%map s = bv_to_string v in
    let i = Int.of_string s in
    Smtlib.bv i size

module DynamicSize = struct
  type t =
    | Dynamic of string
    | Static of int
    | Sum of t * t
    [@@deriving compare, sexp]

  (* let rec static_value = function
    | Dynamic _ -> None
    | Static n -> Some n
    | Sum (n, m) ->
      let open Option.Let_syntax in
      let%bind n_val = static_value n in
      let%map m_val = static_value m in
      n_val + m_val *)
end

let fresh_name ctx x =
  Env.pick_fresh_name_f ctx
    ~f:(fun s ->
      let s', n = String.lsplit2 s ~on:'_' |> Option.value ~default:(s, "0") in
      Fmt.str "%s_%d" s' (int_of_string n + 1))
    x

type dsize_encoding =
  { smt_term : Smtlib.term;
    let_bindings : (string * Smtlib.term) list;
    constraints : Smtlib.term list
  }

let rec dynamic_size_to_smt (bv : DynamicSize.t) (len : int) (maxlen : int) =
  match bv with
  | Dynamic d ->
    let const = Smtlib.const d in
    let mbw = min_bit_width maxlen in
    if len > mbw then
      { smt_term = zero_extend (len - mbw) const;
        let_bindings = [];
        constraints = []
      }
    else { smt_term = const; let_bindings = []; constraints = [] }
  | Static n ->
    { smt_term = Smtlib.bv n len; let_bindings = []; constraints = [] }
  | Sum (s1, s2) ->
    let s1_enc = dynamic_size_to_smt s1 len maxlen in
    let s2_enc = dynamic_size_to_smt s2 len maxlen in
    let let_bindings' = s1_enc.let_bindings @ s2_enc.let_bindings in
    let binder = fresh_name let_bindings' "dsum" in
    let const_binder = Smtlib.(Const (Id binder)) in
    let term =
      Smtlib.bvadd
        (zero_extend 1 s1_enc.smt_term)
        (zero_extend 1 s2_enc.smt_term)
    in
    { smt_term = Smtlib.extract (len - 1) 0 const_binder;
      let_bindings = (binder, term) :: let_bindings';
      constraints =
        Smtlib.(equals (extract len len const_binder) (bv 0 1))
        :: (s1_enc.constraints @ s2_enc.constraints)
    }

let rec max_arith_value (term : Expression.arith) (maxlen : int) =
  match term with
  | Num n -> return n
  | Length (_, _) -> return maxlen
  | Plus (tm1, tm2) ->
    let%bind v1 = max_arith_value tm1 maxlen in
    let%map v2 = max_arith_value tm2 maxlen in
    v1 + v2

let id_fst_compare (Smtlib.Id x, _) (Smtlib.Id y, _) : int = String.compare x y
let id_dedup = List.dedup_and_sort ~compare:id_fst_compare

let valid_expr_to_smt (ctx : Env.context) (x : var) (inst : Instance.t) =
  let%map binder = Env.index_to_name ctx x in
  const_valid binder inst.name

module type S = sig
  val equal : string -> string -> HeaderTable.t -> Smtlib.term

  val heap_type_to_smt :
    HeaderTable.t ->
    Env.context ->
    string ->
    HeapType.t ->
    ( Smtlib.term,
      [> `EncodingError of string | `VariableLookupError of string ] )
    result

  val smt_consts :
    HeapType.t ->
    string ->
    HeaderTable.t ->
    (Smtlib.identifier * Smtlib.sort) list

  val set_maxlen :
    var -> unit
end

module type Config = sig
  val maxlen : int ref
end

module FixedWidthBitvectorEncoding (C : Config) : S = struct
  let consts (var : string) (ht : HeaderTable.t) =
    let pkt_size = min_bit_width !C.maxlen in
    HeaderTable.to_list ht
    |> List.fold ~init:[] ~f:(fun acc inst ->
           let inst_size = Instance.sizeof inst in
           (id_valid var inst.name, Smtlib.bool_sort)
           :: (id_access var inst.name, Smtlib.BitVecSort inst_size)
           :: acc)
    |> List.append
         [ (id_access var "pkt_in", Smtlib.BitVecSort !C.maxlen);
           (id_pkt_length var "pkt_in", Smtlib.BitVecSort pkt_size);
           (id_access var "pkt_out", Smtlib.BitVecSort !C.maxlen);
           (id_pkt_length var "pkt_out", Smtlib.BitVecSort pkt_size)
         ]

  let smt_consts (hty : HeapType.t) (x0 : string) (header_table : HeaderTable.t)
      =
    let rec smt_consts_aux (hty : HeapType.t)
        (acc : (Smtlib.identifier * Smtlib.sort) list) =
      match hty with
      | Nothing | Top -> acc
      | Choice (hty1, hty2) -> smt_consts_aux hty1 acc |> smt_consts_aux hty2
      | Sigma (x, hty1, hty2) ->
        let x1 = x ^ "_l" in
        let x2 = x ^ "_r" in
        consts x1 header_table @ consts x2 header_table @ acc
        |> smt_consts_aux hty1 |> smt_consts_aux hty2
      | Refinement (x, hty, _) ->
        consts x header_table @ acc |> smt_consts_aux hty
      | Substitution (hty1, x, hty2) ->
        consts x header_table @ acc
        |> smt_consts_aux hty2 |> smt_consts_aux hty1
    in
    smt_consts_aux hty (consts x0 header_table)

  let hdreq (x : string) (y : string) (inst : string) : Smtlib.term =
    let open Smtlib in
    let eq = equals (const_access x inst) (const_access y inst) in
    implies (const_valid y inst) eq

  let equal (x : string) (y : string) (ht : Syntax.HeaderTable.t) : Smtlib.term
      =
    let p = [ "pkt_in"; "pkt_out" ] in
    let pkt_terms =
      p
      |> List.fold ~init:[] ~f:(fun acc elem ->
             let len_const id = const_pkt_len id elem in
             let pkt_const id = const_access id elem in
             let eq_len = Smtlib.equals (len_const x) (len_const y) in
             let eq_pkt = Smtlib.equals (pkt_const x) (pkt_const y) in
             eq_len :: eq_pkt :: acc)
    in
    let inst_terms =
      String.Map.keys ht
      |> List.fold ~init:[] ~f:(fun acc elem ->
             let inst_const id = const_access id elem in
             let valid_const id = const_valid id elem in
             Smtlib.equals (valid_const x) (valid_const y)
             :: Smtlib.equals (inst_const x) (inst_const y)
             :: acc)
    in
    ands @@ List.join [ pkt_terms; inst_terms ]

  let pktbounds (x : string) : Smtlib.term =
    let open Smtlib in
    let pkt_size = min_bit_width !C.maxlen in

    let pkt_in = const_pkt_in x in
    let pkt_in_length = const_pkt_in_len x in
    let pkt_out = const_pkt_out x in
    let pkt_out_length = const_pkt_out_len x in
    let len_ok len_const = bvule len_const (bv !C.maxlen pkt_size) in
    let value_ok const_len const_pkt =
      let padded = zero_extend (!C.maxlen - pkt_size + 1) const_len in
      or_
        (equals const_len (bv 0 pkt_size))
        (bvult (zero_extend 1 const_pkt) (bvshl (bv 1 (!C.maxlen + 1)) padded))
    in
    ands
    @@ [ len_ok pkt_in_length;
         len_ok pkt_out_length;
         value_ok pkt_in_length pkt_in;
         value_ok pkt_out_length pkt_out
       ]

  let append_packet (x0 : string) (x1 : string) (x2 : string) (packet : string)
      =
    let open Smtlib in
    let pkt_size = min_bit_width !C.maxlen in

    let pkt var = const_access var packet in
    let pkt_len var = const_pkt_len var packet in
    let maxlen_bv = bv !C.maxlen pkt_size in
    let len_ok t = bvule t maxlen_bv in
    let newlen =
      bvadd (zero_extend 1 (pkt_len x1)) (zero_extend 1 (pkt_len x2))
    in
    let bounded len_slice = ite (len_ok len_slice) len_slice maxlen_bv in
    let padded = zero_extend (!C.maxlen - pkt_size) (pkt_len x1) in
    let binder_len = Printf.sprintf "len_%s_%s" x1 x2 in
    let const_binder_len = const binder_len in

    let binder_len_value = Printf.sprintf "len_value_%s_%s" x1 x2 in
    let const_binder_len_value = const binder_len_value in
    ands
    @@ [ Let
           ( binder_len,
             newlen,
             Let
               ( binder_len_value,
                 extract (pkt_size - 1) 0 const_binder_len,
                 and_
                   (* Addition does not overflow *)
                   (equals
                      (extract pkt_size pkt_size const_binder_len)
                      (bv 0 1))
                   (equals (pkt_len x0) (bounded const_binder_len_value)) ) );
         or_
           (equals (pkt_len x0) (bv 0 pkt_size))
           (or_
              (and_
                 (equals (pkt_len x1) (bv 0 pkt_size))
                 (equals (pkt x0) (pkt x2)))
              (and_
                 (not_ (equals (pkt_len x1) (bv 0 pkt_size)))
                 (equals (pkt x0) (bvor (pkt x1) (bvshl (pkt x2) padded)))))
       ]

  let append (x0 : string) (x1 : string) (x2 : string)
      (ht : Syntax.HeaderTable.t) =
    let open Smtlib in
    let append_valid inst =
      equals (const_valid x0 inst)
        (or_ (const_valid x1 inst) (const_valid x2 inst))
    in
    let disjoint inst =
      not_ (and_ (const_valid x1 inst) (const_valid x2 inst))
    in
    let eqs =
      String.Map.keys ht
      |> List.fold ~init:[] ~f:(fun acc inst ->
             disjoint inst :: append_valid inst :: hdreq x0 x1 inst
             :: hdreq x0 x2 inst :: acc)
    in
    ands
    @@ [ append_packet x0 x1 x2 "pkt_in"; append_packet x0 x1 x2 "pkt_out" ]
    @ eqs

  let rec static_size_of_bv_expr (maxlen : int) (term : Expression.bv) =
    match term with
    | Minus (tm1, tm2) ->
      let%bind size_tm1 = static_size_of_bv_expr maxlen tm1 in
      let%map size_tm2 = static_size_of_bv_expr maxlen tm2 in
      assert (size_tm1 = size_tm2);
      size_tm1
    | Bv Nil -> return 0
    | Bv bv -> return (Syntax.BitVector.sizeof bv)
    | Concat (tm1, tm2) ->
      let%bind size_tm1 = static_size_of_bv_expr maxlen tm1 in
      let%map size_tm2 = static_size_of_bv_expr maxlen tm2 in
      min (size_tm1 + size_tm2) maxlen
    | Slice (_, l, r) -> return (r - l)
    | Packet (_, _) -> return maxlen

  type term_encoding =
    { smt_term : Smtlib.term;
      dynamic_size : DynamicSize.t;
      let_bindings : (string * Smtlib.term) list;
      constraints : Smtlib.term list
    }

  let rec arith_expr_to_smt (ctx : Env.context) (length : int)
      (term : Expression.arith) =
    match term with
    | Num n ->
      return
        { smt_term = Smtlib.bv n length;
          dynamic_size = DynamicSize.Static length;
          let_bindings = [];
          constraints = []
        }
    | Length (x, p) ->
      assert (length >= min_bit_width !C.maxlen);
      let%map binder = Env.index_to_name ctx x in
      let smt_pkt =
        Smtlib.const (Fmt.str "%s.%a.length" binder Pretty.pp_packet p)
      in
      let ssize_diff = length - min_bit_width !C.maxlen in
      let smt =
        if ssize_diff > 0 then zero_extend ssize_diff smt_pkt else smt_pkt
      in
      { smt_term = smt;
        dynamic_size = DynamicSize.Static length;
        let_bindings = [];
        constraints = []
      }
    | Plus (tm1, tm2) ->
      let%bind tm1_enc = arith_expr_to_smt ctx length tm1 in
      let%map tm2_enc = arith_expr_to_smt ctx length tm2 in
      let let_bindings' = tm1_enc.let_bindings @ tm2_enc.let_bindings in
      let x = fresh_name let_bindings' "sum" in
      let const_x = Smtlib.(Const (Id x)) in
      (* Ensure that addition does not overflow *)
      let sum =
        Smtlib.(
          bvadd
            (zero_extend 1 tm1_enc.smt_term)
            (zero_extend 1 tm2_enc.smt_term))
      in
      { smt_term = Smtlib.extract (length - 1) 0 const_x;
        dynamic_size = DynamicSize.Static length;
        let_bindings = (x, sum) :: let_bindings';
        constraints =
          Smtlib.(equals (extract length length const_x) (bv 0 1))
          :: (tm1_enc.constraints @ tm2_enc.constraints)
      }

  let rec bv_expr_to_smt (term : Expression.bv) (length : int)
      (ctx : Env.context) : (term_encoding, 'a) result =
    match term with
    | Minus (e1, e2) ->
      let%bind { smt_term = e1_smt; dynamic_size = e1_dsize; _ } = bv_expr_to_smt e1 length ctx in
      let%map { smt_term = e2_smt; dynamic_size = e2_dsize; _ } = bv_expr_to_smt e2 length ctx in
      assert([%compare.equal: DynamicSize.t] e1_dsize e2_dsize);
      { smt_term = Smtlib.bvsub e1_smt e2_smt;
        dynamic_size = e1_dsize;
        let_bindings = [];
        constraints = []
      }
    | Bv v ->
      let%map bv_smt = bv_to_smt v length in
      let size = Syntax.BitVector.sizeof v in
      { smt_term = bv_smt;
        dynamic_size = DynamicSize.Static size;
        let_bindings = [];
        constraints = []
      }
    | Concat (e1, e2) ->
      let%bind { smt_term = e1_smt; dynamic_size = e1_dsize; _ } =
        bv_expr_to_smt e1 length ctx
      in
      let%map { smt_term = e2_smt; dynamic_size = e2_dsize; _ } =
        bv_expr_to_smt e2 length ctx
      in
      let e1_dsize_smt = dynamic_size_to_smt e1_dsize length !C.maxlen in
      let e2_dsize_smt = dynamic_size_to_smt e2_dsize length !C.maxlen in

      { smt_term =
          Smtlib.ite
            (Smtlib.equals e1_dsize_smt.smt_term (Smtlib.bv 0 length))
            e2_smt
            Smtlib.(bvor e1_smt (bvshl e2_smt e1_dsize_smt.smt_term));
        dynamic_size = DynamicSize.Sum (e1_dsize, e2_dsize);
        let_bindings = e1_dsize_smt.let_bindings @ e2_dsize_smt.let_bindings;
        constraints = e1_dsize_smt.constraints @ e2_dsize_smt.constraints
      }
    | Slice (Instance (x, inst), 0, r) when r = Instance.sizeof inst ->
      let%map name = Env.index_to_name ctx x in
      let svar = Smtlib.const (Fmt.str "%s.%s" name inst.name) in
      let size_diff = length - r in
      let smt =
        if size_diff > 0 then zero_extend size_diff svar
        else
          (* If the instance slice covers the whole range, we can just use the
             variable *)
          svar
      in
      { smt_term = smt;
        dynamic_size = DynamicSize.Static r;
        let_bindings = [];
        constraints = []
      }
    | Slice (s, l, r) ->
      assert (length >= r - l);
      let svar = Fmt.str "%a" (Pretty.pp_sliceable ctx) s in
      let extract = Smtlib.(extract (r - 1) l (const svar)) in
      let size_diff = length - (r - l) in
      let smt =
        if size_diff > 0 then zero_extend size_diff extract else extract
      in
      return
        { smt_term = smt;
          dynamic_size = DynamicSize.Static (r - l);
          let_bindings = [];
          constraints = []
        }
    | Packet (x, p) ->
      let%map binder = Env.index_to_name ctx x in
      let pvar = Fmt.str "%s.%a" binder Pretty.pp_packet p in
      let const = Smtlib.const pvar in
      let smt =
        if length > !C.maxlen then zero_extend (length - !C.maxlen) const
        else const
      in
      { smt_term = smt;
        dynamic_size = DynamicSize.Dynamic (Fmt.str "%s.length" pvar);
        let_bindings = [];
        constraints = []
      }

  let encode_bv_expr_comparison (ctx : Env.context)
      (f : Smtlib.term -> Smtlib.term -> Smtlib.term) (e1 : Expression.bv)
      (e2 : Expression.bv) =
    let%bind ssize_tm1 = static_size_of_bv_expr !C.maxlen e1 in
    let%bind ssize_tm2 = static_size_of_bv_expr !C.maxlen e2 in
    let len = max ssize_tm1 ssize_tm2 in
    let%bind { smt_term = e1_smt;
               dynamic_size = e1_dsize;
               let_bindings = e1_bindings;
               constraints = e1_constraints
             } =
      bv_expr_to_smt e1 len ctx
    in
    let%map { smt_term = e2_smt;
              dynamic_size = e2_dsize;
              let_bindings = e2_bindings;
              constraints = e2_constraints
            } =
      bv_expr_to_smt e2 len ctx
    in
    match (e1_dsize, e2_dsize) with
    | Static n, Static m ->
      assert (n = m);
      f e1_smt e2_smt
    | _ ->
      let constr =
        List.fold (e1_constraints @ e2_constraints) ~init:(f e1_smt e2_smt)
          ~f:(fun acc c -> Smtlib.and_ c acc)
      in
      List.fold (e1_bindings @ e2_bindings) ~init:constr ~f:(fun acc l ->
          Smtlib.Let (fst l, snd l, acc))

  let encode_bv_expr_eq (e1_smt : Smtlib.term) (e2_smt : Smtlib.term) =
    Smtlib.equals e1_smt e2_smt

  let encode_bv_expr_gt (e1_smt : Smtlib.term) (e2_smt : Smtlib.term) =
    Smtlib.bvugt e1_smt e2_smt

  let encode_arith_expr_comparison (ctx : Env.context)
      (f : Smtlib.term -> Smtlib.term -> Smtlib.term) (e1 : Expression.arith)
      (e2 : Expression.arith) =
    let%bind max_tm1 = max_arith_value e1 !C.maxlen in
    let%bind max_tm2 = max_arith_value e2 !C.maxlen in
    let static_size = min_bit_width (max max_tm1 max_tm2) in
    let%bind e1_enc = arith_expr_to_smt ctx static_size e1 in
    let%map e2_enc = arith_expr_to_smt ctx static_size e2 in
    let init =
      List.fold (e1_enc.constraints @ e2_enc.constraints)
        ~init:(f e1_enc.smt_term e2_enc.smt_term) ~f:(fun acc c ->
          Smtlib.and_ c acc)
    in
    List.fold (e1_enc.let_bindings @ e2_enc.let_bindings) ~init ~f:(fun acc l ->
        Smtlib.Let (fst l, snd l, acc))

  let rec form_to_smt (header_table : HeaderTable.t) (ctx : Env.context)
      (form : Formula.t) =
    match form with
    | True -> Ok true_
    | False -> Ok false_
    | IsValid (x, inst) -> valid_expr_to_smt ctx x inst
    | Eq (ArithExpr e1, ArithExpr e2) ->
      encode_arith_expr_comparison ctx Smtlib.equals e1 e2
    | Eq (BvExpr e1, BvExpr e2) ->
      encode_bv_expr_comparison ctx encode_bv_expr_eq e1 e2
    | Gt (ArithExpr e1, ArithExpr e2) ->
      encode_arith_expr_comparison ctx Smtlib.bvugt e1 e2
    | Gt (BvExpr e1, BvExpr e2) ->
      encode_bv_expr_comparison ctx encode_bv_expr_gt e1 e2
    | Eq _ | Gt _ ->
      Error
        (`EncodingError "Expressions must have the same type to be comparable.")
    | Neg e ->
      let%map exp_smt = form_to_smt header_table ctx e in
      Smtlib.not_ exp_smt
    | And (e1, e2) ->
      let%bind e1_smt = form_to_smt header_table ctx e1 in
      let%map e2_smt = form_to_smt header_table ctx e2 in
      Smtlib.and_ e1_smt e2_smt
    | Or (e1, e2) ->
      let%bind e1_smt = form_to_smt header_table ctx e1 in
      let%map e2_smt = form_to_smt header_table ctx e2 in
      Smtlib.or_ e1_smt e2_smt
    | Implies (e1, e2) ->
      let%bind e1_smt = form_to_smt header_table ctx e1 in
      let%map e2_smt = form_to_smt header_table ctx e2 in
      Smtlib.implies e1_smt e2_smt

  let rec heap_type_to_smt (ht : HeaderTable.t) (ctx : Env.context)
      (x0 : string) (hty : HeapType.t) =
    match hty with
    | Nothing -> return (Smtlib.bool_to_term false)
    | Top -> return (Smtlib.bool_to_term true)
    | Choice (hty1, hty2) ->
      let%bind smt_hty1 = heap_type_to_smt ht ctx x0 hty1 in
      let%map smt_hty2 = heap_type_to_smt ht ctx x0 hty2 in
      Smtlib.or_ smt_hty1 smt_hty2
    | Sigma (x, hty1, hty2) ->
      let x1 = x ^ "_l" in
      let x2 = x ^ "_r" in
      let%bind smt_hty1 = heap_type_to_smt ht ctx x1 hty1 in
      let ctx' = Env.add_binding ctx x1 (Env.VarBind hty1) in
      let%map smt_hty2 = heap_type_to_smt ht ctx' x2 hty2 in
      ands
        [ smt_hty1;
          smt_hty2;
          pktbounds x0;
          pktbounds x1;
          pktbounds x2;
          append x0 x1 x2 ht
        ]
    | Refinement (x1, hty, e) ->
      let%bind smt_hty = heap_type_to_smt ht ctx x1 hty in
      let ctx' = Env.add_binding ctx x1 (Env.VarBind hty) in
      let%map smt_exp = form_to_smt ht ctx' e in
      ands [ equal x0 x1 ht; smt_hty; smt_exp; pktbounds x0; pktbounds x1 ]
    | Substitution (hty1, x2, hty2) ->
      let ctx' = Env.add_binding ctx x2 (Env.VarBind hty2) in
      let%bind smt_hty1 = heap_type_to_smt ht ctx' x0 hty1 in
      let%map smt_hty2 = heap_type_to_smt ht ctx x2 hty2 in
      ands [ smt_hty1; smt_hty2; pktbounds x0; pktbounds x2 ]
  let set_maxlen len = 
    C.maxlen := len
end

module DefaultEncoding = FixedWidthBitvectorEncoding (struct
  let maxlen = ref(1500)
end)
