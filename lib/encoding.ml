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

let rec freshen_binders (hty : HeapType.t)
    (pick_unique_name : string -> string) : HeapType.t =
  let open HeapType in
  match hty with
  | Nothing -> Nothing
  | Empty -> Empty
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
    | _ -> Error "Dont know how to encode bit variables")

let bv_to_string v =
  let%map bs = to_string_aux v in
  Printf.sprintf "0b%s" (String.rev bs)

let bv_to_smt v size =
  let l = Syntax.BitVector.sizeof v in
  if l = 0 then
    Error "Cannot encode an empty bitvector"
  else
    let%map s = bv_to_string v in
    let i = Int.of_string s in
    Smtlib.bv i size

type dynamic_size =
  | Dynamic of string
  | Static of int
  | Sum of dynamic_size * dynamic_size

let rec max_value_dynamic_size (ds : dynamic_size) (maxlen : int) =
  match ds with
  | Dynamic _ -> maxlen
  | Static n -> n
  | Sum (n, m) ->
    max_value_dynamic_size n maxlen + max_value_dynamic_size m maxlen

let rec dynamic_size_to_smt (bv : dynamic_size) (len : int) (maxlen : int) =
  match bv with
  | Dynamic d ->
    let const = Smtlib.const d in
    let mbw = min_bit_width maxlen in
    if len > mbw then
      zero_extend (len - mbw) const
    else
      const
  | Static n -> Smtlib.bv n len
  | Sum (s1, s2) ->
    Smtlib.bvadd
      (dynamic_size_to_smt s1 len maxlen)
      (dynamic_size_to_smt s2 len maxlen)

let rec max_arith_value (term : Term.t) (maxlen : int) =
  match term with
  | Num n -> return n
  | Length (_, _) -> return maxlen
  | Plus (tm1, tm2) ->
    let%bind v1 = max_arith_value tm1 maxlen in
    let%map v2 = max_arith_value tm2 maxlen in
    v1 + v2
  | _ -> Error "Not an arithmetic term"

let type_of_term (term : Term.t) =
  match term with
  | Num _
  | Length (_, _)
  | Plus (_, _) ->
    `Arith
  | Minus (_, _)
  | Bv _
  | Concat (_, _)
  | Slice (_, _, _)
  | Packet (_, _) ->
    `Bits

let id_fst_compare (Smtlib.Id x, _) (Smtlib.Id y, _) : int = String.compare x y

let id_dedup = List.dedup_and_sort ~compare:id_fst_compare

let valid_expr_to_smt (ctx : Env.context) (x : var) (inst : Instance.t) =
  let binder = Env.index_to_name ctx x in
  const_valid binder inst.name

module type S = sig
  val equal : string -> string -> HeaderTable.t -> Smtlib.term

  val header_type_to_smt :
    HeaderTable.t ->
    Env.context ->
    string ->
    HeapType.t ->
    (Smtlib.term, string) result

  val smt_consts :
    HeapType.t ->
    string ->
    HeaderTable.t ->
    (Smtlib.identifier * Smtlib.sort) list
end

module type Config = sig
  val maxlen : int
end

module FixedWidthBitvectorEncoding (C : Config) : S = struct
  let consts (var : string) (ht : HeaderTable.t) =
    let pkt_size = min_bit_width C.maxlen in
    HeaderTable.to_list ht
    |> List.fold ~init:[] ~f:(fun acc inst ->
           let inst_size = Instance.sizeof inst in
           (id_valid var inst.name, Smtlib.bool_sort)
           :: (id_access var inst.name, Smtlib.BitVecSort inst_size) :: acc)
    |> List.append
         [ (id_access var "pkt_in", Smtlib.BitVecSort C.maxlen);
           (id_pkt_length var "pkt_in", Smtlib.BitVecSort pkt_size);
           (id_access var "pkt_out", Smtlib.BitVecSort C.maxlen);
           (id_pkt_length var "pkt_out", Smtlib.BitVecSort pkt_size)
         ]

  let smt_consts (hty : HeapType.t) (x0 : string)
      (header_table : HeaderTable.t) =
    let rec smt_consts_aux (hty : HeapType.t)
        (acc : (Smtlib.identifier * Smtlib.sort) list) =
      match hty with
      | Nothing
      | Empty
      | Top ->
        acc
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
             :: Smtlib.equals (inst_const x) (inst_const y) :: acc)
    in
    ands @@ List.join [ pkt_terms; inst_terms ]

  let pktbounds (x : string) : Smtlib.term =
    let open Smtlib in
    let pkt_size = min_bit_width C.maxlen in

    let pkt_in = const_pkt_in x in
    let pkt_in_length = const_pkt_in_len x in
    let pkt_out = const_pkt_out x in
    let pkt_out_length = const_pkt_out_len x in
    let len_ok len_const = bvule len_const (bv C.maxlen pkt_size) in
    let value_ok const_len const_pkt =
      let padded = zero_extend (C.maxlen - pkt_size + 1) const_len in
      or_
        (equals const_len (bv 0 pkt_size))
        (bvult (zero_extend 1 const_pkt) (bvshl (bv 1 (C.maxlen + 1)) padded))
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
    let pkt_size = min_bit_width C.maxlen in

    let pkt var = const_access var packet in
    let pkt_len var = const_pkt_len var packet in
    let maxlen_bv = bv C.maxlen pkt_size in
    let len_ok t = bvule t maxlen_bv in
    let newlen =
      bvadd (zero_extend 1 (pkt_len x1)) (zero_extend 1 (pkt_len x2))
    in
    let bounded len_slice =
      ite (len_ok len_slice) len_slice maxlen_bv
    in
    let padded = zero_extend (C.maxlen - pkt_size) (pkt_len x1) in
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
                   (equals (extract pkt_size pkt_size const_binder_len) (bv 0 1))
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
             disjoint inst
             :: append_valid inst :: hdreq x0 x1 inst :: hdreq x0 x2 inst :: acc)
    in
    ands
    @@ [ append_packet x0 x1 x2 "pkt_in"; append_packet x0 x1 x2 "pkt_out" ]
    @ eqs

  let rec static_size_of_term (term : Term.t) (maxlen : int) =
    match term with
    | Num _
    | Length (_, _)
    | Plus (_, _) ->
      Error "Can't compute static size for arithmetic terms."
    | Minus (tm1, tm2) ->
      let%bind size_tm1 = static_size_of_term tm1 maxlen in
      let%map size_tm2 = static_size_of_term tm2 maxlen in
      assert(size_tm1 = size_tm2);
      size_tm1
    | Bv Nil -> return 0
    | Bv bv -> return (Syntax.BitVector.sizeof bv)
    | Concat (tm1, tm2) ->
      let%bind size_tm1 = static_size_of_term tm1 maxlen in
      let%map size_tm2 = static_size_of_term tm2 maxlen in
      size_tm1 + size_tm2
    | Slice (_, l, r) -> return (r - l)
    | Packet (_, _) -> return maxlen

  let rec term_to_smt (term : Term.t) (length : int) (ctx : Env.context) =
    match term with
    | Num n -> return (Smtlib.bv n length, Static length)
    | Length (x, p) ->
      assert (length >= min_bit_width C.maxlen);
      let binder = Env.index_to_name ctx x in
      let smt_pkt =
        Smtlib.const (Fmt.str "%s.%a.length" binder Pretty.pp_packet p)
      in
      let ssize_diff = length - min_bit_width C.maxlen in
      let smt =
        if ssize_diff > 0 then
          zero_extend ssize_diff smt_pkt
        else
          smt_pkt
      in
      return (smt, Static length)
    | Plus (tm1, tm2) ->
      let%bind tm1_smt, _ = term_to_smt tm1 length ctx in
      let%map tm2_smt, _ = term_to_smt tm2 length ctx in
      (Smtlib.bvadd tm1_smt tm2_smt, Static length)
    | Minus (tm1, tm2) ->
      let%bind tm1_smt, _ = term_to_smt tm1 length ctx in
      let%map tm2_smt, _ = term_to_smt tm2 length ctx in
      (Smtlib.bvsub tm1_smt tm2_smt, Static length)
    | Bv v ->
      let%map bv_smt = bv_to_smt v length in
      let size = Syntax.BitVector.sizeof v in
      (bv_smt, Static size)
    | Concat (tm1, tm2) ->
      let%bind tm1_smt, tm1_size = term_to_smt tm1 length ctx in
      let%map tm2_smt, tm2_size = term_to_smt tm2 length ctx in
      let tm1_size_smt = dynamic_size_to_smt tm1_size length C.maxlen in
      (* TODO: Handle the case where tm1 is empty *)
      Smtlib.
        (bvor tm1_smt (bvshl tm2_smt tm1_size_smt), Sum (tm1_size, tm2_size))
    (* If the instance slice covers the whole range, we can just use the
       variable *)
    | Slice (Instance (x, inst), 0, r) when r = Instance.sizeof inst ->
      let name = Env.index_to_name ctx x in
      let svar = Smtlib.const (Fmt.str "%s.%s" name inst.name) in
      let size_diff = length - r in
      let smt =
        if size_diff > 0 then
          zero_extend size_diff svar
        else
          svar
      in
      return (smt, Static r)
    | Slice (s, l, r) ->
      assert (length >= r - l);
      let svar = Fmt.str "%a" (Pretty.pp_sliceable ctx) s in
      let extract = Smtlib.(extract (r - 1) l (const svar)) in
      let size_diff = length - (r - l) in
      let smt =
        if size_diff > 0 then
          zero_extend size_diff extract
        else
          extract
      in
      return (smt, Static (r - l))
    | Packet (x, p) ->
      let binder = Env.index_to_name ctx x in
      let pvar = Fmt.str "%s.%a" binder Pretty.pp_packet p in
      let const = Smtlib.const pvar in
      let smt =
        if length > C.maxlen then
          zero_extend (length - C.maxlen) const
        else
          const
      in
      return (smt, Dynamic (Fmt.str "%s.length" pvar))

  let encode_term_comparison (tm1 : Term.t) (tm2 : Term.t) (op : [< `EQ | `GT ])
      (ctx : Env.context) =
    match (type_of_term tm1, type_of_term tm2) with
    | `Arith, `Arith -> (
      let%bind max_tm1 = max_arith_value tm1 C.maxlen in
      let%bind max_tm2 = max_arith_value tm2 C.maxlen in
      let static_size = min_bit_width (max max_tm1 max_tm2) in
      let%bind tm1_smt, _ = term_to_smt tm1 static_size ctx in
      let%bind tm2_smt, _ = term_to_smt tm2 static_size ctx in
      match op with
      | `EQ -> return (Smtlib.equals tm1_smt tm2_smt)
      | `GT -> return (Smtlib.bvugt tm1_smt tm2_smt))
    | `Bits, `Bits -> (
      let%bind ssize_tm1 = static_size_of_term tm1 C.maxlen in
      let%bind ssize_tm2 = static_size_of_term tm2 C.maxlen in
      let len = max ssize_tm1 ssize_tm2 in

      let%bind tm1_smt, tm1_dsize = term_to_smt tm1 len ctx in
      let%map tm2_smt, tm2_dsize = term_to_smt tm2 len ctx in
      let eq_tm12 = Smtlib.equals tm1_smt tm2_smt in
      match (tm1_dsize, tm2_dsize) with
      | Static n, Static m ->
        if n <> m then
          false_
        else
          eq_tm12
      | _ -> (
        let dyn_len =
          min_bit_width
            (max
               (max_value_dynamic_size tm1_dsize C.maxlen)
               (max_value_dynamic_size tm2_dsize C.maxlen))
        in
        let tm1_size_smt = dynamic_size_to_smt tm1_dsize dyn_len C.maxlen in
        let tm2_size_smt = dynamic_size_to_smt tm2_dsize dyn_len C.maxlen in
        match op with
        | `EQ ->
          Smtlib.(
            and_
              (equals tm1_size_smt tm2_size_smt)
              (or_ (equals (bv 0 dyn_len) tm1_size_smt) eq_tm12))
        | `GT ->
          (* TODO: Case `GT should use bvugt? *)
          Smtlib.(
            and_
              (equals tm1_size_smt tm2_size_smt)
              (or_
                 (equals (bv 0 dyn_len) tm1_size_smt)
                 (Smtlib.bvugt tm1_smt tm2_smt)))))
    | _ -> Error "Terms must have the same type to be comparable."

  let rec exp_to_smt (header_table : HeaderTable.t) (ctx : Env.context)
      (expr : Expression.t) =
    match expr with
    | True -> Ok true_
    | False -> Ok false_
    | IsValid (x, inst) -> return (valid_expr_to_smt ctx x inst)
    | TmEq (tm1, tm2) -> encode_term_comparison tm1 tm2 `EQ ctx
    | TmGt (tm1, tm2) -> encode_term_comparison tm1 tm2 `GT ctx
    (* | Neg (IsValid (x, inst)) -> return (Smtlib.not_ (valid_expr_to_smt x
       inst)) *)
    | Neg e ->
      let%map exp_smt = exp_to_smt header_table ctx e in
      Smtlib.not_ exp_smt
    | And (e1, e2) ->
      let%bind e1_smt = exp_to_smt header_table ctx e1 in
      let%map e2_smt = exp_to_smt header_table ctx e2 in
      Smtlib.and_ e1_smt e2_smt
    | Or (e1, e2) ->
      let%bind e1_smt = exp_to_smt header_table ctx e1 in
      let%map e2_smt = exp_to_smt header_table ctx e2 in
      Smtlib.or_ e1_smt e2_smt
    | Implies (e1, e2) ->
      let%bind e1_smt = exp_to_smt header_table ctx e1 in
      let%map e2_smt = exp_to_smt header_table ctx e2 in
      Smtlib.implies e1_smt e2_smt

  let rec header_type_to_smt (ht : HeaderTable.t) (ctx : Env.context)
      (x0 : string) (hty : HeapType.t) =
    match hty with
    | Nothing -> return (Smtlib.bool_to_term false)
    | Empty ->
      String.Map.keys ht
      |> List.fold ~init:true_ ~f:(fun acc inst ->
             Smtlib.and_ (Smtlib.not_ (const_valid x0 inst)) acc)
      |> return
    | Top -> return (Smtlib.bool_to_term true)
    | Choice (hty1, hty2) ->
      let%bind smt_hty1 = header_type_to_smt ht ctx x0 hty1 in
      let%map smt_hty2 = header_type_to_smt ht ctx x0 hty2 in
      Smtlib.or_ smt_hty1 smt_hty2
    | Sigma (x, hty1, hty2) ->
      let x1 = x ^ "_l" in
      let x2 = x ^ "_r" in
      let%bind smt_hty1 = header_type_to_smt ht ctx x1 hty1 in
      let ctx' = Env.add_binding ctx x1 (Env.VarBind hty1) in
      let%map smt_hty2 = header_type_to_smt ht ctx' x2 hty2 in
      ands
        [ smt_hty1;
          smt_hty2;
          pktbounds x0;
          pktbounds x1;
          pktbounds x2;
          append x0 x1 x2 ht
        ]
    | Refinement (x1, hty, e) ->
      let%bind smt_hty = header_type_to_smt ht ctx x1 hty in
      let ctx' = Env.add_binding ctx x1 (Env.VarBind hty) in
      let%map smt_exp = exp_to_smt ht ctx' e in
      ands [ equal x0 x1 ht; smt_hty; smt_exp; pktbounds x0; pktbounds x1 ]
    | Substitution (hty1, x2, hty2) ->
      let ctx' = Env.add_binding ctx x2 (Env.VarBind hty2) in
      let%bind smt_hty1 = header_type_to_smt ht ctx' x0 hty1 in
      let%map smt_hty2 = header_type_to_smt ht ctx x2 hty2 in
      ands [ smt_hty1; smt_hty2; pktbounds x0; pktbounds x2 ]
end

module SimpleEncoding : S = struct
  let equal (x : string) (y : string) (ht : Syntax.HeaderTable.t) =
    let inst_terms =
      String.Map.keys ht
      |> List.fold ~init:[] ~f:(fun acc elem ->
             let inst_const id = const_access id elem in
             let valid_const id = const_valid id elem in
             Smtlib.equals (valid_const x) (valid_const y)
             :: Smtlib.equals (inst_const x) (inst_const y) :: acc)
    in
    ands inst_terms

  (* TODO: Shared *)
  let hdreq (x : string) (y : string) (inst : string) : Smtlib.term =
    let open Smtlib in
    let eq = equals (const_access x inst) (const_access y inst) in
    implies (const_valid y inst) eq

  let append (x0 : string) (x1 : string) (x2 : string)
      (ht : Syntax.HeaderTable.t) =
    let open Smtlib in
    let append_valid inst =
      equals (const_valid x0 inst)
        (xor (const_valid x1 inst) (const_valid x2 inst))
    in
    let eqs =
      String.Map.keys ht
      |> List.fold ~init:[] ~f:(fun acc inst ->
             append_valid inst :: hdreq x0 x1 inst :: hdreq x0 x2 inst :: acc)
    in
    ands eqs

  let rec static_size_of_term (term : Term.t) =
    match term with
    | Num _
    | Length (_, _)
    | Plus (_, _) ->
      Error "Can't compute static size for arithmetic terms."
    | Minus (tm1, tm2) ->
      let%bind size_tm1 = static_size_of_term tm1 in
      let%map size_tm2 = static_size_of_term tm2 in
      assert(size_tm1 = size_tm2);
      size_tm1
    | Bv Nil -> return 0
    | Bv bv -> return (Syntax.BitVector.sizeof bv)
    | Concat (tm1, tm2) ->
      let%bind size_tm1 = static_size_of_term tm1 in
      let%map size_tm2 = static_size_of_term tm2 in
      size_tm1 + size_tm2
    | Slice (_, l, r) -> return (r - l)
    | Packet (_, _) -> Error "Can't compute static size for arithmetic terms."

  let rec header_type_to_smt (ht : HeaderTable.t) (ctx : Env.context)
      (x0 : string) (hty : HeapType.t) =
    match hty with
    | Nothing -> return (Smtlib.bool_to_term false)
    | Empty ->
      String.Map.keys ht
      |> List.fold ~init:true_ ~f:(fun acc inst ->
             Smtlib.and_ (Smtlib.not_ (const_valid x0 inst)) acc)
      |> return
    | Top -> return (Smtlib.bool_to_term true)
    | Choice (hty1, hty2) ->
      let%bind smt_hty1 = header_type_to_smt ht ctx x0 hty1 in
      let%map smt_hty2 = header_type_to_smt ht ctx x0 hty2 in
      Smtlib.or_ smt_hty1 smt_hty2
    | Sigma (x, hty1, hty2) ->
      let x1 = x ^ "_l" in
      let x2 = x ^ "_r" in
      let%bind smt_hty1 = header_type_to_smt ht ctx x1 hty1 in
      let ctx' = Env.add_binding ctx x1 (Env.VarBind hty1) in
      let%map smt_hty2 = header_type_to_smt ht ctx' x2 hty2 in
      ands [ smt_hty1; smt_hty2; append x0 x1 x2 ht ]
    | Refinement (x1, hty, e) ->
      let%bind smt_hty = header_type_to_smt ht ctx x1 hty in
      let ctx' = Env.add_binding ctx x1 (Env.VarBind hty) in
      let%map smt_exp = exp_to_smt ht ctx' e in
      ands [ equal x0 x1 ht; smt_hty; smt_exp ]
    | Substitution (hty1, x2, hty2) ->
      let ctx' = Env.add_binding ctx x2 (Env.VarBind hty2) in
      let%bind smt_hty1 = header_type_to_smt ht ctx' x0 hty1 in
      let%map smt_hty2 = header_type_to_smt ht ctx x2 hty2 in
      ands [ smt_hty1; smt_hty2 ]

  and exp_to_smt (header_table : HeaderTable.t) (ctx : Env.context)
      (expr : Expression.t) =
    match expr with
    | True -> return true_
    | False -> return false_
    | IsValid (x, inst) ->
      (* let valid_str = Fmt.str "%a" (Pretty.pp_expr ctx) valid_exp in return
         (Smtlib.equals (Smtlib.const valid_str) (Smtlib.bv 1 1)) *)
      return (valid_expr_to_smt ctx x inst)
    | TmEq (tm1, tm2) -> encode_term_comparison tm1 tm2 `EQ ctx
    | TmGt (tm1, tm2) -> encode_term_comparison tm1 tm2 `GT ctx
    (* | Neg (IsValid (_, _) as valid_exp) -> let valid_str = Fmt.str "%a"
       (Pretty.pp_expr ctx) valid_exp in return (Smtlib.equals (Smtlib.const
       valid_str) (Smtlib.bv 0 1)) *)
    | Neg e ->
      let%map exp_smt = exp_to_smt header_table ctx e in
      Smtlib.not_ exp_smt
    | And (e1, e2) ->
      let%bind e1_smt = exp_to_smt header_table ctx e1 in
      let%map e2_smt = exp_to_smt header_table ctx e2 in
      Smtlib.and_ e1_smt e2_smt
    | Or (e1, e2) ->
      let%bind e1_smt = exp_to_smt header_table ctx e1 in
      let%map e2_smt = exp_to_smt header_table ctx e2 in
      Smtlib.or_ e1_smt e2_smt
    | Implies (e1, e2) ->
      let%bind e1_smt = exp_to_smt header_table ctx e1 in
      let%map e2_smt = exp_to_smt header_table ctx e2 in
      Smtlib.implies e1_smt e2_smt

  and encode_term_comparison (tm1 : Term.t) (tm2 : Term.t) (op : [< `EQ | `GT ])
      (ctx : Env.context) =
    match (type_of_term tm1, type_of_term tm2) with
    | `Arith, `Arith ->
      Error "TODO Arith"
      (* ( let%bind max_tm1 = max_arith_value tm1 C.maxlen in let%bind max_tm2 =
         max_arith_value tm2 C.maxlen in let static_size = min_bit_width (max
         max_tm1 max_tm2) in let%bind tm1_smt, _ = term_to_smt tm1 static_size
         ctx in let%bind tm2_smt, _ = term_to_smt tm2 static_size ctx in match
         op with | `EQ -> return (Smtlib.equals tm1_smt tm2_smt) | `GT -> return
         (Smtlib.bvugt tm1_smt tm2_smt) ) *)
    | `Bits, `Bits -> (
      match op with
      | `EQ
      | `GT ->
        let%bind ssize_tm1 = static_size_of_term tm1 in
        let%bind ssize_tm2 = static_size_of_term tm2 in
        let len = max ssize_tm1 ssize_tm2 in
        let%bind tm1_smt, _ = term_to_smt tm1 len ctx in
        let%map tm2_smt, _ = term_to_smt tm2 len ctx in
        (* let eq_tm12 = Smtlib.equals tm1_smt tm2_smt in *)
        (* match (tm1_dsize, tm2_dsize) with *)
        (* | Static n, Static m -> *)
        (* if n <> m then *)
        (* false_ *)
        (* else *)
        (* eq_tm12 *)
        (* | _ -> *)
        (* let dyn_len = *)
        (* min_bit_width *)
        (* (max *)
        (* (max_value_dynamic_size tm1_dsize C.maxlen) *)
        (* (max_value_dynamic_size tm2_dsize C.maxlen)) *)
        (* in *)
        (* let tm1_size_smt = dynamic_size_to_smt tm1_dsize dyn_len C.maxlen in *)
        (* let tm2_size_smt = dynamic_size_to_smt tm2_dsize dyn_len C.maxlen in *)
        (* Smtlib.( *)
        (* and_ *)
        (* (equals tm1_size_smt tm2_size_smt) *)
        (* (or_ (equals (bv 0 dyn_len) tm1_size_smt) eq_tm12)) )*)
        Smtlib.(equals tm1_smt tm2_smt))
    | _ -> Error "Terms must have the same type to be comparable."

  and term_to_smt (term : Term.t) (length : int) (ctx : Env.context) =
    match term with
    | Num n -> return (Smtlib.bv n length, Static length)
    | Length (_, _) ->
      Error "Simple encoding does not support packet length terms."
    | Plus (tm1, tm2) ->
      let%bind tm1_smt, _ = term_to_smt tm1 length ctx in
      let%map tm2_smt, _ = term_to_smt tm2 length ctx in
      (Smtlib.bvadd tm1_smt tm2_smt, Static length)
    | Minus (tm1, tm2) ->
      let%bind tm1_smt, _ = term_to_smt tm1 length ctx in
      let%map tm2_smt, _ = term_to_smt tm2 length ctx in
      (Smtlib.bvsub tm1_smt tm2_smt, Static length)
    | Bv v ->
      let%map bv_smt = bv_to_smt v length in
      let size = Syntax.BitVector.sizeof v in
      (bv_smt, Static size)
    | Concat (_, _) -> Error "TODO"
    (* let%bind tm1_smt, tm1_size = term_to_smt tm1 length ctx in let%map
       tm2_smt, tm2_size = term_to_smt tm2 length ctx in let tm1_size_smt =
       dynamic_size_to_smt tm1_size length C.maxlen in Smtlib. (bvor tm1_smt
       (bvshl tm2_smt tm1_size_smt), Sum (tm1_size, tm2_size)) *)
    (* If the instance slice covers the whole range, we can just use the
       variable *)
    | Slice (Instance (x, inst), 0, r) when r = Instance.sizeof inst ->
      let name = Env.index_to_name ctx x in
      let svar = Smtlib.const (Fmt.str "%s.%s" name inst.name) in
      let size_diff = length - r in
      let smt =
        if size_diff > 0 then
          zero_extend size_diff svar
        else
          svar
      in
      return (smt, Static r)
    | Slice (s, l, r) ->
      assert (length >= r - l);
      let svar = Fmt.str "%a" (Pretty.pp_sliceable ctx) s in
      let extract = Smtlib.(extract (r - 1) l (const svar)) in
      let size_diff = length - (r - l) in
      let smt =
        if size_diff > 0 then
          zero_extend size_diff extract
        else
          extract
      in
      return (smt, Static (r - l))
    | Packet (_, _) -> Error "Simple encoding does not support packet terms."

  let consts (var : string) (ht : HeaderTable.t) =
    HeaderTable.to_list ht
    |> List.fold ~init:[] ~f:(fun acc inst ->
           let inst_size = Instance.sizeof inst in
           (id_valid var inst.name, Smtlib.bool_sort)
           :: (id_access var inst.name, Smtlib.BitVecSort inst_size) :: acc)

  let smt_consts (hty : HeapType.t) (x0 : string)
      (header_table : HeaderTable.t) =
    let rec smt_consts_aux (hty : HeapType.t)
        (acc : (Smtlib.identifier * Smtlib.sort) list) =
      match hty with
      | Nothing
      | Empty
      | Top ->
        acc
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
end

module DefaultEncoding = FixedWidthBitvectorEncoding (struct
  let maxlen = 1500
end)
