open Core_kernel
open Alcotest
open Pi4
open Syntax
open Formula
open HeapType

let eth_inst = Test_utils.mk_inst "eth" [ ("smac", 48) ]

(*; "dmac", 48; "type", 16])*)

let ipv4_inst = Test_utils.mk_inst "ipv4" [ ("src", 32); ("dst", 32) ]
let header_table = HeaderTable.populate [ eth_inst; ipv4_inst ]
let init_ctx = []
let maxlen = 32

module TestConfig = struct
  let verbose = true

  let maxlen = ref(32)
end

module Test = Test_utils.TestRunner (TestConfig)

let hty_empty = HeapType.empty header_table "x"
let hty_inst inst ht = HeapType.instance inst ht "x"

(* let test_htyeqv ?(header_table = header_table) hty1 hty2 = make_prover "z3";
   htyeqv header_table init_ctx maxlen hty1 hty2 *)

let test_eqv_nothing () = Test.is_equiv Nothing Nothing [] header_table

let test_neqv_empty_nothing () =
  Test.not_equiv hty_empty Nothing [] header_table

let test_nothing_neqv_empty () =
  Test.not_equiv Nothing hty_empty [] header_table

let test_eqv_empty () = Test.is_equiv hty_empty hty_empty [] header_table

let test_eqv_choice_nothing () =
  Test.is_equiv (Choice (hty_empty, Nothing)) hty_empty [] header_table

let test_eqv_choice_nothing2 () =
  Test.is_equiv
    (Choice (hty_empty, Choice (Nothing, Nothing)))
    hty_empty [] header_table

let test_eqv_header () =
  Test.is_equiv
    (hty_inst eth_inst header_table)
    (hty_inst eth_inst header_table)
    [] header_table

let test_eqv_choice_idem () =
  let h = hty_inst eth_inst header_table in
  let c h1 h2 = Choice (h1, h2) in
  let lhs = c h h in
  let rhs = h in
  Test.is_equiv lhs rhs [] header_table

let test_eqv_choice_ACI () =
  let h_inst = Test_utils.mk_inst "h" [ ("h1", 4) ] in
  let g_inst = Test_utils.mk_inst "g" [ ("g1", 4) ] in
  let f_inst = Test_utils.mk_inst "f" [ ("f1", 4) ] in
  let ht = HeaderTable.populate [ h_inst; g_inst; f_inst ] in
  let hty_inst_local inst = HeapType.weak_instance inst "x" in
  let h = hty_inst_local h_inst in
  let g = hty_inst_local g_inst in
  let f = hty_inst_local f_inst in
  let c h1 h2 = Choice (h1, h2) in
  let lhs = c h @@ c h @@ c g f in
  let rhs = c f @@ c h g in

  Test.is_equiv lhs rhs [] ht

let test_eqv_refine_alpha () =
  let h_inst = Test_utils.mk_inst "h" [ ("f", 32) ] in
  let ht = HeaderTable.populate [ h_inst ] in
  let href_x =
    Refinement
      ( "x",
        hty_inst h_inst ht,
        Eq (Expression.bit_access (Packet (0, PktIn)) 0, BvExpr (bv_s "1")) )
  in
  let href_y =
    Refinement
      ( "y",
        hty_inst h_inst ht,
        Eq (Expression.bit_access (Packet (0, PktIn)) 0, BvExpr (bv_s "1")) )
  in
  Test.is_equiv href_x href_y [] ht

let test_eqv_refine_ident () =
  let h_inst = Test_utils.mk_inst "h" [ ("f", 32) ] in
  let ht = HeaderTable.populate [ h_inst ] in
  let href =
    Refinement
      ( "x",
        hty_inst h_inst ht,
        Eq (Expression.bit_access (Packet (0, PktIn)) 0, BvExpr (bv_s "1")) )
  in
  Test.is_equiv href href [] ht

let test_eqv_sigma () =
  let lhs =
    Sigma
      ( "g",
        Refinement
          ( "y",
            hty_inst eth_inst header_table,
            Eq (ArithExpr (Length (0, PktIn)), ArithExpr (Num 2)) ),
        Refinement
          ("z", hty_empty, Eq (ArithExpr (Length (0, PktIn)), ArithExpr (Num 2)))
      )
  in
  let rhs =
    Refinement
      ( "x",
        hty_inst eth_inst header_table,
        Eq (ArithExpr (Length (0, PktIn)), ArithExpr (Num 4)) )
  in
  Test.is_equiv lhs rhs [] header_table

let test_eqv_sigma_self () =
  let hty =
    Sigma
      ( "x",
        Refinement
          ( "y",
            hty_inst eth_inst header_table,
            And
              ( Eq (ArithExpr (Length (0, PktIn)), ArithExpr (Num 0)),
                Eq (ArithExpr (Length (0, PktOut)), ArithExpr (Num 0)) ) ),
        hty_empty )
  in
  Test.is_equiv hty hty [] header_table

let test_eqv_fixed_pktin () =
  let s = Refinement ("x", hty_empty, pkt_eq_s (0, PktIn) "0101") in
  let t =
    Refinement
      ( "x",
        hty_empty,
        And
          ( Eq (BvExpr (Slice (Packet (0, PktIn), 0, 4)), BvExpr (bv_s "0101")),
            Eq (ArithExpr (Length (0, PktIn)), ArithExpr (Num 4)) ) )
  in
  Test.is_equiv s t [] header_table

let test_pkt_length_gt_n () =
  let hty =
    Refinement
      ("x", hty_empty, Eq (ArithExpr (Length (0, PktIn)), ArithExpr (Num 4)))
  in
  Test.not_equiv
    (Refinement ("y", hty, Gt (ArithExpr (Length (0, PktIn)), ArithExpr (Num 2))))
    Nothing [] header_table

let parse_header_type hty_str =
  Pi4.Parsing.parse_heap_type header_table [] hty_str

let test_pkt_length_gt2 () =
  let hty =
    parse_header_type
      "{x:{y:\\empty | y.pkt_in.length == 4} | x.pkt_in.length > 2}"
  in
  Test.not_equiv hty Nothing [] header_table

let test_pkt_length_gt_n_fails () =
  let hty =
    Refinement
      ("x", hty_empty, Eq (ArithExpr (Length (0, PktIn)), ArithExpr (Num 4)))
  in
  Test.is_equiv
    (Refinement ("y", hty, Gt (ArithExpr (Length (0, PktIn)), ArithExpr (Num 4))))
    Nothing [] header_table

let test_refine_false_eqv_nothing () =
  let hty = Refinement ("x", hty_empty, False) in
  Test.is_equiv hty Nothing [] header_table

let test_refine_false_pred_eqv_nothing () =
  let hty =
    Refinement
      ( "x",
        hty_empty,
        Eq (ArithExpr (Plus (Length (0, PktIn), Num 1)), ArithExpr (Num 0)) )
  in
  Test.is_equiv hty Nothing [] header_table

let test_refine_false_pred_eqv_nothing2 () =
  let inner =
    Refinement
      ( "x",
        hty_empty,
        Eq (ArithExpr (Plus (Length (0, PktIn), Num 1)), ArithExpr (Num 0)) )
  in
  let hty =
    Refinement
      ("y", inner, Eq (ArithExpr (Length (0, PktIn)), ArithExpr (Num 0)))
  in
  Test.is_equiv hty Nothing [] header_table

let test_eqv_sigma_inst () =
  let inst = hty_inst eth_inst header_table in
  let sigma =
    Sigma
      ( "x",
        Refinement
          ( "y",
            inst,
            And
              ( Eq (ArithExpr (Length (0, PktIn)), ArithExpr (Num 0)),
                Eq (ArithExpr (Length (0, PktOut)), ArithExpr (Num 0)) ) ),
        hty_empty )
  in
  Test.is_equiv inst sigma [] header_table

let pred_pkt_out_empty binder =
  Eq (ArithExpr (Length (binder, PktOut)), ArithExpr (Num 0))

let pred_pkt_in_empty binder =
  Eq (ArithExpr (Length (binder, PktIn)), ArithExpr (Num 0))

let pred_pkt_in_out_empty binder =
  And (pred_pkt_in_empty binder, pred_pkt_out_empty binder)

let print_hty_eqv expected actual =
  Fmt.pr "@[<v>%a@ should be equivalent to@ %a@]@." (Pretty.pp_header_type [])
    expected (Pretty.pp_header_type []) actual

let test_eqv_concat_choice_nothing () =
  let hty_eth =
    Refinement ("p", hty_inst eth_inst header_table, pred_pkt_in_out_empty 0)
  in
  let hty_ipv4 =
    Sigma
      ( "q",
        Refinement
          ("r", hty_inst ipv4_inst header_table, pred_pkt_in_out_empty 0),
        hty_empty )
  in
  let choice = Choice (Nothing, hty_ipv4) in
  let hty1 = Sigma ("s", hty_eth, choice) in
  let hty2 = Sigma ("q", hty_eth, hty_inst ipv4_inst header_table) in
  Test.is_equiv hty1 hty2 [] header_table

let test_eqv_concat_choice_nothing2 () =
  let hty_eth =
    Refinement ("p", hty_inst eth_inst header_table, pred_pkt_in_out_empty 0)
  in
  let hty_ipv4 =
    Sigma
      ( "q",
        Refinement
          ("r", hty_inst ipv4_inst header_table, pred_pkt_in_out_empty 0),
        hty_empty )
  in
  let choice = Choice (Nothing, hty_ipv4) in
  let hty1 = Sigma ("s", hty_eth, choice) in
  let hty2 = Sigma ("q", hty_eth, hty_inst ipv4_inst header_table) in
  Test.is_equiv hty1 hty2 [] header_table

let test_eqv_concat_choice_nothing3 () =
  let hty_eth =
    Refinement ("z", hty_inst eth_inst header_table, pred_pkt_in_out_empty 0)
  in
  let hty_ipv4 = hty_inst ipv4_inst header_table in
  let choice =
    Choice
      ( Sigma
          ( "y",
            Refinement
              ( "z",
                hty_ipv4,
                And
                  ( Eq
                      ( ArithExpr (Plus (Plus (Length (0, PktIn), Num 1), Num 1)),
                        ArithExpr (Num 0) ),
                    pred_pkt_out_empty 0 ) ),
            hty_empty ),
        Choice
          ( Sigma
              ( "y",
                Refinement
                  ( "y",
                    Refinement
                      ( "z",
                        hty_ipv4,
                        And
                          ( Eq
                              ( ArithExpr (Plus (Length (0, PktIn), Num 1)),
                                ArithExpr (Num 0) ),
                            pred_pkt_out_empty 0 ) ),
                    pred_pkt_in_empty 0 ),
                hty_empty ),
            Choice
              ( Sigma
                  ( "y",
                    Refinement
                      ( "y",
                        Refinement
                          ( "z",
                            hty_ipv4,
                            And
                              ( Eq
                                  ( ArithExpr (Plus (Length (0, PktIn), Num 1)),
                                    ArithExpr (Num 0) ),
                                pred_pkt_out_empty 0 ) ),
                        Eq
                          ( ArithExpr (Plus (Length (0, PktIn), Num 1)),
                            ArithExpr (Num 0) ) ),
                    hty_empty ),
                Sigma
                  ( "y",
                    Refinement
                      ( "y",
                        Refinement
                          ( "y",
                            Refinement ("z", hty_ipv4, pred_pkt_in_out_empty 0),
                            pred_pkt_in_empty 0 ),
                        pred_pkt_in_empty 0 ),
                    hty_empty ) ) ) )
  in
  let hty1 = Sigma ("y", hty_eth, choice) in
  let hty2 = Sigma ("y", hty_eth, hty_ipv4) in
  Test.is_equiv hty1 hty2 [] header_table

let test_eqv_concat_choice_nothing4 () =
  let hty_eth = hty_inst eth_inst header_table in
  let hty_eth_a = Refinement ("a", hty_eth, pred_pkt_in_out_empty 0) in
  let hty_eth_p = Refinement ("p", hty_eth, pred_pkt_in_out_empty 0) in
  let hty_ipv4 = hty_inst ipv4_inst header_table in
  let choice =
    Choice
      ( Sigma
          ( "b",
            Refinement
              ( "c",
                hty_ipv4,
                And
                  ( Eq
                      ( ArithExpr (Plus (Plus (Length (0, PktIn), Num 1), Num 1)),
                        ArithExpr (Num 0) ),
                    pred_pkt_out_empty 0 ) ),
            hty_empty ),
        Choice
          ( Sigma
              ( "d",
                Refinement
                  ( "e",
                    Refinement
                      ( "f",
                        hty_ipv4,
                        And
                          ( Eq
                              ( ArithExpr (Plus (Length (0, PktIn), Num 1)),
                                ArithExpr (Num 0) ),
                            pred_pkt_out_empty 0 ) ),
                    pred_pkt_in_empty 0 ),
                hty_empty ),
            Choice
              ( Sigma
                  ( "g",
                    Refinement
                      ( "h",
                        Refinement
                          ( "i",
                            hty_ipv4,
                            And
                              ( Eq
                                  ( ArithExpr (Plus (Length (0, PktIn), Num 1)),
                                    ArithExpr (Num 0) ),
                                pred_pkt_out_empty 0 ) ),
                        Eq
                          ( ArithExpr (Plus (Length (0, PktIn), Num 1)),
                            ArithExpr (Num 0) ) ),
                    hty_empty ),
                Sigma
                  ( "j",
                    Refinement
                      ( "k",
                        Refinement
                          ( "l",
                            Refinement ("m", hty_ipv4, pred_pkt_in_out_empty 0),
                            pred_pkt_in_empty 0 ),
                        pred_pkt_in_empty 0 ),
                    hty_empty ) ) ) )
  in
  let hty1 = Sigma ("n", hty_eth_a, choice) in
  let hty2 = Sigma ("o", hty_eth_p, hty_ipv4) in
  print_hty_eqv hty1 hty2;
  Test.is_equiv hty1 hty2 [] header_table

let test_sigma_semantic_sugar () =
  let hty_sigma =
    Parsing.parse_heap_type header_table []
      {| 
        Σx:{y:eth|y.pkt_in.length == 0 && y.pkt_out.length == 0}.
          {y:ipv4|y.pkt_in == x.pkt_in && y.pkt_in.length == x.pkt_in.length && y.pkt_out == x.pkt_out && y.pkt_out.length == x.pkt_out.length}
      |}
  in

  let hty_ref =
    Parsing.parse_heap_type header_table []
      {| {x:⊤|x.eth.valid && x.ipv4.valid && x.pkt_in.length==0 && x.pkt_out.length==0}|}
  in

  let hty_subst =
    Parsing.parse_heap_type header_table []
      {|
        ({z:⊤|
          !(r.eth.valid && l.eth.valid) && 
          !(r.ipv4.valid && l.ipv4.valid) && 
          (l.eth.valid || r.eth.valid => z.eth.valid) &&
          (l.ipv4.valid || r.ipv4.valid => z.ipv4.valid) &&
          (l.eth.valid => z.eth==l.eth) && 
          (r.eth.valid => z.eth==r.eth) && 
          (l.ipv4.valid => z.ipv4==l.ipv4) && 
          (r.ipv4.valid => z.ipv4==r.ipv4) &&
          z.pkt_in == l.pkt_in@r.pkt_in &&
          z.pkt_out == l.pkt_out@r.pkt_out &&
          z.pkt_in.length == l.pkt_in.length+r.pkt_in.length &&
          z.pkt_out.length == l.pkt_out.length+r.pkt_out.length}[r ↦ {y:ipv4|y.pkt_in == l.pkt_in && y.pkt_in.length == l.pkt_in.length && y.pkt_out == l.pkt_out && y.pkt_out.length == l.pkt_out.length}]
        )[l ↦ {y:eth|y.pkt_in.length == 0 && y.pkt_out.length == 0}]
      |}
  in

  Test.is_equiv hty_sigma hty_ref [] header_table;
  Test.is_equiv hty_subst hty_ref [] header_table

let test_concat_minus () =
  let inst = Test_utils.mk_inst "h" [ ("ihl", 2); ("ttl", 4); ("flg", 2) ] in
  let ht = HeaderTable.populate [ inst ] in
  let x = Parsing.parse_heap_type ht [] {| {y: ⊤ | y.pkt_in.length > 12 ∧ y.pkt_in[0:12] == 0x35c} |} in
  let ctx = [ ("x", Env.VarBind x) ] in
  let t1 =
    Parsing.parse_heap_type ht ctx
      {|
        {y:⊤ | (y.pkt_in.length + 8) == x.pkt_in.length ∧
                x.pkt_in[0:8]@y.pkt_in == x.pkt_in ∧
                y.pkt_out.length == x.pkt_out.length ∧
                y.pkt_out == x.pkt_out ∧
                y.h[0:2] == x.pkt_in[0:2] ∧
                y.h[2:6] == (x.pkt_in[2:6] - 0x1) ∧
                y.h[6:8] == x.pkt_in[6:8] ∧
                y.h.valid}
      |}
  in
  let t2 =
    Parsing.parse_heap_type ht ctx
      {|
        {y:⊤ | (y.pkt_in.length + 8) == x.pkt_in.length ∧
            x.pkt_in[0:8]@y.pkt_in == x.pkt_in ∧
            y.pkt_out.length == x.pkt_out.length ∧
            y.pkt_out == x.pkt_out ∧
            y.h[0:8] == x.pkt_in[0:2]@(x.pkt_in[2:6] - 0x1)@x.pkt_in[6:8] ∧
            y.h.valid}
      |}
  in
  Test.is_equiv t2 t1 ctx ht

let test_concat_minus_1 () =
  let inst = Test_utils.mk_inst "h" [ ("ihl", 2); ("ttl", 4); ("flg", 2) ] in
  let ht = HeaderTable.populate [ inst ] in
  let ctx = [] in
  let t1 =
    Parsing.parse_heap_type ht ctx
      {|
        {y:⊤ | y.pkt_in.length == 8 ∧ y.pkt_in[0:8] == 0x21}
      |}
  in
  let t2 =
    Parsing.parse_heap_type ht ctx
      {|
        {y:⊤ | y.pkt_in.length == 8 ∧ y.pkt_in[0:8] == (0x22 - 0x01)}
      |}
  in
  Test.is_equiv t2 t1 ctx ht

 
(* Test fails because there is no specific value for y.pkt_in *)
let test_concat_minus_broken () =
  let inst = Test_utils.mk_inst "h" [ ("ihl", 2); ("ttl", 4); ("flg", 2) ] in
  let ht = HeaderTable.populate [ inst ] in
  let x = Parsing.parse_heap_type ht [] {| {y: ⊤ | y.pkt_in.length > 12} |} in
  let ctx = [ ("x", Env.VarBind x) ] in
  let t1 =
    Parsing.parse_heap_type ht ctx
      {|
        {y:⊤ | (y.pkt_in.length + 8) == x.pkt_in.length ∧
                x.pkt_in[0:8]@y.pkt_in == x.pkt_in ∧
                y.pkt_out.length == x.pkt_out.length ∧
                y.pkt_out == x.pkt_out ∧
                y.h[0:2] == x.pkt_in[0:2] ∧
                y.h[2:6] == (x.pkt_in[2:6] - 0x1) ∧
                y.h[6:8] == x.pkt_in[6:8] ∧
                y.h.valid}
      |}
  in
  let t2 =
    Parsing.parse_heap_type ht ctx
      {|
        {y:⊤ | (y.pkt_in.length + 8) == x.pkt_in.length ∧
            x.pkt_in[0:8]@y.pkt_in == x.pkt_in ∧
            y.pkt_out.length == x.pkt_out.length ∧
            y.pkt_out == x.pkt_out ∧
            y.h[0:8] == x.pkt_in[0:2]@(x.pkt_in[2:6] - 0b1)@x.pkt_in[6:8] ∧
            y.h.valid}
      |}
  in
  Test.is_equiv t2 t1 ctx ht

let test_set =
  [ test_case "Header type equivalence ∅" `Quick test_eqv_nothing;
    test_case "Header type equivalence ε" `Quick test_eqv_empty;
    test_case "Header type equivalence h" `Quick test_eqv_header;
    test_case "ε + ∅ should be equivalent to ε" `Quick test_eqv_choice_nothing;
    test_case "ε + ∅ + ∅ should be equivalent to ε" `Quick
      test_eqv_choice_nothing2;
    test_case "Header type choice idempotence " `Quick test_eqv_choice_idem;
    test_case "Header type choice ACI" `Quick test_eqv_choice_ACI;
    test_case "refinement identity" `Quick test_eqv_refine_ident;
    test_case "refinement identity (α-rename)" `Quick test_eqv_refine_alpha;
    test_case "concatenation is correct" `Quick test_eqv_sigma;
    test_case "∅ ≠ ε" `Quick test_neqv_empty_nothing;
    test_case "ε ≠ ∅" `Quick test_nothing_neqv_empty;
    test_case "Σ-type is equivalent to itself" `Quick test_eqv_sigma_self;
    test_case
      "{x:ε | x.pkt_in=0101} = {x:ε | x.pkt_in[0:4]=0101 ∧ |x.pkt_in|=4}" `Quick
      test_eqv_fixed_pktin;
    test_case "length of pkt_in in {x:ε | |x.pkt_in|=4} > 2" `Quick
      test_pkt_length_gt_n;
    test_case "{x: {y: ε | y.pkt_in.length == 320} | x.pkt_in.length > 111}"
      `Quick test_pkt_length_gt2;
    test_case "length of pkt_in in {x:ε | |x.pkt_in|=4} not > 4" `Quick
      test_pkt_length_gt_n_fails;
    test_case "Refinement with false is equivalent to ∅" `Quick
      test_refine_false_eqv_nothing;
    test_case "{x:ε | len(x.pkt_in) + 1 == 0} should be equal to ∅" `Quick
      test_refine_false_pred_eqv_nothing;
    test_case "Σ-type is semantic sugar" `Quick test_sigma_semantic_sugar;
    test_case "Concat Minus" `Quick test_concat_minus;
    test_case "Concat Minus 1" `Quick test_concat_minus_1;
    test_case "Concat Minus Broken" `Quick test_concat_minus_broken;
  ]
