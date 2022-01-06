open Alcotest
open Pi4
open Syntax
open Formula
open HeapType

module TestConfig = struct
  let verbose = true

  let maxlen = 32
end

module Test = Test_utils.TestRunner (TestConfig)

let eth_inst =
  Test_utils.mk_inst "eth" [ ("smac", 48) (* "dmac", 48; "type", 16*) ]

let ipv4_inst = Test_utils.mk_inst "ipv4" [ ("src", 32); ("dst", 32) ]

let ipv6_inst = Test_utils.mk_inst "ipv6" [ ("version", 4); ("class", 8) ]

let tcp_inst = Test_utils.mk_inst "tcp" [ ("sport", 16); ("dport", 16) ]

let h_inst = Test_utils.mk_inst "h" [ ("f", 8); ("g", 16) ]

let header_table = HeaderTable.populate [ eth_inst; ipv4_inst; h_inst ]

let hty_empty = HeapType.empty header_table "x"

let hty_inst inst = HeapType.instance inst header_table "x"

let pred_pkt_out_empty binder =
  Eq (ArithExpr (Length (binder, PktOut)), ArithExpr (Num 0))

let pred_pkt_in_empty binder =
  Eq (ArithExpr (Length (binder, PktIn)), ArithExpr (Num 0))

let pred_pkt_in_out_empty binder =
  And (pred_pkt_in_empty binder, pred_pkt_out_empty binder)

let test_subtype_empty_nothing () =
  Test.not_subtype hty_empty Nothing [] header_table

let test_subtype_empty_empty () =
  Test.is_subtype hty_empty hty_empty [] header_table

let test_subtype_ref_empty () =
  let s = hty_empty in
  let t =
    Refinement
      ("x", hty_empty, Eq (ArithExpr (Length (0, PktIn)), ArithExpr (Num 8)))
  in
  Test.not_subtype s t [] header_table

let test_subtype_fixed_pktin_slice () =
  let s = Refinement ("x", hty_empty, pkt_eq_s (0, PktIn) "0101") in
  let t =
    Refinement
      ( "x",
        hty_empty,
        Eq (BvExpr (Slice (Packet (0, PktIn), 0, 4)), BvExpr (bv_s "0101")) )
  in
  Test.is_subtype s t [] header_table

let test_subtype_slice_fixed_pktin () =
  let s =
    Refinement
      ( "x",
        hty_empty,
        Eq (BvExpr (Slice (Packet (0, PktIn), 0, 4)), BvExpr (bv_s "0101")) )
  in
  let t = Refinement ("x", hty_empty, pkt_eq_s (0, PktIn) "0101") in
  Test.not_subtype s t [] header_table

let test_subtype_fixed_pktout_slice () =
  let s = Refinement ("x", hty_empty, pkt_eq_s (0, PktOut) "0101") in
  let t =
    Refinement
      ( "x",
        hty_empty,
        Eq (BvExpr (Slice (Packet (0, PktOut), 0, 4)), BvExpr (bv_s "0101")) )
  in
  Test.is_subtype s t [] header_table

(* Test doesn't make sense when using the smart constructor *)
(* let test_subtype_slice_fixed_pktout () = let s = Refinement ("x", Empty, TmEq
   (Slice (Packet (0, PktOut), 0, 4), bv_s "0101")) in let t = Refinement ("x",
   Empty, TmEq (Packet (0, PktOut), bv_s "0101")) in pr_ht "Type s" s; pr_ht
   "Type t" t; Alcotest.(check bool) "not ({x:ε | x.pkt_out[0:4]=0101} <: {x:ε |
   x.pkt_out=0101})" false ((check_subtype header_table [] 1500 s t) |>
   Result.ok_or_failwith) *)

let test_subtype_fixed_pktin_fixed_length () =
  let s = Refinement ("x", hty_empty, pkt_eq_s (0, PktIn) "0101") in
  let t =
    Refinement
      ("x", hty_empty, Eq (ArithExpr (Length (0, PktIn)), ArithExpr (Num 4)))
  in
  Test.is_subtype s t [] header_table

(* Test doesn't make sense when using the smart constructor *)
let test_subtype_fixed_length_fixed_pktin () =
  let s =
    Refinement
      ("x", hty_empty, Eq (ArithExpr (Length (0, PktIn)), ArithExpr (Num 4)))
  in
  (* let t = Refinement ("x", hty_empty, pkt_eq_s (0, PktIn) "0101") in *)
  let t =
    Refinement
      ("x", hty_empty, Eq (BvExpr (Packet (0, PktIn)), BvExpr (bv_s "0101")))
  in
  Test.not_subtype s t [] header_table

(* Alcotest.(check bool) "not ({x:ε | |x.pkt_in|=4} <: {x:ε | x.pkt_in=0101})"
   false ((check_subtype header_table [] 1500 s t) |> Result.ok_or_failwith) *)

let test_subtype_fixed_pktout_fixed_length () =
  let s = Refinement ("x", hty_empty, pkt_eq_s (0, PktOut) "0101") in
  let t =
    Refinement
      ("x", hty_empty, Eq (ArithExpr (Length (0, PktOut)), ArithExpr (Num 4)))
  in
  Test.is_subtype s t [] header_table

(* Test doesn't make sense when using the smart constructor *)
(* let test_subtype_fixed_length_fixed_pktout () = let s = Refinement ("x",
   Empty, TmEq (Length (0, PktOut), Num 4)) in let t = Refinement ("x", Empty,
   pkt_eq_s (0, PktOut) "0101") in pr_ht "Type s" s; pr_ht "Type t" t;
   Alcotest.(check bool) "not ({x:ε | |x.pkt_out|=4} <: {x:ε | x.pkt_out=0101})"
   false ((check_subtype header_table [] 1500 s t) |> Result.ok_or_failwith) *)

let test_check_instance_valid_eth () =
  let hty = Sigma ("x", hty_inst eth_inst, hty_inst ipv4_inst) in
  (* let hty = Refinement ("x", Top, And (IsValid (0, eth_inst), IsValid(0,
     ipv4_inst))) in *)
  let t1 = Refinement ("x", Top, IsValid (0, eth_inst)) in
  Alcotest.(check bool)
    "Σx:eth.ipv4 includes 'eth'" true
    (Test.check_subtype hty t1 [] header_table)

let test_check_instance_valid_ipv4 () =
  let hty =
    Refinement ("x", Top, And (IsValid (0, eth_inst), IsValid (0, ipv4_inst)))
  in
  (* let hty = Sigma ("x", hty_inst eth_inst, hty_inst ipv4_inst) in *)
  let t2 = Refinement ("x", hty, IsValid (0, ipv4_inst)) in
  Alcotest.(check bool)
    "Σx:eth.ipv4 includes 'ipv4'" true
    (Test.check_subtype hty t2 [] header_table)

let test_check_instance_valid_choice () =
  let hty = Choice (hty_inst eth_inst, hty_inst ipv4_inst) in
  let htyv = Refinement ("x", hty, IsValid (0, eth_inst)) in
  Alcotest.(check bool)
    "eth + ipv4 does not include 'eth'" false
    (Test.check_subtype hty htyv [] header_table)

(*let test_freshen1 () = let hty = Sigma ("x", hty_inst eth_inst, Refinement
  ("x", hty_inst ipv4_inst, True)) in let htyv = Refinement ("x", hty, IsValid
  (0, "eth")) in let hty_f = Sigma ("x!", hty_inst eth_inst, Refinement ("x!!",
  hty_inst ipv4_inst, True)) in let htyv_f = Refinement ("x", hty_f, IsValid (0,
  "eth")) in

  Alcotest.(check string) "variables freshened" (Pi4.Pretty.print_header_type []
  htyv_f |> Result.ok_or_failwith) (Pi4.Pretty.print_header_type [] (freshen
  htyv) |> Result.ok_or_failwith)*)

let test_subtype_empty_concat () =
  let hty_s = hty_inst eth_inst in
  let hty_t =
    Sigma
      ( "x",
        hty_empty,
        Refinement
          ( "y",
            hty_inst eth_inst,
            And
              ( Eq (ArithExpr (Length (0, PktIn)), ArithExpr (Num 0)),
                Eq (ArithExpr (Length (0, PktOut)), ArithExpr (Num 0)) ) ) )
  in
  Test.is_subtype hty_s hty_t [] header_table

let test_subtype_concat_empty () =
  let hty_s =
    Sigma
      ( "x",
        hty_empty,
        Refinement
          ( "y",
            hty_inst eth_inst,
            And
              ( Eq (ArithExpr (Length (0, PktIn)), ArithExpr (Num 0)),
                Eq (ArithExpr (Length (0, PktOut)), ArithExpr (Num 0)) ) ) )
  in
  let hty_t = hty_inst eth_inst in
  Test.is_subtype hty_s hty_t [] header_table

let test_plus () =
  let hty_s =
    Refinement
      ( "x",
        hty_empty,
        Eq (ArithExpr (Plus (Length (0, PktIn), Num 1)), ArithExpr (Num 33)) )
  in
  let hty_t =
    Refinement
      ("y", hty_empty, Eq (ArithExpr (Length (0, PktIn)), ArithExpr (Num 32)))
  in
  Test.is_subtype hty_s hty_t [] header_table

let test_concat () =
  let hty_s =
    Refinement
      ( "x",
        hty_inst h_inst,
        Eq
          ( BvExpr
              (Concat (Slice (Instance (0, h_inst), 0, 8), Packet (0, PktIn))),
            BvExpr (Concat (bv_s "01011010", Packet (0, PktIn))) ) )
  in
  let hty_t =
    Refinement
      ( "y",
        hty_inst h_inst,
        Eq
          (BvExpr (Slice (Instance (0, h_inst), 0, 8)), BvExpr (bv_s "01011010"))
      )
  in
  Test.is_subtype hty_s hty_t [] header_table

let test_concat2 () =
  let hty_s =
    Substitution
      ( Refinement
          ( "x",
            hty_inst h_inst,
            Eq
              ( BvExpr
                  (Concat (Slice (Instance (0, h_inst), 0, 4), Packet (0, PktIn))),
                BvExpr (Packet (1, PktIn)) ) ),
        "z",
        Refinement
          ( "y",
            hty_empty,
            Eq (BvExpr (Slice (Packet (0, PktIn), 0, 4)), BvExpr (bv_s "1111"))
          ) )
  in
  let hty_t =
    Refinement
      ( "x",
        hty_inst h_inst,
        Eq (BvExpr (Slice (Instance (0, h_inst), 0, 4)), BvExpr (bv_s "1111"))
      )
  in
  Test.is_subtype hty_s hty_t [] header_table

let test_concat3 () =
  let hty_s =
    Parsing.parse_heap_type header_table []
      {|
        (Σ x:
          {y:ε|y.pkt_in.length==6}.
          {z:eth|z.pkt_in==x.pkt_in@s.pkt_in})[s->{t:ε|t.pkt_in.length==8}]
      |}
  in

  Test.not_subtype hty_s Nothing [] header_table

let test_subst () =
  (* let hty_s = Parsing.parse_heap_type
     "{x:eth|x.pkt_in.length==y.pkt_in.length}[y ->
     {z:\\empty|z.pkt_in.length==1 || z.pkt_in.length==2}]" header_table []
     in *)
  (* let hty_t = Parsing.parse_heap_type "{x:eth|x.pkt_in.length==1}"
     header_table [] in *)
  (* let hty_t = Parsing.parse_heap_type
     "{x:eth|x.pkt_in.length==v.pkt_in.length}[v ->
     {z:\\empty|z.pkt_in.length==1}]" header_table [] in *)
  let hty_s =
    Parsing.parse_heap_type header_table []
      "{x:eth|x.pkt_in.length==1} + {x:eth|x.pkt_in.length==2}"
  in
  let hty_t =
    Parsing.parse_heap_type header_table []
      "{x:eth|x.pkt_in.length==v.pkt_in.length}[v -> {z:\\empty|z.pkt_in.length==1 || z.pkt_in.length==2}]"
  in

  Test.is_subtype hty_s hty_t [] header_table

let test_refine_choice () =
  let inst_a = Test_utils.mk_inst "a" [ ("a", 4) ] in
  let inst_b = Test_utils.mk_inst "b" [ ("b", 2) ] in
  let ht = HeaderTable.populate [ inst_a; inst_b ] in
  (* TODO: From the perspective of the formalization we expect this to work
     without the explicit validity check. *)
  let hty_s =
    Parsing.parse_heap_type ht [] "{x:(a+b)|x.a.a==0x1 ∧ x.a.valid}"
  in
  let hty_t = Parsing.parse_heap_type ht [] "a" in
  Test.is_subtype hty_s hty_t [] ht

let test_type_extract_nothing () =
  let ht =
    HeaderTable.populate
      [ Test_utils.mk_inst "a_0" [ ("a", 4) ];
        Test_utils.mk_inst "a_1" [ ("a", 4) ];
        Test_utils.mk_inst "b_0" [ ("b", 2) ]
      ]
  in
  let hty_var =
    Parsing.parse_heap_type ht []
      {|
        {y_2:
          {x_2:
            ⊤
            | true ∧
              ¬(x_2.a_0.valid) ∧
              ¬(x_2.b_0.valid)}
          | y_2.pkt_in.length == 4} 
      |}
  in

  let hty_s =
    Parsing.parse_heap_type ht
      [ ("x_1", Env.VarBind hty_var) ]
      {|
        Σy_0:
          ({z_0:
            {v_0:
              ⊤
              | v_0.a_1.valid ∧
                ¬(v_0.a_0.valid) ∧
                ¬(v_0.b_0.valid)}
            | z_0.pkt_in.length == 0 ∧
              z_0.pkt_out.length == 0}).
          ({u_0:
            {y_1:
              {x_0:
                ⊤
                | true ∧
                  ¬(x_0.a_0.valid) ∧
                  ¬(x_0.b_0.valid)}
              | (y_1.pkt_in.length + 4) == 4}
            | true ∧
            (x_1.a_0.valid ⇒
            (u_0.a_0.valid ∧
              u_0.a_0[0:4] == x_1.a_0[0:4])) ∧
            (x_1.a_1.valid ⇒
              (u_0.a_1.valid ∧
              u_0.a_1[0:4] == x_1.a_1[0:4])) ∧
            (x_1.b_0.valid ⇒
              (u_0.b_0.valid ∧
              u_0.b_0[0:2] == x_1.b_0[0:2])) ∧
            x_1.pkt_out.length == u_0.pkt_out.length ∧
            x_1.pkt_out == u_0.pkt_out ∧
            y_0.a_1[0:4]@u_0.pkt_in == x_1.pkt_in ∧
            (u_0.pkt_in.length + 4) == x_1.pkt_in.length})
      |}
  in

  Test.not_subtype hty_s Nothing [ ("x_1", Env.VarBind hty_var) ] ht

let test_refinement_not_nothing () =
  let ht =
    HeaderTable.populate
      [ Test_utils.mk_inst "a_0" [ ("a", 4) ];
        Test_utils.mk_inst "a_1" [ ("a", 4) ];
        Test_utils.mk_inst "b_0" [ ("b", 2) ]
      ]
  in
  let hty_s =
    Parsing.parse_heap_type ht []
      {|
      {y_1:
      ⊤
      | ¬(y_1.a_1.valid) ∧
        ¬(y_1.a_0.valid) ∧
        ¬(y_1.b_0.valid) ∧
        (y_1.pkt_in.length + 4) == 6}
      |}
  in

  Test.not_subtype hty_s Nothing [] ht

let test_sigma_not_nothing () =
  let ht =
    HeaderTable.populate
      [ Test_utils.mk_inst "a_0" [ ("a", 4) ];
        Test_utils.mk_inst "a_1" [ ("a", 4) ];
        Test_utils.mk_inst "b_0" [ ("b", 2) ]
      ]
  in
  let hty_s =
    Parsing.parse_heap_type ht []
      {|
        Σy_0:
          ({z_0:
            {v_0:
              ⊤
              | v_0.a_1.valid ∧
                ¬(v_0.a_0.valid) ∧
                ¬(v_0.b_0.valid)}
            | z_0.pkt_in.length == 0 ∧
              z_0.pkt_out.length == 0}).
          ({u_0:
            {y_1:
              {x_0:
                ⊤
                | true ∧
                  ¬(x_0.a_0.valid) ∧
                  ¬(x_0.b_0.valid)}
              | (y_1.pkt_in.length + 4) == 4}
            | true})
      |}
  in

  Test.not_subtype hty_s Nothing [] ht

let test_subtype_roundtripping () =
  let ht =
    HeaderTable.populate
      [ Test_utils.mk_inst "h_0" [ ("f", 1) ];
        Test_utils.mk_inst "h_1" [ ("f", 1) ]
      ]
  in
  let hty_var =
    Parsing.parse_heap_type ht []
      {|
        {y_9:
          {x_3:
            ⊤
            | x_3.h_0.valid}
          | y_9.pkt_in.length == 0 ∧
            y_9.pkt_out.length == 0}
      |}
  in

  let env = [ ("x_2", Env.VarBind hty_var) ] in
  let hty_s =
    Parsing.parse_heap_type ht env
      {|
        ((Σy_6:
          ({z_2:
            {v_0:
              ⊤
              | v_0.h_1.valid ∧
                ¬(v_0.h_0.valid)}
            | z_2.pkt_in.length == 0 ∧
              z_2.pkt_out.length == 0}).
          ({u_1:
            Σz_1:
              ({y_8:
                  {w_4:
                    ⊤
                    | true ∧
                      ¬(w_4.h_0.valid) ∧
                      ¬(w_4.h_1.valid)}
                  | y_8.pkt_out.length == 0 ∧
                    y_6.h_1[0:1]@y_8.pkt_in == y_0.pkt_out ∧
                    (y_8.pkt_in.length + 1) == y_0.pkt_out.length}).
              ({y_7:
                  {w_3:
                    ⊤
                    | true ∧
                      ¬(w_3.h_0.valid) ∧
                      ¬(w_3.h_1.valid)}
                  | y_7.pkt_out.length == 0 ∧
                    y_7.pkt_in == y_0.pkt_in ∧
                    y_7.pkt_in.length == y_0.pkt_in.length})
            | true ∧
              (y_3.h_0.valid ⇒
                (u_1.h_0.valid ∧
                  u_1.h_0[0:1] == y_3.h_0[0:1])) ∧
              (y_3.h_1.valid ⇒
                (u_1.h_1.valid ∧
                  u_1.h_1[0:1] == y_3.h_1[0:1])) ∧
              y_3.pkt_out.length == u_1.pkt_out.length ∧
              y_3.pkt_out == u_1.pkt_out ∧
              y_6.h_1[0:1]@u_1.pkt_in == y_3.pkt_in ∧
              (u_1.pkt_in.length + 1) == y_3.pkt_in.length}))[
        y_3 ↦
          Σz_0:
            ({y_5:
                {w_2:
                  ⊤
                  | true ∧
                    ¬(w_2.h_0.valid) ∧
                    ¬(w_2.h_1.valid)}
                | y_5.pkt_out.length == 0 ∧
                  y_5.pkt_in == y_0.pkt_out ∧
                  y_5.pkt_in.length == y_0.pkt_out.length}).
            ({y_4:
                {w_1:
                  ⊤
                  | true ∧
                    ¬(w_1.h_0.valid) ∧
                    ¬(w_1.h_1.valid)}
                | y_4.pkt_out.length == 0 ∧
                  y_4.pkt_in == y_0.pkt_in ∧
                  y_4.pkt_in.length == y_0.pkt_in.length})])[
        y_0 ↦
          Σx_0:
            ({u_0:
              {y_2:
                {x_1:
                  ⊤
                  | x_1.h_0.valid}
                | y_2.pkt_in.length == 0 ∧
                  y_2.pkt_out.length == 0}
              | x_2.pkt_in.length == u_0.pkt_in.length ∧
                x_2.pkt_in == u_0.pkt_in ∧
                x_2.pkt_out.length == u_0.pkt_out.length ∧
                x_2.pkt_out == u_0.pkt_out ∧
                true ∧
                (x_2.h_0.valid ⇒
                  (u_0.h_0.valid ∧
                    u_0.h_0[0:1] == x_2.h_0[0:1])) ∧
                (x_2.h_1.valid ⇒
                  (u_0.h_1.valid ∧
                    u_0.h_1[0:1] == x_2.h_1[0:1]))}).
            ({y_1:
              {w_0:
                ⊤
                | true ∧
                  ¬(w_0.h_0.valid) ∧
                  ¬(w_0.h_1.valid)}
              | y_1.pkt_in.length == 0 ∧
                y_1.pkt_out.length == 1 ∧
                y_1.pkt_out[0:1] == x_2.h_0[0:1]})]
      |}
  in

  let hty_t =
    Parsing.parse_heap_type ht env
      {|
        {y_10:
          {x_4:
            ⊤
            | x_4.h_1.valid}
          | true ∧
            y_10.h_1[0:1] == x_2.h_0[0:1]}
      |}
  in

  Test.is_subtype hty_s hty_t env ht

let test_subtype_roundtripping2 () =
  let ht =
    HeaderTable.populate
      [ Test_utils.mk_inst "h_0" [ ("f", 1) ];
        Test_utils.mk_inst "h_1" [ ("f", 1) ]
      ]
  in
  let hty_var =
    Parsing.parse_heap_type ht []
      {|
          {y_9:
            {x_3:
              ⊤
              | x_3.h_0.valid}
            | y_9.pkt_in.length == 0 ∧
              y_9.pkt_out.length == 0}
        |}
  in

  let env = [ ("x_2", Env.VarBind hty_var) ] in
  let hty_subst1 =
    Parsing.parse_heap_type ht env
      {|
        Σx_0:
        ({u_0:
          {y_2:
            {x_1:
              ⊤
              | x_1.h_0.valid}
            | y_2.pkt_in.length == 0 ∧
              y_2.pkt_out.length == 0}
          | x_2.pkt_in.length == u_0.pkt_in.length ∧
            x_2.pkt_in == u_0.pkt_in ∧
            x_2.pkt_out.length == u_0.pkt_out.length ∧
            x_2.pkt_out == u_0.pkt_out ∧
            true ∧
            (x_2.h_0.valid ⇒
              (u_0.h_0.valid ∧
                u_0.h_0[0:1] == x_2.h_0[0:1])) ∧
            (x_2.h_1.valid ⇒
              (u_0.h_1.valid ∧
                u_0.h_1[0:1] == x_2.h_1[0:1]))}).
        ({y_1:
          {w_0:
            ⊤
            | true ∧
              ¬(w_0.h_0.valid) ∧
              ¬(w_0.h_1.valid)}
          | y_1.pkt_in.length == 0 ∧
            y_1.pkt_out.length == 1 ∧
            y_1.pkt_out[0:1] == x_2.h_0[0:1]})
        |}
  in

  let env' = ("y_0", Env.VarBind hty_subst1) :: env in
  let hty_subst2 =
    Parsing.parse_heap_type ht env'
      {|
          Σz_0:
            ({y_5:
                {w_2:
                  ⊤
                  | true ∧
                    ¬(w_2.h_0.valid) ∧
                    ¬(w_2.h_1.valid)}
                | y_5.pkt_out.length == 0 ∧
                  y_5.pkt_in == y_0.pkt_out ∧
                  y_5.pkt_in.length == y_0.pkt_out.length}).
            ({y_4:
                {w_1:
                  ⊤
                  | true ∧
                    ¬(w_1.h_0.valid) ∧
                    ¬(w_1.h_1.valid)}
                | y_4.pkt_out.length == 0 ∧
                  y_4.pkt_in == y_0.pkt_in ∧
                  y_4.pkt_in.length == y_0.pkt_in.length})
        |}
  in

  let env'' = ("y_3", Env.VarBind hty_subst2) :: env' in
  let hty_s =
    Parsing.parse_heap_type ht env''
      {|
          Σy_6:
            ({z_2:
              {v_0:
                ⊤
                | v_0.h_1.valid ∧
                  ¬(v_0.h_0.valid)}
              | z_2.pkt_in.length == 0 ∧
                z_2.pkt_out.length == 0}).
            ({u_1:
              Σz_1:
                ({y_8:
                    {w_4:
                      ⊤
                      | true ∧
                        ¬(w_4.h_0.valid) ∧
                        ¬(w_4.h_1.valid)}
                    | y_8.pkt_out.length == 0 ∧
                      y_6.h_1[0:1]@y_8.pkt_in == y_0.pkt_out ∧
                      (y_8.pkt_in.length + 1) == y_0.pkt_out.length}).
                ({y_7:
                    {w_3:
                      ⊤
                      | true ∧
                        ¬(w_3.h_0.valid) ∧
                        ¬(w_3.h_1.valid)}
                    | y_7.pkt_out.length == 0 ∧
                      y_7.pkt_in == y_0.pkt_in ∧
                      y_7.pkt_in.length == y_0.pkt_in.length})
              | true ∧
                (y_3.h_0.valid ⇒
                  (u_1.h_0.valid ∧
                    u_1.h_0[0:1] == y_3.h_0[0:1])) ∧
                (y_3.h_1.valid ⇒
                  (u_1.h_1.valid ∧
                    u_1.h_1[0:1] == y_3.h_1[0:1])) ∧
                y_3.pkt_out.length == u_1.pkt_out.length ∧
                y_3.pkt_out == u_1.pkt_out ∧
                y_6.h_1[0:1]@u_1.pkt_in == y_3.pkt_in ∧
                (u_1.pkt_in.length + 1) == y_3.pkt_in.length})
        |}
  in

  let hty_t =
    Parsing.parse_heap_type ht env''
      {|
          {y_10:
            {x_4:
              ⊤
              | x_4.h_1.valid}
            | true ∧
              y_10.h_1[0:1] == x_2.h_0[0:1]}
        |}
  in

  Test.is_subtype hty_s hty_t env'' ht

let test_subtype_extract_opt () =
  let header_table =
    HeaderTable.populate
      [ Parsing.parse_instance_exn "A { a : 4; }";
        Parsing.parse_instance_exn "B { b : 2; }"
      ]
  in
  let input_type =
    Parsing.parse_heap_type header_table [] "{y:ε|y.pkt_in.length > 5}"
  in
  let context = [ ("x", Env.VarBind input_type) ] in
  let subtype =
    Parsing.parse_heap_type header_table context
      {|
        {z:⊤
          | 
            z.A.valid ∧ 
            z.B.valid ∧ 
            z.pkt_in.length + 4 > 5 ∧
            z.A@z.pkt_in == x.pkt_in ∧ 
            z.pkt_out == x.pkt_out  }
      |}
  in

  let supertype = Parsing.parse_heap_type header_table [] "Σy:A.B" in
  Test.is_subtype subtype supertype context header_table

let test_subtype_plus () =
  let header_table =
    HeaderTable.populate
      [ Parsing.parse_instance_exn "A { a : 4; }";
        Parsing.parse_instance_exn "B { b : 2; }"
      ]
  in
  let subtype =
    Parsing.parse_heap_type header_table []
      {|
        {x:A|x.pkt_in.length+4 == 0}
      |}
  in

  let supertype = Parsing.parse_heap_type header_table [] "A" in
  Test.is_subtype subtype supertype [] header_table

let test_set =
  [ (* test_case "not ({x:ε | x.pkt_out[0:4]=0101} <: {x:ε | x.pkt_out=0101})"
       `Quick test_subtype_slice_fixed_pktout; *)

    (* test_case "not ({x:ε | |x.pkt_in|=4} <: {x:ε | x.pkt_in=0101})" `Quick
       test_subtype_fixed_length_fixed_pktin; *)

    (* test_case "not ({x:ε | |x.pkt_out|=4} <: {x:ε | x.pkt_out=0101})" `Quick
       test_subtype_fixed_length_fixed_pktout *)
    test_case "ε <: ε" `Quick test_subtype_empty_empty;
    test_case "not(ε <: ∅)" `Quick test_subtype_empty_nothing;
    test_case "not(ε <: {x:ε | |x.pkt_in|=8})" `Quick test_subtype_ref_empty;
    test_case "{x:ε | x.pkt_in=0101} <: {x:ε | x.pkt_in[0:4]=0101}" `Quick
      test_subtype_fixed_pktin_slice;
    test_case "not ({x:ε | x.pkt_in[0:4]=0101} <: {x:ε | x.pkt_in=0101})" `Quick
      test_subtype_slice_fixed_pktin;
    test_case "{x:ε | x.pkt_out=0101} <: {x:ε | x.pkt_out[0:4]=0101}" `Quick
      test_subtype_fixed_pktout_slice;
    test_case "{x:ε | x.pkt_in=0101} <: {x:ε | |x.pkt_in|=4}" `Quick
      test_subtype_fixed_pktin_fixed_length;
    test_case "{x:ε | x.pkt_out=0101} <: {x:ε | |x.pkt_out|=4}" `Quick
      test_subtype_fixed_pktout_fixed_length;
    test_case "Σx:eth.ipv4 includes 'eth'" `Slow test_check_instance_valid_eth;
    test_case "Σx:eth.ipv4 includes 'ipv4'" `Slow test_check_instance_valid_ipv4;
    test_case "eth + ipv4 does not include 'eth'" `Quick
      test_check_instance_valid_choice;
    test_case "eth <: Σx:ε.{y:eth | |y.pkt_in|=0 ∧ |y.pkt_out|=0" `Quick
      test_subtype_empty_concat;
    test_case "Σx:ε.{y:eth | |y.pkt_in|=0 ∧ |y.pkt_out|=0 <: eth" `Quick
      test_subtype_concat_empty;
    test_case "{x:ε | len(x.pkt_in)+1 = 33 } <: {x:ε | len(x.pkt_in) = 32 }"
      `Quick test_plus;
    test_case
      "{x:h | h[0:8] @ pkt_in = 01011010 @ x.pkt_in } <: {x:h | h[0:8] = 01011010 }"
      `Quick test_concat;
    test_case
      "{x:h | x.h[0:4] @ x.pkt_in = z.pkt_in }[z -> {y:ε | y.pkt_in[0:4]=1111}] <: {x:h | h[0:4] = 1111 }"
      `Quick test_concat2;
    test_case "Concat3" `Quick test_concat3;
    test_case "Substitution" `Quick test_subst;
    test_case "{x:a+b| x.a.a = 0x1} <: a" `Quick test_refine_choice;
    test_case "Type of extract should not be ∅" `Quick test_type_extract_nothing;
    test_case "Refinement type should not be ∅" `Quick
      test_refinement_not_nothing;
    test_case "Sigma type should not be ∅" `Quick test_sigma_not_nothing;
    test_case "Single header roundtripping subtype" `Quick
      test_subtype_roundtripping;
    test_case "Single header roundtripping subtype 2" `Quick
      test_subtype_roundtripping2;
    test_case "Optimized subtype extract" `Quick test_subtype_extract_opt;
    test_case "Plus" `Quick test_subtype_plus
  ]
