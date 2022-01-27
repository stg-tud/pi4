open Core
open Alcotest
open Pi4
open Syntax

let inst_ether =
  Test_utils.mk_inst "ether"
    [ ("dstAddr", 48); ("srcAddr", 48); ("etherType", 16) ]

let inst_vlan =
  Test_utils.mk_inst "vlan"
    [ ("prio", 3); ("id", 1); ("vlan", 12); ("etherType", 16) ]

let inst_ipv4 =
  Test_utils.mk_inst "ipv4"
    [ ("version", 4);
      ("ihl", 4);
      ("tos", 8);
      ("len", 16);
      ("id", 16);
      ("flags", 3);
      ("frag", 13);
      ("ttl", 8);
      ("proto", 8);
      ("chksum", 16);
      ("src", 32);
      ("dst", 32)
    ]

let test_parse_header_table () =
  print_endline (Sys.getcwd());
  let input = Parsing.read_file "./examples/headers.pi4" in
  let expected =
    Program.
      { declarations =
          [ HeaderTypeDecl
              { name = "A_t";
                fields =
                  [ { name = "f"; typ = 4 };
                    { name = "g"; typ = 8 };
                    { name = "h"; typ = 4 }
                  ]
              };
            HeaderTypeDecl
              { name = "B_t"; fields = [ { name = "f"; typ = 8 } ] };
            HeaderInstanceDecl { name = "A"; type_name = "A_t" };
            HeaderInstanceDecl { name = "B"; type_name = "B_t" }
          ];
        command = Skip
      }
  in

  Alcotest.(check Testable.program)
    "programs are equal" expected
    (Parsing.parse_program input)

let test_parse_extract () =
  let input = Parsing.read_file "./examples/extract.pi4" in
  let prog = Parsing.parse_program input in

  Alcotest.(check Testable.command)
    "commands are equal" (Extract inst_ether) prog.command

let test_parse_sequence () =
  let input = Parsing.read_file "./examples/sequence.pi4" in
  let prog = Parsing.parse_program input in
  let expected = Command.Seq (Extract inst_ether, Extract inst_ipv4) in

  Alcotest.(check Testable.command) "commands are equal" expected prog.command

let test_parse_conditional () =
  let input = Parsing.read_file "./examples/conditional.pi4" in
  let prog = Parsing.parse_program input in
  let expected =
    Command.Seq
      ( Extract inst_ether,
        If
          ( Eq
              ( BvExpr (Slice (Instance (0, inst_ether), 96, 112)),
                BvExpr (bv_x "0800") ),
            Extract inst_ipv4,
            Skip ) )
  in

  Alcotest.(check Testable.command) "commands are equal" expected prog.command

let test_parse_optional_else () =
  let input = Parsing.read_file "./examples/optional-else.pi4" in
  let prog = Parsing.parse_program input in
  let expected =
    Command.Seq
      ( Extract inst_ether,
        If
          ( Eq
              ( BvExpr (Slice (Instance (0, inst_ether), 96, 112)),
                BvExpr (bv_x "0800") ),
            Extract inst_ipv4,
            Skip ) )
  in

  Alcotest.(check Testable.command) "commands are equal" expected prog.command

let test_parse_nested_if () =
  let input = Parsing.read_file "./examples/nested-if.pi4" in
  let prog = Parsing.parse_program input in
  let expected =
    Command.Seq
      ( Extract inst_ether,
        If
          ( Eq
              ( BvExpr (Slice (Instance (0, inst_ether), 96, 112)),
                BvExpr (bv_x "8100") ),
            Seq
              ( Extract inst_vlan,
                If
                  ( Eq
                      ( BvExpr (Slice (Instance (0, inst_vlan), 16, 32)),
                        BvExpr (bv_x "0800") ),
                    Extract inst_ipv4,
                    Skip ) ),
            Skip ) )
  in

  Alcotest.(check Testable.command) "commands are equal" expected prog.command

let test_parse_reset () =
  let input = Parsing.read_file "./examples/reset.pi4" in
  let prog = Parsing.parse_program input in
  let expected =
    Command.Seq
      ( Extract inst_ether,
        Seq
          ( If
              ( Eq
                  ( BvExpr (Slice (Instance (0, inst_ether), 96, 112)),
                    BvExpr (bv_x "0800") ),
                Extract inst_ipv4,
                Skip ),
            Seq
              ( Remit inst_ether,
                Seq (If (IsValid (0, inst_ipv4), Remit inst_ipv4, Skip), Reset)
              ) ) )
  in

  Alcotest.(check Testable.command) "commands are equal" expected prog.command

let test_parse_add () =
  let input = Parsing.read_file "./examples/add_vlan.pi4" in
  let prog = Parsing.parse_program input in
  let eth_l, eth_r =
    match Instance.field_bounds inst_ether "etherType" with
    | Ok (l, r) -> (l, r)
    | Error (`FieldAccessError e) -> failwith e
  in
  let expected =
    Command.Seq
      ( Extract inst_ether,
        Seq
          ( If
              ( Eq
                  ( BvExpr (Slice (Instance (0, inst_ether), 96, 112)),
                    BvExpr (bv_x "8100") ),
                Extract inst_vlan,
                Skip ),
            If
              ( Neg (IsValid (0, inst_vlan)),
                Seq
                  ( Add inst_vlan,
                    Assign (inst_ether, eth_l, eth_r, BvExpr (bv_x "8100")) ),
                Skip ) ) )
  in

  Alcotest.(check Testable.command) "commands are equal" expected prog.command

let test_parse_ascription () =
  let input = Parsing.read_file "./examples/ascription.pi4" in
  let prog = Parsing.parse_program input in
  let header_table = HeaderTable.of_decls prog.declarations in
  let hty_in =
    Parsing.parse_heap_type header_table [] "{y:\\empty|y.pkt_in.length>7}"
  in
  let hty_out = Parsing.parse_heap_type header_table [] "a" in
  let inst_a = Test_utils.mk_inst "a" [ ("a", 4) ] in
  let inst_b = Test_utils.mk_inst "b" [ ("b", 8) ] in
  let expected =
    Command.Seq (Ascription (Extract inst_a, "z", hty_in, hty_out), Extract inst_b)
  in

  Alcotest.(check Testable.command) "commands are equal" expected prog.command

let test_set =
  [ test_case "Header table is parsed correctly" `Quick test_parse_header_table;
    test_case "Extract is parsed correctly" `Quick test_parse_extract;
    test_case "Sequence is parsed correctly" `Quick test_parse_sequence;
    test_case "Conditional is parsed correctly" `Quick test_parse_conditional;
    test_case "Optional else branch is parsed correctly" `Quick
      test_parse_optional_else;
    test_case "Nested If is parsed correctly" `Quick test_parse_nested_if;
    test_case "Reset is parsed correctly" `Quick test_parse_reset;
    test_case "Add and assign are parsed correctly" `Quick test_parse_add;
    test_case "Ascription is parsed correctly" `Quick test_parse_ascription
  ]
