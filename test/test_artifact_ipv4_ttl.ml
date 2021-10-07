open Alcotest
open Pi4
open Syntax

module TestConfig = struct
  let verbose = true

  let maxlen = 272
end

module Test = Test_utils.TestRunner (TestConfig)

module Config = struct
  let maxlen = 320
end

module P = Prover.Make (Encoding.FixedWidthBitvectorEncoding (Config))
module T = Typechecker.MakeSSAChecker (Typechecker.CompleteChecker (Config))

let test_typecheck_ssa header_table cmd ty =
  Prover.make_prover "z3";
  Alcotest.(check Testable.typechecker_result)
    (Fmt.str "%a" (Pretty.pp_type []) ty)
    Typechecker.TypecheckingResult.Success
    (T.check_type cmd ty header_table)

let eth_inst =
  Test_utils.mk_inst "ether"
    [ ("dstAddr", 48); ("srcAddr", 48); ("etherType", 16) ]

let ipv4_inst =
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

let stdmeta_inst = Test_utils.mk_inst "stdmeta" [ ("egressSpec", 9) ]

let header_table = HeaderTable.populate [ eth_inst; ipv4_inst; stdmeta_inst ]

let parse_header_type hty_str =
  Parsing.header_type_of_string hty_str header_table []

let test_ttl_safe1 () =
  let ingress =
    {|
      header_type ipv4_t {
        ttl: 8;
      }
      header_type standard_metadata_t {
        egress_spec: 9;
      }
      header ipv4 : ipv4_t
      header stdmeta : standard_metadata_t
      stdmeta.egress_spec := 0b111111111
    |}
  in
  let prog = Parsing.parse_program ingress in
  Fmt.pr "%a\n" Pretty.pp_command prog.command;
  let header_table = HeaderTable.of_decls prog.declarations in
  Logs.debug (fun m -> m "%a\n" Pretty.pp_header_table header_table);
  let ty =
    Parsing.parse_type
      "(x:{y:⊤|y.ipv4.valid ∧ y.stdmeta.valid}) ->
     {y:⊤|y.ipv4.valid ∧ y.stdmeta.valid ∧ ((y.ipv4.valid ∧ y.ipv4.ttl=0x00) =>
     y.stdmeta.egress_spec=0b111111111)}"
      header_table
  in
  Test.typecheck header_table prog.command ty

let test_ttl_safe1_ssa () =
  let ingress =
    {|
        header_type ipv4_t {
          ttl: 8;
        }
        header_type standard_metadata_t {
          egress_spec: 9;
        }
        header ipv4_0 : ipv4_t
        header stdmeta_0 : standard_metadata_t
        header stdmeta_1 : standard_metadata_t
        add(stdmeta_1);
        stdmeta_1.egress_spec := 0b111111111
      |}
  in
  let prog = Parsing.parse_program ingress in
  Fmt.pr "%a\n" Pretty.pp_command prog.command;
  let header_table = HeaderTable.of_decls prog.declarations in
  Logs.debug (fun m -> m "%a\n" Pretty.pp_header_table header_table);
  let ty =
    Parsing.parse_type
      "(x:{y:⊤|y.ipv4_0.valid && y.stdmeta_0.valid && !y.stdmeta_1.valid}) -> {y:⊤|y.ipv4_0.valid && y.stdmeta_0.valid && y.stdmeta_1.valid && ((y.ipv4_0.valid ∧ y.ipv4_0.ttl=0x00) =>
      y.stdmeta_1.egress_spec=0b111111111)}"
      header_table
  in
  test_typecheck_ssa header_table prog.command ty

let test_ttl_safe1_ssa_ascribed () =
  let ingress =
    {|
        header_type ipv4_t {
          ttl: 8;
        }
        header_type standard_metadata_t {
          egress_spec: 9;
        }
        header ipv4_0 : ipv4_t
        header stdmeta_0 : standard_metadata_t
        header stdmeta_1 : standard_metadata_t
        add(stdmeta_1);
        if (ipv4_0.ttl == 0b00000000) {
            stdmeta_1.egress_spec := 0b111111111
        } else {
            stdmeta_1.egress_spec := 0b00000001
        }
      |}
  in
  let prog = Parsing.parse_program ingress in
  Fmt.pr "%a\n" Pretty.pp_command prog.command;
  let header_table = HeaderTable.of_decls prog.declarations in
  Logs.debug (fun m -> m "%a\n" Pretty.pp_header_table header_table);
  let ty =
    Parsing.parse_type
      "(x:{y:⊤|y.ipv4_0.valid && y.stdmeta_0.valid && !y.stdmeta_1.valid}) -> {y:⊤|y.ipv4_0.valid && y.stdmeta_0.valid && y.stdmeta_1.valid && ((y.ipv4_0.valid ∧ y.ipv4_0.ttl=0b00000000) =>
      y.stdmeta_1.egress_spec=0b111111111)}"
      header_table
  in
  test_typecheck_ssa header_table prog.command ty

let test_ttl_safe2 () =
  let ingress =
    {|
      header_type ipv4_t {
        ttl: 8;
      }
      header_type standard_metadata_t {
        egress_spec: 9;
      }
      header ipv4 : ipv4_t
      header stdmeta : standard_metadata_t
      if(ipv4[0:8]==0x00) {
        stdmeta.egress_spec := 0b111111111
      }
    |}
  in
  let prog = Parsing.parse_program ingress in
  Fmt.pr "%a\n" Pretty.pp_command prog.command;
  let header_table = HeaderTable.of_decls prog.declarations in
  Logs.debug (fun m -> m "%a\n" Pretty.pp_header_table header_table);
  let ty =
    Parsing.parse_type
      "(x:{y:⊤|y.ipv4.valid ∧ y.stdmeta.valid}) ->
      {y:⊤|y.ipv4.valid ∧ y.stdmeta.valid ∧ ((y.ipv4.valid ∧ y.ipv4.ttl=0x00) =>
      y.stdmeta.egress_spec=0b111111111)}"
      header_table
  in
  Test.typecheck header_table prog.command ty

let test_ttl_safe2_ssa () =
  let ingress =
    {|
        header_type ipv4_t {
          ttl: 8;
        }
        header_type standard_metadata_t {
          egress_spec: 9;
        }
        header ipv4_0 : ipv4_t
        header stdmeta_0 : standard_metadata_t
        header stdmeta_1 : standard_metadata_t
        if(ipv4_0[0:8] == 0b00000000) {
          add(stdmeta_1);
          stdmeta_1.egress_spec := 0b111111111
        }
      |}
  in
  let prog = Parsing.parse_program ingress in
  Fmt.pr "%a\n" Pretty.pp_command prog.command;
  let header_table = HeaderTable.of_decls prog.declarations in
  Logs.debug (fun m -> m "%a\n" Pretty.pp_header_table header_table);
  let ty =
    Parsing.parse_type
      "(x:{y:⊤|y.ipv4_0.valid && y.stdmeta_0.valid && !y.stdmeta_1.valid}) -> {y:⊤|y.ipv4_0.valid && y.stdmeta_0.valid && (y.ipv4_0.ttl=0x00 =>
      y.stdmeta_1.valid && y.stdmeta_1.egress_spec=0b111111111)}"
      header_table
  in
  test_typecheck_ssa header_table prog.command ty

let test_ttl_safe3_ssa_ascribed () =
  let ingress =
    {|
        header_type ipv4_t {
          ttl: 2;
        }
        header_type standard_metadata_t {
          egress_spec: 2;
        }
        header ipv4_0 : ipv4_t
        header stdmeta_0 : standard_metadata_t
        header stdmeta_1 : standard_metadata_t
        add(stdmeta_1);
        if (ipv4_0.ttl == 0b00) {
            stdmeta_1.egress_spec := 0b11
        } else {
            stdmeta_1.egress_spec := 0b01
        }
      |}
  in
  let prog = Parsing.parse_program ingress in
  Fmt.pr "%a\n" Pretty.pp_command prog.command;
  let header_table = HeaderTable.of_decls prog.declarations in
  Logs.debug (fun m -> m "%a\n" Pretty.pp_header_table header_table);
  let ty =
    Parsing.parse_type
      "(x:{y:⊤|y.ipv4_0.valid && y.stdmeta_0.valid && !y.stdmeta_1.valid}) -> {y:⊤|y.ipv4_0.valid && y.stdmeta_0.valid && y.stdmeta_1.valid && ((y.ipv4_0.valid ∧ y.ipv4_0.ttl=0b00) =>
      y.stdmeta_1.egress_spec=0b11)}"
      header_table
  in
  test_typecheck_ssa header_table prog.command ty

(* TODO: ipv4_1.ttl := ipv4_0.ttl - 0x01 is missing *)
(* Adding this command produces some weird error *)
(* A similar bug seems to appear if we ascribe add(ipv4_1) with type  as (x:{y:⊤|y.ipv4_0.valid && y.ipv4_0.ttl == 0x00 && !y.ipv4_1.valid && y.stdmeta_0.valid && y.stdmeta_1.valid && y.stdmeta_1.egress_spec == 0b111111111}) -> {y:⊤|y.ipv4_0.valid && y.ipv4_0.ttl == 0x00 && y.ipv4_1.valid && y.stdmeta_0.valid && y.stdmeta_1.valid && y.stdmeta_1.egress_spec == 0b111111111}) *)
let test_ttl_safe_ssa () =
  let ingress =
    {|
        header_type ipv4_t {
          ttl: 8; 
        }
        header_type standard_metadata_t {
          egress_spec: 9;
        }
        header ipv4_0 : ipv4_t
        header ipv4_1 : ipv4_t
        header stdmeta_0 : standard_metadata_t
        header stdmeta_1 : standard_metadata_t
        if(ipv4_0.valid) {
          if(ipv4_0.ttl == 0x00) {
            (add(stdmeta_1) as (x:{y:⊤|y.ipv4_0.valid && y.ipv4_0.ttl == 0x00 && !y.ipv4_1.valid && y.stdmeta_0.valid && !y.stdmeta_1.valid}) -> {y:⊤|y.ipv4_0.valid && y.ipv4_0.ttl == 0x00 && !y.ipv4_1.valid && y.stdmeta_0.valid && y.stdmeta_1.valid});
            (stdmeta_1.egress_spec := 0b111111111 as (x:{y:⊤|y.ipv4_0.valid && y.ipv4_0.ttl == 0x00 && !y.ipv4_1.valid && y.stdmeta_0.valid && y.stdmeta_1.valid}) -> {y:⊤|y.ipv4_0.valid && y.ipv4_0.ttl == 0x00 && !y.ipv4_1.valid && y.stdmeta_0.valid && y.stdmeta_1.valid && y.stdmeta_1.egress_spec == 0b111111111});
            (if(ipv4_0.valid) {
              (add(ipv4_1));
              ipv4_1[0:8] := ipv4_0[0:8]
            } else {
              skip
            })
          } else {
            (add(stdmeta_1) as (x:{y:⊤|y.ipv4_0.valid && (!y.ipv4_0.ttl == 0x00) && !y.ipv4_1.valid && y.stdmeta_0.valid && !y.stdmeta_1.valid}) -> {y:⊤|y.ipv4_0.valid && (!y.ipv4_0.ttl == 0x00) && !y.ipv4_1.valid && y.stdmeta_0.valid && y.stdmeta_1.valid});
            (stdmeta_1.egress_spec := 0b000000001 as (x:{y:⊤|y.ipv4_0.valid && (!y.ipv4_0.ttl == 0x00) && !y.ipv4_1.valid && y.stdmeta_0.valid && y.stdmeta_1.valid}) -> {y:⊤|y.ipv4_0.valid && (!y.ipv4_0.ttl == 0x00) && !y.ipv4_1.valid && y.stdmeta_0.valid && y.stdmeta_1.valid && y.stdmeta_1.egress_spec == 0b000000001});
            (add(ipv4_1) as (x:{y:⊤|y.ipv4_0.valid && (!y.ipv4_0.ttl == 0x00) && !y.ipv4_1.valid && y.stdmeta_0.valid && y.stdmeta_1.valid && y.stdmeta_1.egress_spec == 0b000000001}) -> {y:⊤|y.ipv4_0.valid && (!y.ipv4_0.ttl == 0x00) && y.ipv4_1.valid && y.stdmeta_0.valid && y.stdmeta_1.valid && y.stdmeta_1.egress_spec == 0b000000001})
          }
        } else {
          (if(stdmeta_0.valid) {
            add(stdmeta_1);
            stdmeta_1[0:9] := stdmeta_0[0:9]
          } else {
            skip
          });
          (if(ipv4_0.valid) {
            add(ipv4_1);
            ipv4_1[0:8] := ipv4_0[0:8]
          } else {
            skip
          })
        }
      |}
  in
  let prog = Parsing.parse_program ingress in
  Fmt.pr "%a\n" Pretty.pp_command prog.command;
  let header_table = HeaderTable.of_decls prog.declarations in
  Logs.debug (fun m -> m "%a\n" Pretty.pp_header_table header_table);
  let ty =
    Parsing.parse_type
      "(x:{y:⊤|y.ipv4_0.valid && !y.ipv4_1.valid && y.stdmeta_0.valid && !y.stdmeta_1.valid}) -> {y:⊤|y.ipv4_0.valid && y.stdmeta_0.valid && (y.ipv4_0.ttl == 0x00 => y.stdmeta_1.egress_spec == 0b111111111) && ((!y.ipv4_0.ttl == 0x00) => y.stdmeta_1.egress_spec == 0b000000001)}"
      header_table
  in
  test_typecheck_ssa header_table prog.command ty

let test_ttl_unsafe_ssa () =
  let ingress =
    {|
        header_type ipv4_t {
          ttl: 8; 
        }
        header_type standard_metadata_t {
          egress_spec: 9;
        }
        header ipv4_0 : ipv4_t
        header ipv4_1 : ipv4_t
        header stdmeta_0 : standard_metadata_t
        header stdmeta_1 : standard_metadata_t
        if(ipv4_0.valid) {
          add(stdmeta_1);
          stdmeta_1.egress_spec := 0b000000001;
          add(ipv4_1)
        } else {
          (if(stdmeta_0.valid) {
            add(stdmeta_1);
            stdmeta_1[0:9] := stdmeta_0[0:9]
          } else {
            skip
          });
          (if(ipv4_0.valid) {
            add(ipv4_1);
            ipv4_1[0:8] := ipv4_0[0:8]
          } else {
            skip
          })
        }
      |}
  in
  let prog = Parsing.parse_program ingress in
  Fmt.pr "%a\n" Pretty.pp_command prog.command;
  let header_table = HeaderTable.of_decls prog.declarations in
  Logs.debug (fun m -> m "%a\n" Pretty.pp_header_table header_table);
  let ty =
    Parsing.parse_type
      (* It checks with the following type, which indeed describes the program's behavior"(x:{y:⊤|y.ipv4_0.valid && !y.ipv4_1.valid && y.stdmeta_0.valid && !y.stdmeta_1.valid}) -> {y:⊤|y.ipv4_0.valid && y.stdmeta_0.valid && (y.ipv4_0.valid => y.stdmeta_1.egress_spec == 0b000000001)}" *)
      "(x:{y:⊤|y.ipv4_0.valid && !y.ipv4_1.valid && y.stdmeta_0.valid && !y.stdmeta_1.valid}) -> {y:⊤|y.ipv4_0.valid && y.stdmeta_0.valid && (y.ipv4_0.ttl == 0x00 => y.stdmeta_1.egress_spec == 0b111111111) && ((!y.ipv4_0.ttl == 0x00) => y.stdmeta_1.egress_spec == 0b000000001)}"
      header_table
  in
  test_typecheck_ssa header_table prog.command ty

let test_set =
  [ test_case "Safe1" `Quick test_ttl_safe1;
    test_case "Safe1 SSA" `Quick test_ttl_safe1_ssa;
    test_case "Safe1 SSA Ascribed" `Quick test_ttl_safe1_ssa_ascribed;
    test_case "Safe2" `Quick test_ttl_safe2;
    test_case "Safe2 SSA" `Quick test_ttl_safe2_ssa;
    test_case "Safe3 SSA Ascribed" `Quick test_ttl_safe3_ssa_ascribed;
    test_case "Safe" `Quick test_ttl_safe_ssa;
    test_case "Unafe" `Quick test_ttl_unsafe_ssa;
  ]
