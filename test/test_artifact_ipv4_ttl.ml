open Alcotest
open Pi4
open Syntax

module TestConfig = struct
  let verbose = true

  let maxlen = ref(272)
end

module Test = Test_utils.TestRunner (TestConfig)

module Config = struct
  let maxlen = ref(320)
end

module P = Prover.Make (Encoding.FixedWidthBitvectorEncoding (Config))
module T = Typechecker.Make (Typechecker.SemanticChecker (Config))

let test_typecheck_ssa header_table cmd ty =
  Prover.make_prover "z3";
  Alcotest.(check Testable.typechecker_result)
    (Fmt.str "%a" (Pretty.pp_pi_type []) ty)
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

let meta_inst = Test_utils.mk_inst "meta" [ ("egressSpec", 9) ]

let header_table = HeaderTable.populate [ eth_inst; ipv4_inst; meta_inst ]

let parse_heap_type s = Parsing.parse_heap_type header_table [] s

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
      header meta : standard_metadata_t
      meta.egress_spec := 0b111111111
    |}
  in
  let prog = Parsing.parse_program ingress in
  Fmt.pr "%a\n" Pretty.pp_command prog.command;
  let header_table = HeaderTable.of_decls prog.declarations in
  Logs.debug (fun m -> m "%a\n" Pretty.pp_header_table header_table);
  let ty =
    Parsing.parse_type
      {| 
        (x:{y:⊤|y.ipv4.valid ∧ y.meta.valid}) ->
          {y:⊤|y.ipv4.valid ∧ y.meta.valid ∧ (y.ipv4.ttl==0x00 => y.meta.egress_spec==0b111111111)}
      |}
      header_table
  in
  Test.typecheck header_table prog.command ty

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
      header meta : standard_metadata_t
      if(ipv4[0:8]==0x00) {
        meta.egress_spec := 0b111111111
      }
    |}
  in
  let prog = Parsing.parse_program ingress in
  Fmt.pr "%a\n" Pretty.pp_command prog.command;
  let header_table = HeaderTable.of_decls prog.declarations in
  Logs.debug (fun m -> m "%a\n" Pretty.pp_header_table header_table);
  let ty =
    Parsing.parse_type
      {| 
        (x:{y:⊤|y.ipv4.valid ∧ y.meta.valid}) ->
          {y:⊤|y.ipv4.valid ∧ y.meta.valid ∧ (y.ipv4.ttl==0x00 => y.meta.egress_spec==0b111111111)}
      |}
      header_table
  in
  Test.typecheck header_table prog.command ty

let test_ttl_safe () =
  let ingress =
    {|
        header_type ipv4_t {
          ttl: 8; 
        }
        header_type standard_metadata_t {
          egress_spec: 9;
        }
        header ipv4 : ipv4_t
        header meta : standard_metadata_t
        if(ipv4.valid) {
          if(ipv4.ttl == 0x00) {
            meta.egress_spec := 0b111111111
          } else {
            meta.egress_spec := 0b000000001;
            ipv4.ttl := ipv4.ttl - 0x01
          }
        }
      |}
  in
  let prog = Parsing.parse_program ingress in
  Fmt.pr "%a\n" Pretty.pp_command prog.command;
  let header_table = HeaderTable.of_decls prog.declarations in
  Logs.debug (fun m -> m "%a\n" Pretty.pp_header_table header_table);
  let ty =
    Parsing.parse_type
      {| 
        (x:{y:ipv4~| y.meta.valid}) ->
          {y:ipv4~|
                y.meta.valid && 
                ((x.ipv4.ttl==0x00) => (y.meta.egress_spec==0b111111111))}
      |}
      header_table
  in
  test_typecheck_ssa header_table prog.command ty

let test_ttl_unsafe () =
  let ingress =
    {|
        header_type ipv4_t {
          ttl: 8; 
        }
        header_type standard_metadata_t {
          egress_spec: 9;
        }
        header ipv4 : ipv4_t
        header meta : standard_metadata_t
        if(ipv4.valid) {
          meta.egress_spec := 0b000000001;
          ipv4.ttl := ipv4.ttl - 0x01
        }
      |}
  in
  let prog = Parsing.parse_program ingress in
  Fmt.pr "%a\n" Pretty.pp_command prog.command;
  let header_table = HeaderTable.of_decls prog.declarations in
  Logs.debug (fun m -> m "%a\n" Pretty.pp_header_table header_table);
  let ty =
    Parsing.parse_type
      "(x:{y:⊤|y.ipv4.valid && y.meta.valid}) -> {y:⊤|y.ipv4.valid && y.meta.valid && (y.ipv4.valid => y.meta.egress_spec == 0b000000001)}"
      (* "(x:{y:⊤|y.ipv4.valid && y.meta.valid}) -> {y:⊤|y.ipv4.valid &&
         y.meta.valid && ((y.ipv4.ttl == 0x00) => y.meta.egress_spec ==
         0b111111111) && ((y.ipv4.ttl != 0x00) => y.meta.egress_spec ==
         0b000000001)}" *)
      (* "(x:{y:ipv4~| y.meta.valid}) ->
       *   {y:ipv4~|
       *         y.meta.valid && 
       *         ((x.ipv4.ttl==0x00) => (y.meta.egress_spec==0b111111111))}" *)
      header_table
  in
  test_typecheck_ssa header_table prog.command ty

let test_set =
  [ test_case "Safe1" `Quick test_ttl_safe1;
    test_case "Safe2" `Quick test_ttl_safe2;
    test_case "Safe" `Quick test_ttl_safe;
    test_case "Unafe" `Quick test_ttl_unsafe
  ]
