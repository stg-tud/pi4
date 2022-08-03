open Alcotest
open Pi4
open Syntax

module TestConfig = struct
  let verbose = true

  let maxlen = ref(64)
end

module Test = Test_utils.TestRunner (TestConfig)

let eth_inst = Test_utils.mk_inst "ether" [ ("etherType", 16) ]

let ipv4_inst =
  Test_utils.mk_inst "ipv4" [ ("version", 4); ("ihl", 4); ("dst", 32) ]

let header_table = HeaderTable.populate [ eth_inst; ipv4_inst ]

let parse_header_type hty_str = Parsing.parse_heap_type header_table [] hty_str

let test_parser () =
  let input =
    "header_type ether_t {
      etherType: 16;
    }
    header_type ipv4_t {
      version: 4;
      ihl: 4;
      dst: 32;
    }
    header ether : ether_t
    header ipv4 : ipv4_t
    extract(ether); 
    if(ether.etherType==0x0800){ 
      extract(ipv4) 
    }"
  in
  let prog = Parsing.parse_program input in
  let header_table = HeaderTable.of_decls prog.declarations in
  let ty =
    Parsing.parse_type
      {|
        (y:{x:ε|x.pkt_in.length>64}) →
          {y:⊤|y.ether.valid ∧ y.ipv4.valid ∧ y.ether.etherType == 0x0800} + {y:ether|y.ether.etherType!=0x0800}
      |}
      header_table
  in
  Test.typecheck header_table prog.command ty

let test_header_validty () =
  let input =
    "header_type ether_t {
      etherType: 16;
    }
    header_type ipv4_t {
      version: 4;
      ihl: 4;
      dst: 32;
    }
    header ether : ether_t
    header ipv4 : ipv4_t
    
    ipv4.dst := 0x0a0a0a0a"
  in
  let prog = Parsing.parse_program input in
  let header_table = HeaderTable.of_decls prog.declarations in
  let ty =
    Parsing.parse_type
      {|
        (x: (Σx:ether.({y:ipv4|x.ether.etherType == 0x0800} + 
          {z:ε|!x.ether.etherType == 0x0800}))) -> 
        {y:⊤|y.ipv4.dst == 0x0a0a0a0a}
      |}
      header_table
  in
  Test.not_typecheck header_table prog.command ty

let test_set =
  [ test_case "Parser typechecks" `Quick test_parser;
    test_case "Typechecking assignment fails" `Quick test_header_validty
  ]
