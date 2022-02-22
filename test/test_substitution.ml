open Alcotest
open Pi4
open Syntax
open Core_kernel
open Result

module TestConfig = struct
  let verbose = true

  let maxlen = 1500
end

module Config = struct
  let maxlen = TestConfig.maxlen
end

module P = Prover.Make (Encoding.FixedWidthBitvectorEncoding (Config))
module C = Typechecker.SemanticChecker (Config)

module Test = Test_utils.TestRunner (TestConfig)

let types_equiv program_str type_str ()= 
  let program = Parsing.parse_program program_str in
  let header_table = HeaderTable.of_decls program.declarations in
  let ty = Parsing.parse_type type_str header_table in
  match ty with
  | Pi (x, annot_tyin, _) ->  
    let tycout = C.compute_type program.command (x, annot_tyin) [] header_table
    in
    match tycout with
    | Ok ht -> 
      let ctx = [ (x, Env.VarBind annot_tyin) ] in
      let simplified = Substitution.simplify ht TestConfig.maxlen in
      Test.is_equiv ht simplified ctx header_table
    | Error(_) -> ()

let default_header = 
  {|
    header_type  ethernet_t {
      dstAddr: 48;
      srcAddr: 48;
      etherType: 16;
    }
    header_type ipv4_t {
      version: 4; 
      ihl: 4; 
      tos: 8; 
      len: 16; 
      id: 16; 
      flags: 3; 
      frag: 13; 
      ttl: 8; 
      proto: 8; 
      chksum: 16; 
      src: 32; 
      dst: 32;
    }

    header ether : ethernet_t
    header ipv4 : ipv4_t
  |}

let eth_header =
  {|
  header_type  ethernet_t {
    dstAddr: 48;
    srcAddr: 48;
    etherType: 16;
  }
    header ether : ethernet_t
  |}
let default_type_str = 
  {|(x:{y:ε | y.pkt_in.length > 272}) -> 
    {y:⊤| true}|}
  
let extract_str =
  eth_header ^
  {|
    extract(ether);
    skip
  |}
let extract_extract_str =
  default_header ^
  {|
    extract(ether);
    extract(ipv4)
  |}
let extract_add_str =
  default_header ^
  {|
    extract(ether);
    add(ipv4)
  |}

let extract_skip_str =
  default_header ^
  {|
    extract(ether);
    skip
  |}

let extract_remit_str =
  default_header ^
  {|
    extract(ether);
    remit(ether)
  |}

let ext_assign_str =
  default_header ^
  {|
    extract(ipv4);
    ipv4.flags := 0b111
  |}

let ext_if_str = 
  default_header ^
  {|
    extract(ether);
    if(ether.valid) {
      skip
    } else {
      skip
    }
  |}

let add_skip_str =
  default_header ^
  {|
    add(ether);
    skip
  |}

let add_extract_str =
  default_header ^
  {|
    add(ether);
    extract(ether)
  |}

let test_set = 
  [
    test_case "Extract" `Quick (types_equiv extract_str default_type_str);
    test_case "Extract-Extract" `Quick (types_equiv extract_extract_str default_type_str);
    test_case "Extract-Add" `Quick (types_equiv extract_add_str default_type_str);
    test_case "Extract-Skip" `Quick (types_equiv extract_skip_str default_type_str);
    test_case "Extract-Remit" `Quick (types_equiv extract_remit_str default_type_str);
    test_case "Extract-Assign" `Quick (types_equiv ext_assign_str default_type_str);
    test_case "Extract-If" `Quick (types_equiv ext_if_str default_type_str);
    test_case "Add-Skip" `Quick (types_equiv add_skip_str default_type_str);
    test_case "Add-Extract" `Quick (types_equiv add_extract_str default_type_str);
  ]