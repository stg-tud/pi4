open Alcotest
open Pi4
open Syntax
open Core_kernel
open Result

module TestConfig = struct
  let verbose = true

  let maxlen = 22
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
    let tycout = C.compute_type program.command (x, annot_tyin) [] header_table ~smpl_subs:false in
    let simplified = C.compute_type program.command (x, annot_tyin) [] header_table ~smpl_subs:true in
    match tycout, simplified with
    | Ok (ht), Ok(smpl) -> 
      let ctx = [ (x, Env.VarBind annot_tyin) ] in
      Test.is_equiv ht smpl ctx header_table
    | _ -> ()

let default_header = 
  {|
    header_type  ethernet_t {
      dstAddr: 4;
      srcAddr: 4;
      etherType: 2;
    }
    header_type ipv4_t {
      version: 2; 
      ihl: 2; 
      tos: 4;
    }
    header_type ipv4opt_t{
      type: 2;
    }

    header ether : ethernet_t
    header ipv4 : ipv4_t
    header ipv4opt : ipv4opt_t
  |}

let ether_header =
  {|
  header_type  ethernet_t {
    dstAddr: 4;
    srcAddr: 4;
    etherType: 2;
  }
    header ether : ethernet_t
  |}

let default_type_str = 
  {|(x:{y:ε | y.pkt_in.length > 20}) -> 
    {y:⊤| true}|}
  
let extract_str =
  ether_header ^
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
  ether_header ^
  {|
    extract(ether);
    remit(ether)
  |}

let ext_assign_str =
  default_header ^
  {|
    extract(ipv4);
    ipv4.ihl := 0b11
  |}

let ext_if_str = 
  default_header ^
  {|
    extract(ether);
    if(ether.valid) {
      extract(ipv4)
    } else {
      add(ipv4)
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

let cplx1_str = 
  ether_header ^
  {|
    if(ether.valid) {
      extract(ether)
    } else {
      add(ether)
    };
    ether.srcAddr := 0b1010
  |}

let cplx2_str = 
  default_header ^
  {|
    extract(ether);
    if(ether.srcAddr == 0b1010) {
      extract(ipv4)
    } else {
      add(ipv4)
    };
    ipv4.ihl := 0b11
  |}

let cplx3_str = 
  default_header ^
  {|
    extract(ether);
    if(ether.srcAddr == 0b1010) {
      extract(ipv4);
      if(ipv4.ihl == 0b00) {
        add(ipv4opt)
      }
    } else {
      add(ipv4)
    };
    ipv4.ihl := 0b11
  |}
  
let cplx4_str = 
  default_header ^
  {|
    extract(ether);
    ether.dstAddr := 0b1011;
    remit(ether)
  |}


let cplx5_type_str = 
{|
  (x:{y:⊤ | y.ether.valid ∧
            y.ether.srcAddr != 0b0001 ∧
            y.ipv4.valid ∧
            y.pkt_out.length == 0 ∧
            y.pkt_in.length > 20 
            }) -> 
    {y:⊤| true}
|}


let cplx5_str = 
  default_header ^
  {|
    ether.dstAddr := 0b0000;
    if(ether.valid) {
      remit(ether)
    };
    if(ipv4.valid) {
      remit(ipv4)
    };
    reset;
    extract(ether);
    extract(ipv4);
    ipv4.ihl := 0b00
    |}

let cplx6_str = 
  default_header ^
  {|
    add(ether);
    extract(ipv4);
    reset;
    add(ether);
    extract(ipv4);
    ether.dstAddr := 0b1111;
    ipv4.ihl := 0b11;
    skip;
    remit(ipv4);
    if(ether.valid) {
      add(ipv4opt)
    }
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
    test_case "Complex 1" `Quick (types_equiv cplx1_str default_type_str);
    test_case "Complex 2" `Quick (types_equiv cplx2_str default_type_str);
    test_case "Complex 3" `Quick (types_equiv cplx3_str default_type_str);
    test_case "Complex 4" `Quick (types_equiv cplx4_str default_type_str);
    test_case "Complex 5" `Quick (types_equiv cplx5_str cplx5_type_str);
    test_case "Complex 6" `Quick (types_equiv cplx6_str default_type_str );
  ]