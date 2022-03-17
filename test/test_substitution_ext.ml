open Alcotest
open Pi4
open Syntax
open Core_kernel
open Result
module Log = (val Logs.src_log Logging.substitution_src : Logs.LOG)

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
      let ht = Substitution.fold_refinement ht in
      let simplified = Substitution.simplify_substitutions ht TestConfig.maxlen in
      Log.debug(fun m -> m "SMPL RAW: %a" Pretty.pp_header_type_raw simplified);
      Test.is_equiv ht simplified ctx header_table
    | Error(_) -> ()


let ipv4_ttl_hty_str = 
  {|
  (x:{y:⊤| y.ipv4.valid && y.meta.valid}) -> 
    {y:⊤|y.ipv4.valid &&y.meta.valid && ((x.ipv4.ttl==0x00) => (y.meta.egress_spec==0b111111111))}
  |}
let ipv4_ttl_str = 
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

let ipv4_opt_str = 
  {|
    header_type ethernet_t {
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
    header_type ipv4opt_t {
      type: 8;
    }
    header ether : ethernet_t
    header ipv4 : ipv4_t
    header ipv4opt : ipv4opt_t

    extract(ether);
    if(ether.etherType == 0x0800) {
      extract(ipv4);
      if(ipv4.ihl != 0x5) {
        extract(ipv4opt)
      }
    }
  |}

let ipv4_opt_hty_str = 
{|
(x:{y:ε | y.pkt_in.length > 280}) -> 
  {y:⊤|((y.ipv4.valid && y.ipv4.ihl!=0x5) => y.ipv4opt.valid) && ((y.ipv4.valid && y.ipv4.ihl==0x5) => !y.ipv4opt.valid)}
|}

let mod_router_table_str = 
  {|
    header_type vlan_t {
      vid: 2;
    }
    header_type meta_t {
      egress_spec: 9;
    }
    header_type vlan_tbl_t {
      vid: 2;
      act: 1;
    }

    header vlan : vlan_t
    header meta : meta_t
    header vlan_tbl : vlan_tbl_t

    if (vlan.vid == vlan_tbl.vid) {
      if (vlan_tbl.act == 0b0) {
        meta.egress_spec := 0b111111111
      } else {
        meta.egress_spec := 0b000000001
      }
    }
  |}
  
let mod_router_table_hty_str = 
  {|
  (x : {x:⊤| x.meta.valid ∧ x.vlan.valid ∧ x.vlan_tbl.valid }) -> { y:⊤ | y.vlan.valid ∧ x.vlan.vid == y.vlan.vid}
  |}


let test_set = 
  [
    test_case "ipv4_ttl" `Quick (types_equiv ipv4_ttl_str ipv4_ttl_hty_str);
    test_case "ipv4_opt" `Quick (types_equiv ipv4_opt_str ipv4_opt_hty_str);
    test_case "mod_router_table" `Quick (types_equiv mod_router_table_str mod_router_table_hty_str);
  ]