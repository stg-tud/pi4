open Alcotest
open Pi4
open Syntax

module Config = struct
  let maxlen = 1500
end

module P = Prover.Make (Encoding.FixedWidthBitvectorEncoding (Config))
module T = Typechecker.MakeSSAChecker (Typechecker.CompleteChecker (Config))

let test_typecheck_ssa header_table cmd ty =
  Prover.make_prover "z3";
  Alcotest.(check Testable.typechecker_result)
    (Fmt.str "%a" (Pretty.pp_type []) ty)
    Typechecker.TypecheckingResult.Success
    (T.check_type cmd ty header_table)

let safe_ssa_string = {|
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
    header ether_0 : ethernet_t
    header ether_1 : ethernet_t
    header ipv4_0 : ipv4_t
    header ipv4_1 : ipv4_t
    header ipv4opt_0 : ipv4opt_t
    header ipv4opt_1 : ipv4opt_t
    (extract(ether_1) as (x:{y:⊤|!y.ether_0.valid && !y.ether_1.valid && !y.ipv4_0.valid && !y.ipv4_1.valid && !y.ipv4opt_0.valid && !y.ipv4opt_1.valid && y.pkt_in.length > 280}) -> {y:⊤|!y.ether_0.valid && y.ether_1.valid && !y.ipv4_0.valid && !y.ipv4_1.valid && !y.ipv4opt_0.valid && !y.ipv4opt_1.valid && y.pkt_in.length > 168});
    if(ether_1[96:112] == 0x0800) {
      (extract(ipv4_1) as (x:{y:⊤|!y.ether_0.valid && y.ether_1.valid && y.ether_1[96:112]==0x0800 && !y.ipv4_0.valid && !y.ipv4_1.valid && !y.ipv4opt_0.valid && !y.ipv4opt_1.valid && y.pkt_in.length > 168}) -> {y:⊤|!y.ether_0.valid && y.ether_1.valid && y.ether_1[96:112]==0x0800 && !y.ipv4_0.valid && y.ipv4_1.valid && !y.ipv4opt_0.valid && !y.ipv4opt_1.valid && y.pkt_in.length > 8});
      if(ipv4_1[4:8] == 0b0101) {
        if(ipv4_0.valid) {
          add(ipv4opt_1);
          ipv4opt_1[0:8] := ipv4opt_0[0:8]
        } else {
          skip
        }
      } else {
        extract(ipv4opt_1)
      }
    } else {
      (if(ipv4opt_0.valid) {
        add(ipv4opt_1);
        ipv4opt_1[0:8] := ipv4opt_0[0:8]
      } else {
        skip
      });
      (if(ipv4_0.valid) {
        add(ipv4_1);
        ipv4_1[0:160] := ipv4_0[0:160]
      } else {
        skip
      })
    }|}

let safe_ssa_type_string =
  {|(x:{y:⊤|!y.ether_0.valid && !y.ether_1.valid && !y.ipv4_0.valid && !y.ipv4_1.valid && !y.ipv4opt_0.valid && !y.ipv4opt_1.valid && y.pkt_in.length > 280}) -> {y:⊤|((y.ipv4_1.valid && !y.ipv4_1[4:8]==0b0101) => y.ipv4opt_1.valid) && ((y.ipv4_1.valid && y.ipv4_1[4:8]==0b0101) => !y.ipv4opt_1.valid)}|}  

let unsafe_ssa_string = {|
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
    header ether_0 : ethernet_t
    header ether_1 : ethernet_t
    header ipv4_0 : ipv4_t
    header ipv4_1 : ipv4_t
    header ipv4opt_0 : ipv4opt_t
    header ipv4opt_1 : ipv4opt_t
    (extract(ether_1) as (x:{y:⊤|!y.ether_0.valid && !y.ether_1.valid && !y.ipv4_0.valid && !y.ipv4_1.valid && !y.ipv4opt_0.valid && !y.ipv4opt_1.valid && y.pkt_in.length > 280}) -> {y:⊤|!y.ether_0.valid && y.ether_1.valid && !y.ipv4_0.valid && !y.ipv4_1.valid && !y.ipv4opt_0.valid && !y.ipv4opt_1.valid && y.pkt_in.length > 168});
    if(ether_1[96:112] == 0x0800) {
      (extract(ipv4_1) as (x:{y:⊤|!y.ether_0.valid && y.ether_1.valid && y.ether_1[96:112]==0x0800 && !y.ipv4_0.valid && !y.ipv4_1.valid && !y.ipv4opt_0.valid && !y.ipv4opt_1.valid && y.pkt_in.length > 168}) -> {y:⊤|!y.ether_0.valid && y.ether_1.valid && y.ether_1[96:112]==0x0800 && !y.ipv4_0.valid && y.ipv4_1.valid && !y.ipv4opt_0.valid && !y.ipv4opt_1.valid && y.pkt_in.length > 8})
    } else {
      (if(ipv4_0.valid) {
        add(ipv4_1);
        ipv4_1[0:160] := ipv4_0[0:160]
      } else {
        skip
      })
    }
  |}  

let unsafe_ssa_type_string =
  {|(x:{y:⊤|!y.ether_0.valid && !y.ether_1.valid && !y.ipv4_0.valid && !y.ipv4_1.valid && !y.ipv4opt_0.valid && !y.ipv4opt_1.valid && y.pkt_in.length > 280}) -> {y:⊤|((y.ipv4_1.valid && !y.ipv4_1[4:8]==0b0101) => y.ipv4opt_1.valid) && ((y.ipv4_1.valid && y.ipv4_1[4:8]==0b0101) => !y.ipv4opt_1.valid)}|}  
                           
let test_safe_ssa () = 
  let program = Parsing.parse_program safe_ssa_string in
  Logs.debug (fun m -> m "%a" Pretty.pp_command program.command);
  let header_table = HeaderTable.of_decls program.declarations in
  let ty = Parsing.parse_type safe_ssa_type_string header_table  in 
  test_typecheck_ssa header_table program.command ty

let test_unsafe_ssa () = 
  let program = Parsing.parse_program unsafe_ssa_string in
  Logs.debug (fun m -> m "%a" Pretty.pp_command program.command);
  let header_table = HeaderTable.of_decls program.declarations in
  let ty = Parsing.parse_type unsafe_ssa_type_string  header_table in 
  test_typecheck_ssa header_table program.command ty

let test_set = [
  test_case "Safe SSA" `Quick test_safe_ssa;
  test_case "Unafe SSA" `Quick test_unsafe_ssa;
]
