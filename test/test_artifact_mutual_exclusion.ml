open Alcotest
open Pi4
open Syntax

module Config = struct
  let maxlen = 32
end

module P = Prover.Make (Encoding.FixedWidthBitvectorEncoding (Config))
module T = Typechecker.MakeSSAChecker (Typechecker.CompleteChecker (Config))

let test_typecheck_ssa header_table cmd ty =
  Prover.make_prover "z3";
  Alcotest.(check Testable.typechecker_result)
    (Fmt.str "%a" (Pretty.pp_type []) ty)
    Typechecker.TypecheckingResult.Success
    (T.check_type cmd ty header_table)

let safe_parser_ssa_string = {|
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
    header_type ipv6_t {
      version: 4;
      trafficClass: 8;
      flowLable: 20;
      payloadLength: 16;
      nextHeader: 8;
      hopLimit: 8;
      srcAddr: 128;
      dstAddr: 128; 
    }
    header ether_0 : ethernet_t
    header ether_1 : ethernet_t
    header ipv4_0 : ipv4_t
    header ipv4_1 : ipv4_t
    header ipv6_0 : ipv6_t
    header ipv6_1 : ipv6_t

    (extract(ether_1) as (x:{y:⊤|!y.ether_0.valid && !y.ether_1.valid && !y.ipv4_0.valid && !y.ipv4_1.valid && !y.ipv6_0.valid && !y.ipv6_1.valid && y.pkt_in.length > 432}) -> {y:⊤|!y.ether_0.valid && y.ether_1.valid && !y.ipv4_0.valid && !y.ipv4_1.valid && !y.ipv6_0.valid && !y.ipv6_1.valid && y.pkt_in.length > 320});
    if(ether_1.etherType == 0x86dd) {
      extract(ipv6_1);
      (if(ipv4_0.valid) {
        add(ipv4_1);
        ipv4_1[0:160] := ipv4_0[0:160]
      } else {
        skip
      })
    } else {
      if(ether_1.etherType == 0x0800) {
        extract(ipv4_1)
      } else {
        (if(ipv4_0.valid) {
          add(ipv4_1);
          ipv4_1[0:160] := ipv4_0[0:160]
        } else {
          skip
        });
        (if(ipv6_0.valid) {
          add(ipv6_1);
          ipv6_1[0:320] := ipv6_0[0:320]
        } else {
          skip
        })
      }
    }|}

let safe_parser_ssa_type_string =
  {|(x:{y:⊤|!y.ether_0.valid && !y.ether_1.valid && !y.ipv4_0.valid && !y.ipv4_1.valid && !y.ipv6_0.valid && !y.ipv6_1.valid && y.pkt_in.length > 432}) -> {y:⊤|!(y.ipv4_1.valid && y.ipv6_1.valid)}|}  

let safe_ingress_ssa_string = {|
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
  header_type ipv6_t {
    version: 4;
    trafficClass: 8;
    flowLable: 20;
    payloadLength: 16;
    nextHeader: 8;
    hopLimit: 8;
    srcAddr: 128;
    dstAddr: 128; 
  }
  header ether_0 : ethernet_t
  header ether_1 : ethernet_t
  header ipv4_0 : ipv4_t
  header ipv6_0 : ipv6_t
  header ipv6_1 : ipv6_t
  if(!ipv4_0.valid) {
    (((((add(ipv6_1) as (x:({y:⊤|y.ether_0.valid && !y.ether_1.valid && !y.ipv4_0.valid && !y.ipv6_0.valid && !y.ipv6_1.valid} + {y:⊤|y.ether_0.valid && !y.ether_1.valid && !y.ipv4_0.valid && y.ipv6_0.valid && !y.ipv6_1.valid})) -> ({y:⊤|y.ether_0.valid && !y.ether_1.valid && !y.ipv4_0.valid && !y.ipv6_0.valid && y.ipv6_1.valid} + {y:⊤|y.ether_0.valid && !y.ether_1.valid && !y.ipv4_0.valid && y.ipv6_0.valid && y.ipv6_1.valid}));
    (add(ether_1) as (x:{y:⊤|y.ether_0.valid && !y.ether_1.valid && !y.ipv4_0.valid && !y.ipv6_0.valid && y.ipv6_1.valid} + {y:⊤|y.ether_0.valid && !y.ether_1.valid && !y.ipv4_0.valid && y.ipv6_0.valid && y.ipv6_1.valid}) -> {y:⊤|y.ether_0.valid && y.ether_1.valid && !y.ipv4_0.valid && !y.ipv6_0.valid && y.ipv6_1.valid} + {y:⊤|y.ether_0.valid && y.ether_1.valid && !y.ipv4_0.valid && y.ipv6_0.valid && y.ipv6_1.valid})) as (x:({y:⊤|y.ether_0.valid && !y.ether_1.valid && !y.ipv4_0.valid && !y.ipv6_0.valid && !y.ipv6_1.valid} + {y:⊤|y.ether_0.valid && !y.ether_1.valid && !y.ipv4_0.valid && y.ipv6_0.valid && !y.ipv6_1.valid})) -> {y:⊤|y.ether_0.valid && y.ether_1.valid && !y.ipv4_0.valid && !y.ipv6_0.valid && y.ipv6_1.valid} + {y:⊤|y.ether_0.valid && y.ether_1.valid && !y.ipv4_0.valid && y.ipv6_0.valid && y.ipv6_1.valid});
    ether_1.etherType := 0x86dd) as (x:({y:⊤|y.ether_0.valid && !y.ether_1.valid && !y.ipv4_0.valid && !y.ipv6_0.valid && !y.ipv6_1.valid} + {y:⊤|y.ether_0.valid && !y.ether_1.valid && !y.ipv4_0.valid && y.ipv6_0.valid && !y.ipv6_1.valid})) -> {y:⊤|y.ether_0.valid && y.ether_1.valid && !y.ipv4_0.valid && !y.ipv6_0.valid && y.ipv6_1.valid} + {y:⊤|y.ether_0.valid && y.ether_1.valid && !y.ipv4_0.valid && y.ipv6_0.valid && y.ipv6_1.valid});
    ether_1[0:96] := ether_0[0:96]
  } else {
    if(ipv6_0.valid) {
      add(ipv6_1);
      ipv6_1[0:320] := ipv6_0[0:320]
    } else {
      skip
    };
    if(ether_0.valid) {
      add(ether_1);
      ether_1[0:112] := ether_0[0:112]
    } else {
      skip
    }
  }|}  

let unsafe_ingress_ssa_string = {|
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
  header_type ipv6_t {
    version: 4;
    trafficClass: 8;
    flowLable: 20;
    payloadLength: 16;
    nextHeader: 8;
    hopLimit: 8;
    srcAddr: 128;
    dstAddr: 128; 
  }
  header ether_0 : ethernet_t
  header ether_1 : ethernet_t
  header ipv4_0 : ipv4_t
  header ipv6_0 : ipv6_t
  header ipv6_1 : ipv6_t
  (add(ipv6_1) as (x:{y:⊤|y.ether_0.valid && !y.ether_1.valid && !y.ipv4_0.valid && !y.ipv6_0.valid && !y.ipv6_1.valid} + {y:⊤|y.ether_0.valid && !y.ether_1.valid && y.ipv4_0.valid && !y.ipv6_0.valid && !y.ipv6_1.valid} + {y:⊤|y.ether_0.valid && !y.ether_1.valid && !y.ipv4_0.valid && y.ipv6_0.valid && !y.ipv6_1.valid}) -> {y:⊤|y.ether_0.valid && !y.ether_1.valid && !y.ipv4_0.valid && !y.ipv6_0.valid && y.ipv6_1.valid} + {y:⊤|y.ether_0.valid && !y.ether_1.valid && y.ipv4_0.valid && !y.ipv6_0.valid && y.ipv6_1.valid} + {y:⊤|y.ether_0.valid && !y.ether_1.valid && !y.ipv4_0.valid && y.ipv6_0.valid && y.ipv6_1.valid});
  (add(ether_1) as (x: {y:⊤|y.ether_0.valid && !y.ether_1.valid && !y.ipv4_0.valid && !y.ipv6_0.valid && y.ipv6_1.valid} + {y:⊤|y.ether_0.valid && !y.ether_1.valid && y.ipv4_0.valid && !y.ipv6_0.valid && y.ipv6_1.valid} + {y:⊤|y.ether_0.valid && !y.ether_1.valid && !y.ipv4_0.valid && y.ipv6_0.valid && y.ipv6_1.valid}) -> {y:⊤|y.ether_0.valid && y.ether_1.valid && !y.ipv4_0.valid && !y.ipv6_0.valid && y.ipv6_1.valid} + {y:⊤|y.ether_0.valid && y.ether_1.valid && y.ipv4_0.valid && !y.ipv6_0.valid && y.ipv6_1.valid} + {y:⊤|y.ether_0.valid && y.ether_1.valid && !y.ipv4_0.valid && y.ipv6_0.valid && y.ipv6_1.valid});
  ether_1.etherType := 0x86dd;
  ether_1[0:96] := ether_0[0:96]
|}  

let safe_ingress_ssa_type_string =
  {|(x:({y:⊤|y.ether_0.valid && !y.ether_1.valid && !y.ipv4_0.valid && !y.ipv6_0.valid && !y.ipv6_1.valid} + {y:⊤|y.ether_0.valid && !y.ether_1.valid && y.ipv4_0.valid && !y.ipv6_0.valid && !y.ipv6_1.valid} + {y:⊤|y.ether_0.valid && !y.ether_1.valid && !y.ipv4_0.valid && y.ipv6_0.valid && !y.ipv6_1.valid})) -> {y:⊤|!(y.ipv4_0.valid && y.ipv6_1.valid)}|}

let unsafe_ingress_ssa_type_string = 
  {| (x:{y:⊤|y.ether_0.valid && !y.ether_1.valid && !y.ipv4_0.valid && !y.ipv6_0.valid && !y.ipv6_1.valid} + {y:⊤|y.ether_0.valid && !y.ether_1.valid && y.ipv4_0.valid && !y.ipv6_0.valid && !y.ipv6_1.valid} + {y:⊤|y.ether_0.valid && !y.ether_1.valid && !y.ipv4_0.valid && y.ipv6_0.valid && !y.ipv6_1.valid}) -> {y:⊤|y.ether_0.valid && y.ether_1.valid && !y.ipv4_0.valid && !y.ipv6_0.valid && y.ipv6_1.valid} + {y:⊤|y.ether_0.valid && y.ether_1.valid && y.ipv4_0.valid && !y.ipv6_0.valid && y.ipv6_1.valid} + {y:⊤|y.ether_0.valid && y.ether_1.valid && !y.ipv4_0.valid && y.ipv6_0.valid && y.ipv6_1.valid}|}

let test_safe_parser_ssa () = 
  let program = Parsing.parse_program safe_parser_ssa_string in
  Logs.debug (fun m -> m "%a" Pretty.pp_command program.command);
  let header_table = HeaderTable.of_decls program.declarations in
  let ty = Parsing.parse_type safe_parser_ssa_type_string header_table  in 
  test_typecheck_ssa header_table program.command ty

let test_safe_ingress_ssa () = 
  let program = Parsing.parse_program safe_ingress_ssa_string in
  Logs.debug (fun m -> m "%a" Pretty.pp_command program.command);
  let header_table = HeaderTable.of_decls program.declarations in
  let ty = Parsing.parse_type safe_ingress_ssa_type_string header_table  in 
  test_typecheck_ssa header_table program.command ty

let test_unsafe_ingress_ssa () = 
  let program = Parsing.parse_program unsafe_ingress_ssa_string in
  Logs.debug (fun m -> m "%a" Pretty.pp_command program.command);
  let header_table = HeaderTable.of_decls program.declarations in
  let ty = Parsing.parse_type safe_ingress_ssa_type_string  header_table in 
  test_typecheck_ssa header_table program.command ty

let test_set = [
  test_case "Safe Parser SSA" `Quick test_safe_parser_ssa;
  test_case "Safe Parser SSA" `Quick test_safe_ingress_ssa;
  test_case "Unsafe SSA" `Quick test_unsafe_ingress_ssa;
]
