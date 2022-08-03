open Alcotest
open Pi4
open Syntax

module Config = struct
  let maxlen = ref(1500)
end

module P = Prover.Make (Encoding.FixedWidthBitvectorEncoding (Config))
module T = Typechecker.Make (Typechecker.SemanticChecker (Config))

let test_typecheck header_table cmd ty =
  Prover.make_prover "z3";
  Alcotest.(check Testable.typechecker_result)
    (Fmt.str "%a" (Pretty.pp_pi_type []) ty)
    Typechecker.TypecheckingResult.Success
    (T.check_type cmd ty header_table)

let test_not_typecheck header_table cmd ty =
  Prover.make_prover "z3";
  Alcotest.(check (neg Testable.typechecker_result))
    (Fmt.str "%a" (Pretty.pp_pi_type []) ty)
    Typechecker.TypecheckingResult.Success
    (T.check_type cmd ty header_table)
  

  
let safe_parser_string =
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
    header ether : ethernet_t
    header ipv4 : ipv4_t
    header ipv6 : ipv6_t

    extract(ether);
    if(ether.etherType == 0x86dd) {
      extract(ipv6)
    } else {
      if(ether.etherType == 0x0800) {
        extract(ipv4)
      }
    }|}

let safe_parser_type_string =
  {|
    (x:{y:ε| y.pkt_in.length > 432}) -> {y:⊤|!(y.ipv4.valid && y.ipv6.valid)}
  |}

let safe_ingress_string =
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
    header ether : ethernet_t
    header ipv4 : ipv4_t
    header ipv6 : ipv6_t
    if(!ipv4.valid) {
      add(ipv6);
      ether.etherType := 0x86dd
    }
  |}

let unsafe_ingress_string =
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
  header ether : ethernet_t
  header ipv4 : ipv4_t
  header ipv6 : ipv6_t
  add(ipv6);
  ether.etherType := 0x86dd
|}

let safe_ingress_type_string =
  {|(x:({y:ether~|!y.ipv4.valid && !y.ipv6.valid} + 
        {y:ether~|y.ipv4.valid && !y.ipv6.valid})) -> 
          {y:⊤|!(y.ipv4.valid && y.ipv6.valid)}|}

let unsafe_ingress_type_string =
  {| 
    (x:({y:⊤|y.ether.valid && !y.ipv4.valid && !y.ipv6.valid} + 
        {y:⊤|y.ether.valid && y.ipv4.valid && !y.ipv6.valid})) ->
          {y:⊤|y.ether.valid && y.ipv6.valid && y.ether.etherType == 0x86dd}
  |}

let unsafe_complete_string =
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
    header ether : ethernet_t
    header ipv4 : ipv4_t
    header ipv6 : ipv6_t

    ((extract(ether);
    if(ether.etherType == 0x86dd) {
      extract(ipv6)
    } else {
      if(ether.etherType == 0x0800) {
        extract(ipv4)
      }
    }) as (x:{y:ε| y.pkt_in.length > 432}) -> ({y:ether~ |!(y.ipv4.valid && y.ipv6.valid)}));
    (add(ipv6);
     ether.etherType := 0x86dd
     as (x: {y:ether~|!(y.ipv4.valid && y.ipv6.valid)}) ->  {y:ether~|!(y.ipv4.valid && y.ipv6.valid)});
    if(ether.valid){
      remit(ether)
    };
    if(ipv4.valid){
      remit(ipv4)
    };
    if(ipv6.valid){
      remit(ipv6)
    }   
   |}

let safe_complete_string =
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
    header ether : ethernet_t
    header ipv4 : ipv4_t
    header ipv6 : ipv6_t

    ((extract(ether);
    if(ether.etherType == 0x86dd) {
      extract(ipv6)
    } else {
      if(ether.etherType == 0x0800) {
        extract(ipv4)
      }
    }) as (x:{y:ε| y.pkt_in.length > 432}) -> ({y:ether~ |!(y.ipv4.valid && y.ipv6.valid)}));
    (if(!ipv4.valid && !ipv6.valid) {
      add(ipv6);
      ether.etherType := 0x86dd
    } as (x: {y:ether~|!(y.ipv4.valid && y.ipv6.valid)}) ->  {y:ether~|!(y.ipv4.valid && y.ipv6.valid)});
    if(ether.valid){
      remit(ether)
    };
    if(ipv4.valid){
      remit(ipv4)
    };
    if(ipv6.valid){
      remit(ipv6)
    }   
   |}
let safe_complete_type_string =
  {|
    (x:{y:ε| y.pkt_in.length > 432}) -> ⊤
  |}

  
let test_safe_parser () =
  let program = Parsing.parse_program safe_parser_string in
  Logs.debug (fun m -> m "%a" Pretty.pp_command program.command);
  let header_table = HeaderTable.of_decls program.declarations in
  let ty = Parsing.parse_type safe_parser_type_string header_table in
  test_typecheck header_table program.command ty

let test_safe_ingress () =
  let program = Parsing.parse_program safe_ingress_string in
  Logs.debug (fun m -> m "%a" Pretty.pp_command program.command);
  let header_table = HeaderTable.of_decls program.declarations in
  let ty = Parsing.parse_type safe_ingress_type_string header_table in
  test_typecheck header_table program.command ty

let test_unsafe_ingress () =
  let program = Parsing.parse_program unsafe_ingress_string in
  Logs.debug (fun m -> m "%a" Pretty.pp_command program.command);
  let header_table = HeaderTable.of_decls program.declarations in
  let ty = Parsing.parse_type unsafe_ingress_type_string header_table in
  test_typecheck header_table program.command ty

let test_safe_complete () =
  let program = Parsing.parse_program safe_complete_string in
  Logs.debug (fun m -> m "%a" Pretty.pp_command program.command);
  let header_table = HeaderTable.of_decls program.declarations in
  let ty = Parsing.parse_type safe_complete_type_string header_table in
  test_typecheck header_table program.command ty

let test_unsafe_complete () =
  let program = Parsing.parse_program unsafe_complete_string in
  Logs.debug (fun m -> m "%a" Pretty.pp_command program.command);
  let header_table = HeaderTable.of_decls program.declarations in
  let ty = Parsing.parse_type safe_complete_type_string header_table in
  test_not_typecheck header_table program.command ty


let test_set =
  [ test_case "Safe Parser" `Quick test_safe_parser;
    test_case "Safe Ingress" `Quick test_safe_ingress;
    test_case "Unsafe" `Quick test_unsafe_ingress;
    test_case "Safe Complete" `Quick test_safe_complete;
    test_case "Unsafe Compelte" `Quick test_unsafe_complete;
  ]
