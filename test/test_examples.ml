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

let test program_str type_str () =
  let program = Parsing.parse_program program_str in
  Logs.debug (fun m -> m "%a" Pretty.pp_command program.command);
  let header_table = HeaderTable.of_decls program.declarations in
  let ty = Parsing.parse_type type_str header_table in
  test_typecheck header_table program.command ty
    

(* 
ether: 112
ipv4: 160
ipv4opt: 8
vlan: 32
*)

(* {|
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
  header_type vlan_t {
    prio: 3; 
    id: 1; 
    vlan: 12; 
    etherType: 16;
  }
|} *)
let e1_extract =
  {|
    header_type  ethernet_t {
      dstAddr: 48;
      srcAddr: 48;
      etherType: 16;
    }

    header ether : ethernet_t

    extract(ether);
    remit(ether);
    remit(ether);
    skip
  |}
let e1_type =
  {|(x:{y:ε | y.pkt_in.length > 120}) -> 
    {y:⊤| y.ether.valid}|}
let e2_add =
  {|
    header_type ipv4opt_t {
      type: 8;
    }
    header ipv4opt : ipv4opt_t

    add(ipv4opt);
    skip
  |} 

let e2_type =
  {|(x:{y:ε | true}) ->
    {y:⊤|y.ipv4opt.valid => y.ipv4opt == 0x00}|}


let e3_if =
  {|
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
    header ipv4 : ipv4_t
    header ipv4opt : ipv4opt_t

    extract(ipv4);
    if(ipv4.ihl != 0x5) {
      extract(ipv4opt)
    } else {
      skip
    };
    skip
  |} 

let e3_type =
  {|(x:{y:ε | y.pkt_in.length > 168}) ->
    {y:⊤|((y.ipv4.valid && y.ipv4.ihl!=0x5) => y.ipv4opt.valid) && ((y.ipv4.valid && y.ipv4.ihl==0x5) => !y.ipv4opt.valid)}|}


let e4_assign = 
  {|
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
    header ipv4 : ipv4_t

    ipv4.version := 0b1111;
    skip
  |}

let e4_type =
  {|(x:{y:⊤ | y.ipv4.valid }) ->
    {y:⊤|y.ipv4.version == 0b1111}|}


let e5_mextract =
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
    header ether : ethernet_t
    header ipv4 : ipv4_t

    extract(ether);
    if(ether.etherType == 0x0800) {
      extract(ipv4)
    };
    skip
  |}

let e5_type = 
  {|(x:{y:ε | y.pkt_in.length > 280}) -> 
    {y:⊤|((y.ether.valid && y.ether.etherType == 0x0800) => y.ipv4.valid)}|}


let test_set =
  [ 
    test_case "E1 Extract" `Quick (test e1_extract e1_type);
    test_case "E2 Add" `Quick (test e2_add e2_type);
    test_case "E3 If" `Quick (test e3_if e3_type);
    test_case "E4 Assign" `Quick (test e4_assign e4_type);
    test_case "E5 Multiple Extracts" `Quick (test e5_mextract e5_type);
  ]
    