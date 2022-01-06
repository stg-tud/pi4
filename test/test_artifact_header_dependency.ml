open Alcotest
open Pi4
open Syntax

module Config = struct
  let maxlen = 1500
end

module P = Prover.Make (Encoding.FixedWidthBitvectorEncoding (Config))
module T = Typechecker.Make (Typechecker.SemanticChecker (Config))

let test_typecheck_ssa header_table cmd ty =
  Prover.make_prover "z3";
  Alcotest.(check Testable.typechecker_result)
    (Fmt.str "%a" (Pretty.pp_pi_type []) ty)
    Typechecker.TypecheckingResult.Success
    (T.check_type cmd ty header_table)

let safe_string =
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
    }
  |}

let safe_type_string =
  {|(x:{y:⊤|!y.ether.valid && !y.ipv4.valid && y.pkt_in.length > 272}) -> {y:⊤|y.ipv4.valid => y.ether.etherType == 0x0800}|}

let unsafe_string =
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
    extract(ether);
    extract(ipv4)
  |}

let unsafe_ssa_type_string =
  (* {|(x:{y:⊤|!y.ether.valid && !y.ipv4.valid && y.pkt_in.length > 272}) ->
     {y:⊤|y.ipv4.valid => y.ether.etherType == 0x0800}|} *)
  {| (x:{y:⊤|!y.ether.valid && !y.ipv4.valid && y.pkt_in.length > 272}) -> {y:⊤|y.ether.valid && y.ipv4.valid} |}

let test_safe () =
  let program = Parsing.parse_program safe_string in
  Logs.debug (fun m -> m "%a" Pretty.pp_command program.command);
  let header_table = HeaderTable.of_decls program.declarations in
  let ty = Parsing.parse_type safe_type_string header_table in
  test_typecheck_ssa header_table program.command ty

let test_unsafe () =
  let program = Parsing.parse_program unsafe_string in
  Logs.debug (fun m -> m "%a" Pretty.pp_command program.command);
  let header_table = HeaderTable.of_decls program.declarations in
  let ty = Parsing.parse_type unsafe_ssa_type_string header_table in
  test_typecheck_ssa header_table program.command ty

let test_set =
  [ test_case "Safe" `Quick test_safe; test_case "Unafe" `Quick test_unsafe ]
