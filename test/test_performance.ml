open Alcotest
open Pi4
open Syntax

module Config = struct
  let maxlen = 1500
end

module P = Prover.Make (Encoding.FixedWidthBitvectorEncoding (Config))
module T = Typechecker.Make (Typechecker.SemanticChecker (Config))

let time f =
  let t = Unix.gettimeofday () in
  let res = f () in
  Printf.printf "Execution time: %f seconds\n"
                (Unix.gettimeofday () -. t);
  res

let test_typecheck header_table cmd ty =
  Prover.make_prover "z3";
  Alcotest.(check Testable.typechecker_result)
    (Fmt.str "%a" (Pretty.pp_pi_type []) ty)
    Typechecker.TypecheckingResult.Success(
    time(fun() -> (T.check_type cmd ty header_table)))

let test_typecheck_unopt header_table cmd ty =
  Prover.make_prover "z3";
  Alcotest.(check Testable.typechecker_result)
    (Fmt.str "%a" (Pretty.pp_pi_type []) ty)
    Typechecker.TypecheckingResult.Success(
    time(fun() -> (T.check_type cmd ty header_table ~smpl_subs:false)))

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
    header_type ipv4opt_t{
      type: 8;
    }

    header ether : ethernet_t
    header ipv4 : ipv4_t
    header ipv4opt : ipv4opt_t
  |}
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

let safe_type_string =
  {|(x:{y:ε | y.pkt_in.length > 280}) -> 
    {y:⊤|((y.ipv4.valid && y.ipv4.ihl!=0x5) => y.ipv4opt.valid) && ((y.ipv4.valid && y.ipv4.ihl==0x5) => !y.ipv4opt.valid)}|}

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
    header ipv4opt : ipv4opt_t
    extract(ether);
    if(ether.etherType == 0x0800) {
      extract(ipv4)
    }
  |}

let unsafe_type_string =
  {|(x:{y:⊤|!y.ether.valid && !y.ipv4.valid && !y.ipv4opt.valid && y.pkt_in.length > 280}) -> 
    {y:⊤|!y.ipv4opt.valid} |}

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
let test_safe () =
  let program = Parsing.parse_program safe_string in
  Logs.debug (fun m -> m "%a" Pretty.pp_command program.command);
  let header_table = HeaderTable.of_decls program.declarations in
  let ty = Parsing.parse_type safe_type_string header_table in
  test_typecheck header_table program.command ty

let test_safe_unopt () =
  let program = Parsing.parse_program safe_string in
  Logs.debug (fun m -> m "%a" Pretty.pp_command program.command);
  let header_table = HeaderTable.of_decls program.declarations in
  let ty = Parsing.parse_type safe_type_string header_table in
  test_typecheck_unopt header_table program.command ty

let test_unsafe () =
  let program = Parsing.parse_program unsafe_string in
  Logs.debug (fun m -> m "%a" Pretty.pp_command program.command);
  let header_table = HeaderTable.of_decls program.declarations in
  let ty = Parsing.parse_type unsafe_type_string header_table in
  test_typecheck header_table program.command ty

let test_unsafe_unopt () =
  let program = Parsing.parse_program unsafe_string in
  Logs.debug (fun m -> m "%a" Pretty.pp_command program.command);
  let header_table = HeaderTable.of_decls program.declarations in
  let ty = Parsing.parse_type unsafe_type_string header_table in
  test_typecheck_unopt header_table program.command ty

let test_set =
  [ 
    test_case "Safe" `Quick test_safe;
    test_case "Safe unopt" `Quick test_safe_unopt; 
    test_case "Unafe" `Quick test_unsafe;
    test_case "Unafe unopt" `Quick test_unsafe_unopt; 
  ]