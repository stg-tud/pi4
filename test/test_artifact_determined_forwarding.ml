open Alcotest
open Pi4
open Syntax

module Config = struct
  let verbose = true

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

let safe_string =
  {|
    header_type ipv4_t {
      version: 4;
      ihl: 4;
      tos: 8;
      len: 16;
      id: 16;
      flg: 3;
      off: 13;
      src: 32;
      dst: 32;
      ttl: 8
    }
    header_type standard_metadata_t {
      ingress_port: 9;
      egress_spec: 9;
      egress_port: 9;
      instance_type: 32;
      packet_length: 32;
      enq_timestamp: 32;
      enq_qdepth: 19;
      deq_timedelta: 32;
      deq_qdepth: 19;
      ingress_global_timestamp: 48;
      mcast_grp: 16;
      egress_rid: 16;
      checksum_error: 1;
      priority: 3;
    }
    header ipv4 : ipv4_t
    header stdmeta : standard_metadata_t

    if(ipv4.valid) {
      if(ipv4.dst != 0x0A0A0A0A) {
        stdmeta.egress_spec := 0b000000001
      } else {
        stdmeta.egress_spec := 0b111111111
      }
    }
  |}

let safe_type_string =
  {|
  (x:{y:ipv4~| y.stdmeta.valid}) -> {y:⊤| y.stdmeta.egress_spec != 0b000000000}
|}

let unsafe_string =
  {|
    header_type ipv4_t {
      version: 4;
      ihl: 4;
      tos: 8;
      len: 16;
      id: 16;
      flg: 3;
      off: 13;
      src: 32;
      dst: 32;
      ttl: 8                 
    }
    header_type standard_metadata_t {
      ingress_port: 9;
      egress_spec: 9;
      egress_port: 9;
      instance_type: 32;
      packet_length: 32;
      enq_timestamp: 32;
      enq_qdepth: 19;
      deq_timedelta: 32;
      deq_qdepth: 19;
      ingress_global_timestamp: 48;
      mcast_grp: 16;
      egress_rid: 16;
      checksum_error: 1;
      priority: 3;                 
    }
    header ipv4 : ipv4_t
    header stdmeta : standard_metadata_t
    if(ipv4.valid) {
      if(ipv4.dst != 0x0a0a0a0a) {
        stdmeta.egress_spec := 0b111111111
      }
    }
  |}

let unsafe_type_string =
  {|(x:{y:⊤|y.ipv4.valid && y.stdmeta.valid}) -> {y:⊤|(y.ipv4.dst != 0x0a0a0a0a) => y.stdmeta.egress_spec != 0b000000000}|}

let test_unsafe () =
  let program = Parsing.parse_program unsafe_string in
  Logs.debug (fun m -> m "%a" Pretty.pp_command program.command);
  let header_table = HeaderTable.of_decls program.declarations in
  let ty = Parsing.parse_type unsafe_type_string header_table in
  test_typecheck header_table program.command ty

let test_safe () =
  let program = Parsing.parse_program safe_string in
  Logs.debug (fun m -> m "%a" Pretty.pp_command program.command);
  let header_table = HeaderTable.of_decls program.declarations in
  let ty = Parsing.parse_type safe_type_string header_table in
  test_typecheck header_table program.command ty

let test_set =
  [ test_case "Safe" `Quick test_safe; test_case "Unsafe" `Quick test_unsafe ]
