open Alcotest
open Pi4
open Syntax

module Config = struct
  let verbose = true
  let maxlen = 320
end

module P = Prover.Make (Encoding.FixedWidthBitvectorEncoding (Config))
module T = Typechecker.MakeSSAChecker (Typechecker.CompleteChecker (Config))

module TT = Typechecker.Make(Typechecker.CompleteChecker (Config))         

            
let test_typecheck_ssa header_table cmd ty =
  Prover.make_prover "z3";
  Alcotest.(check Testable.typechecker_result)
    (Fmt.str "%a" (Pretty.pp_type []) ty)
    Typechecker.TypecheckingResult.Success
    (T.check_type cmd ty header_table)

let test_typecheck header_table cmd ty =
  Prover.make_prover "z3";
  Alcotest.(check Testable.typechecker_result)
    (Fmt.str "%a" (Pretty.pp_type []) ty)
    Typechecker.TypecheckingResult.Success
    (TT.check_type cmd ty header_table)

let safe_ssa_string =
(* {|  header_type standard_metadata_t {
 *       egress_spec: 1;
 *     }
 *     header stdmeta_0 : standard_metadata_t
 *     header stdmeta_1 : standard_metadata_t
 * 
 *     (add(stdmeta_1) as (x:{y:⊤|y.stdmeta_0.valid && !y.stdmeta_1.valid}) -> {y:⊤|y.stdmeta_0.valid && y.stdmeta_1.valid && y.pkt_in.length == x.pkt_in.length});
 *     stdmeta_1.egress_spec := 0b1
 *   |}   *)
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
    header ipv4_0 : ipv4_t
    header stdmeta_0 : standard_metadata_t
    header stdmeta_1 : standard_metadata_t
    if(ipv4_0.valid) {
      if(!ipv4_0.dst == 0x0a0a0a0a) {
        (add(stdmeta_1) as (x:{y:⊤|y.ipv4_0.valid && (!y.ipv4_0.dst == 0x0a0a0a0a) && y.stdmeta_0.valid && y.stdmeta_0.egress_spec == 0b000000000 && !y.stdmeta_1.valid}) -> {y:⊤|y.ipv4_0.valid && (!y.ipv4_0.dst == 0x0a0a0a0a) && y.stdmeta_0.valid && y.stdmeta_0.egress_spec == 0b000000000 && y.stdmeta_1.valid});
        stdmeta_1.egress_spec := 0b111111111
      } else {
        (add(stdmeta_1) as (x:{y:⊤|y.ipv4_0.valid && y.ipv4_0.dst == 0x0a0a0a0a && y.stdmeta_0.valid && y.stdmeta_0.egress_spec == 0b000000000 && !y.stdmeta_1.valid}) -> {y:⊤|y.ipv4_0.valid && y.ipv4_0.dst == 0x0a0a0a0a && y.stdmeta_0.egress_spec == 0b000000000 && y.stdmeta_0.valid && y.stdmeta_1.valid});
        stdmeta_1.egress_spec := 0b000000001
      }
    } else {
      if(stdmeta_0.valid) {
        add(stdmeta_1);
        stdmeta_1.egress_spec := stdmeta_0.egress_spec
      } else {
        if(stdmeta_0.valid) {
          add(stdmeta_1);
          stdmeta_1[0:1] := stdmeta_0[0:1]
        } else {
          skip
        }
      }  
    }
  |}

let safe_ssa_type_string = {|
  (x:{y:⊤|y.ipv4_0.valid && y.stdmeta_0.valid && y.stdmeta_0.egress_spec == 0b000000000 && !y.stdmeta_1.valid}) -> {y:⊤|y.ipv4_0.valid && y.stdmeta_1.valid && (!y.stdmeta_1.egress_spec == 0b000000000)}
|}
(* {|
 *   (x:{y:⊤| y.stdmeta_0.valid && !y.stdmeta_1.valid }) -> {y:⊤| y.stdmeta_1.valid && (!y.stdmeta_1.egress_spec == 0b0)}
 * |}   *)

let unsafe_ssa_string =   {|
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
    header ipv4_0 : ipv4_t
    header stdmeta_0 : standard_metadata_t
    header stdmeta_1 : standard_metadata_t
    if(ipv4_0.valid) {
      if(!ipv4_0.dst == 0x0a0a0a0a) {
        (add(stdmeta_1) as (x:{y:⊤|y.ipv4_0.valid && (!y.ipv4_0.dst == 0x0a0a0a0a) && y.stdmeta_0.valid && y.stdmeta_0.egress_spec == 0b000000000 && !y.stdmeta_1.valid}) -> {y:⊤|y.ipv4_0.valid && (!y.ipv4_0.dst == 0x0a0a0a0a) && y.stdmeta_0.valid && y.stdmeta_0.egress_spec == 0b000000000 && y.stdmeta_1.valid});
        stdmeta_1.egress_spec := 0b111111111
      } else {
        if(stdmeta_0.valid) {
          (add(stdmeta_1) as (x:{y:⊤|y.ipv4_0.valid && y.ipv4_0.dst == 0x0a0a0a0a && y.stdmeta_0.valid && y.stdmeta_0.egress_spec == 0b000000000 && !y.stdmeta_1.valid}) -> {y:⊤|y.ipv4_0.valid && y.ipv4_0.dst == 0x0a0a0a0a && y.stdmeta_0.valid && y.stdmeta_0.egress_spec == 0b000000000 && y.stdmeta_1.valid});
          stdmeta_1.egress_spec := stdmeta_0.egress_spec
        } else {
          skip
        }
      }
    } else {
      if(stdmeta_0.valid) {
        add(stdmeta_1);
        stdmeta_1.egress_spec := stdmeta_0.egress_spec
      } else {
        skip
      }
    }
  |}

let unsafe_ssa_type_string =
  {|(x:{y:⊤|y.ipv4_0.valid && y.stdmeta_0.valid && y.stdmeta_0.egress_spec == 0b000000000 && !y.stdmeta_1.valid}) -> {y:⊤|y.ipv4_0.valid && y.stdmeta_0.valid && y.stdmeta_1.valid && (!y.stdmeta_1.egress_spec == 0b000000000)}|}

let safe_string = {|
    header_type ipv4_t {
      dst: 1;
    }
    header_type standard_metadata_t {
      egress_spec: 1;
    }
    header ipv4 : ipv4_t
    header stdmeta : standard_metadata_t
    stdmeta.egress_spec := 0b1
  |}   

let safe_type_string =
  {|(x:{y:⊤|y.ipv4.valid && y.stdmeta.valid && y.stdmeta.egress_spec == 0b0}) -> {y:⊤|y.ipv4.valid && y.stdmeta.valid && (!y.stdmeta.egress_spec == 0b0)}|}

let unsafe_string =  {|
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
      if(!ipv4.dst == 0x0a0a0a0a) {
        stdmeta.egress_spec := 0b111111111
      } else {
        if(stdmeta.valid) {
          stdmeta.egress_spec := stdmeta.egress_spec
        } else {
          skip
        }
      }
    } else {
      if(stdmeta.valid) {
        add(stdmeta);
        stdmeta.egress_spec := stdmeta.egress_spec
      } else {
        skip
      }
    }
  |} 

let unsafe_type_string =
  {|(x:{y:⊤|y.ipv4.valid && y.stdmeta.valid && y.stdmeta.egress_spec == 0b000000000}) -> {y:⊤|y.ipv4.valid && y.stdmeta.valid && (!y.stdmeta.egress_spec == 0b000000000)}|}                   

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
  let ty = Parsing.parse_type unsafe_ssa_type_string header_table in 
  test_typecheck_ssa header_table program.command ty
 
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
  [
  test_case "Safe SSA" `Quick test_safe_ssa;
  test_case "Unsafe SSA" `Quick test_unsafe_ssa;
  test_case "Safe" `Quick test_safe;
  test_case "Unsafe" `Quick test_unsafe;
  (* test_case "to_ssa Safe is Safe_SSA" `Quick test_to_ssa; *)
]
