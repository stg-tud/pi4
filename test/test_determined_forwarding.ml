open Alcotest
open Pi4
open Syntax

module TestConfig = struct
  let verbose = true

  let maxlen = 112
end

module Test = Test_utils.TestRunner (TestConfig)

let eth_inst =
  Test_utils.mk_inst "ether"
    [ ("dstAddr", 48); ("srcAddr", 48); ("etherType", 16) ]

let stdmeta_inst = Test_utils.mk_inst "stdmeta" [ ("egressSpec", 9) ]

let header_table = HeaderTable.populate [ eth_inst; stdmeta_inst ]

let parse_header_type hty_str =
  Parsing.header_type_of_string hty_str header_table []

let test_determined_forwarding () =
  let prog =
    Parsing.parse_program
      "header_type ether_t { 
        dstAddr: 48;
        srcAddr: 48;
        etherType: 16;
      }
      header_type stdmeta_t {
        egressSpec: 9;
      }

      header ether : ether_t
      header stdmeta : stdmeta_t

      extract(ether);
      if(ether.srcAddr == 0x0123456789ab) {
        stdmeta.egressSpec := 0b111111111
      } else {
        stdmeta.egressSpec := 0b000000001
      }"
  in
  let header_table = HeaderTable.of_decls prog.declarations in
  Logs.debug (fun m -> m "ht");

  let ty =
    Parsing.parse_type
      "(x:{y: stdmeta|y.stdmeta.egressSpec==0b111111110 && y.pkt_in.length>111}) -> 
      {z:?ether|!z.stdmeta.egressSpec == 0b111111110}"
      header_table
  in
  Test.typecheck header_table prog.command ty

let test_set =
  [ test_case "Determined forwarding" `Quick test_determined_forwarding ]
