open Alcotest
open Pi4
open Syntax

module TestConfig = struct
  let verbose = true

  let maxlen = 272
end

module Test = Test_utils.TestRunner (TestConfig)

let eth_inst =
  Test_utils.mk_inst "ether"
    [ ("dstAddr", 48); ("srcAddr", 48); ("etherType", 16) ]

let ipv4_inst =
  Test_utils.mk_inst "ipv4"
    [ ("version", 4);
      ("ihl", 4);
      ("tos", 8);
      ("len", 16);
      ("id", 16);
      ("flags", 3);
      ("frag", 13);
      ("ttl", 8);
      ("proto", 8);
      ("chksum", 16);
      ("src", 32);
      ("dst", 32)
    ]

let header_table = HeaderTable.populate [ eth_inst; ipv4_inst ]

let parse_header_type hty_str =
  Parsing.header_type_of_string hty_str header_table []

let test_dependency_violated () =
  let hty_prog = "ipv4" in
  let hty_inv =
    parse_header_type
      (Printf.sprintf
         "{y:%s|y.ipv4.valid => (y.ether.valid && y.ether.etherType==0x0800)}"
         hty_prog)
  in
  Logs.debug (fun m -> m "%a" (Pretty.pp_header_type []) hty_inv);
  Test.is_equiv hty_inv Nothing [] header_table

let test_dependency_not_violated () =
  let hty_prog = "\\sigma x:ether.{y:ipv4|x.ether.etherType==0x0800}" in
  let hty_inv =
    parse_header_type
      (Printf.sprintf
         "{y:%s|y.ipv4.valid => (y.ether.valid && y.ether.etherType==0x0800)}"
         hty_prog)
  in
  Logs.debug (fun m ->
      m "Inv: %a" (Pretty.pp_header_type []) hty_inv);
  Test.not_equiv hty_inv Nothing [] header_table

(* let test_dependency_not_violated2 () = let hty_prog = "\\sigma
   x:ether.{y:ipv4|x.ether.etherType==0x0800}" in let hty_inv =
   parse_header_type (Printf.sprintf "{y:%s|y.ipv4.valid => (y.ether.valid &&
   y.ether.etherType==0x0800)}" hty_prog) in Logs.debug (fun m -> m "Inv: %a"
   (Pretty.ContextPrinter.pp_header_type []) hty_inv); Test.not_equiv hty_inv
   Nothing [] header_table *)

let test_set =
  [ test_case "Dependency is violated" `Quick test_dependency_violated;
    test_case "Dependency is not violated" `Quick test_dependency_not_violated
    (* test_case "Dependency is not violated" `Quick
       test_dependency_not_violated2 *)
  ]
