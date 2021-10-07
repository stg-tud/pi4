open Alcotest
open Pi4
open Syntax

module TestConfig = struct
  let verbose = true

  let maxlen = 1500
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

let stdmeta_inst = Test_utils.mk_inst "ipv4opt" [ ("value", 320) ]

let header_table = HeaderTable.populate [ eth_inst; ipv4_inst; stdmeta_inst ]

let parse_header_type hty_str =
  Parsing.header_type_of_string hty_str header_table []

let test_ihl_violated () =
  let hty_prog =
    "\\sigma x:ether.{y:ipv4|x.ether.etherType==0x0800 && y.ipv4.ihl==0b0110}"
  in
  let hty_inv =
    parse_header_type
      (Printf.sprintf
         "{z:%s|z.ipv4.valid => ((z.ipv4.ihl==0b1010 && !z.ipv4opt.valid) || (z.ipv4.ihl>0b1010 && z.ipv4opt.valid))}"
         hty_prog)
  in
  Test.is_equiv hty_inv Nothing [] header_table

let test_ihl_lt_five () =
  let hty_prog =
    "\\sigma x:ether.{y:ipv4|x.ether.etherType==0x0800 && y.ipv4.ihl==0b1100}"
  in
  let hty_inv =
    parse_header_type
      (Printf.sprintf
         "{z:%s|z.ipv4.valid => ((z.ipv4.ihl==0b1010 && !z.ipv4opt.valid) || (z.ipv4.ihl>0b1010 && z.ipv4opt.valid))}"
         hty_prog)
  in
  Test.is_equiv hty_inv Nothing [] header_table

let test_ihl_not_violated () =
  let hty_prog =
    "\\sigma x:ether.{y:ipv4|x.ether.etherType==0x0800 && y.ipv4.ihl==0b1010}"
  in
  let hty_inv =
    parse_header_type
      (Printf.sprintf
         "{z:%s|z.ipv4.valid => ((z.ipv4.ihl==0b1010 && !z.ipv4opt.valid) || (z.ipv4.ihl>0b1010 && z.ipv4opt.valid))}"
         hty_prog)
  in
  Test.not_equiv hty_inv Nothing [] header_table

let test_ihl_not_violated2 () =
  let hty_prog =
    {|
      Σv:(Σx:ether.{y:ipv4|x.ether.etherType==0x0800 && y.ipv4.ihl==0b0110}).ipv4opt
    |}
  in
  let hty_inv =
    parse_header_type
      (Printf.sprintf
         "{z:%s|z.ipv4.valid => ((z.ipv4.ihl==0b1010 && !z.ipv4opt.valid) || (z.ipv4.ihl>0b1010 && z.ipv4opt.valid))}"
         hty_prog)
  in
  Test.is_equiv hty_inv Nothing [] header_table

let test_set =
  [ test_case "IHL > 5, but ipv4opt not valid" `Quick test_ihl_violated;
    test_case "IHL < 5" `Quick test_ihl_lt_five;
    test_case "IHL = 5" `Quick test_ihl_not_violated;
    test_case "IHl > 5 ∧ ipv4opt.valid" `Quick test_ihl_not_violated2
  ]
