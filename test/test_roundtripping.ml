open Alcotest
open Pi4
open Syntax

module TestConfig = struct
  let verbose = true

  let maxlen = 36
end

module Test = Test_utils.TestRunner (TestConfig)

let test_single_header_ingress () =
  let ingress =
    "header_type h_t {
      f: 1;
    }
    header h : h_t
    extract(h) as (x:{x:\\empty|x.pkt_in.length>0}) -> h"
  in
  let ingr = Parsing.parse_program ingress in
  let header_table = HeaderTable.of_decls ingr.declarations in
  let ty =
    Parsing.parse_type "(x: {x:\\empty|x.pkt_in.length>0}) -> h" header_table
  in
  Test.typecheck header_table ingr.command ty

let test_single_header_roundtrip_emit () =
  let prog_rt =
    Parsing.parse_program
      "header_type h_t {
        f: 1;
      }
      header h : h_t
      remit(h)"
  in
  let header_table = HeaderTable.of_decls prog_rt.declarations in
  let ty =
    Parsing.parse_type
      {|
        (x:{y:h|y.pkt_in.length==0 && y.pkt_out.length==0 ∧ y.h[0:1]==0b0}) -> 
        {y:h|y =i= x} 
      |}
      header_table
  in
  Test.typecheck header_table prog_rt.command ty

let test_single_header_roundtrip_reset0 () =
  let prog_rt =
    Parsing.parse_program
      "header_type h_t {
        f: 1;
      }
      header h : h_t
      remit(h);
      reset "
  in
  let header_table = HeaderTable.of_decls prog_rt.declarations in
  let ty =
    Parsing.parse_type
      {|
        (x:{y:h|y.pkt_in.length==0 && y.pkt_out.length==0 ∧ y.h[0:1]==0b0}) -> 
        {y:ε| y.pkt_in[0:1] == 0b0 ∧ y.pkt_in.length=1} 
      |}
      header_table
  in
  Test.typecheck header_table prog_rt.command ty

let test_single_header_roundtrip_reset1 () =
  let prog_rt =
    Parsing.parse_program
      "header_type h_t {
        f: 1;
      }
      header h : h_t
      remit(h);
      reset "
  in
  let header_table = HeaderTable.of_decls prog_rt.declarations in
  let ty =
    Parsing.parse_type
      {|
        (x:{y:h|y.pkt_in.length==0 && y.pkt_out.length==0 ∧ y.h[0:1]==0b1}) -> 
        {y:ε|y.pkt_in[0:1] == 0b1} 
      |}
      header_table
  in
  Test.typecheck header_table prog_rt.command ty

let test_single_header_roundtrip () =
  let prog_rt =
    Parsing.parse_program
      "header_type h_t {
        f: 1;
      }
      header h : h_t
      remit(h);
      reset;
      extract(h)"
  in
  let header_table = HeaderTable.of_decls prog_rt.declarations in
  let ty =
    Parsing.parse_type
      {|
        (x:{y:h|y.pkt_in.length==0 && y.pkt_out.length==0 ∧ y.h[0:1]==0b1}) -> 
        {y:h|y =i= x} 
      |}
      header_table
  in
  Test.typecheck header_table prog_rt.command ty

let test_single_header_roundtrip_violated () =
  let prog_rt =
    Parsing.parse_program
      "header_type h_t {
        f: 1;
      }
      header h : h_t
      remit(h);
      reset"
  in
  let header_table = HeaderTable.of_decls prog_rt.declarations in
  let ty =
    Parsing.parse_type
      "(x:{y:h|y.pkt_in.length==0 && y.pkt_out.length==0}) -> 
      {y:\\empty|y =i= x}"
      header_table
  in
  Test.not_typecheck header_table prog_rt.command ty

let test_parser () =
  let parser =
    Parsing.parse_program
      "header_type ether_t { 
        etherType: 16;
      }
      header_type ipv4_t { 
        version: 4; 
      }
      header_type vlan_t {
        etherType: 16;
      }
      header ether : ether_t
      header ipv4 : ipv4_t
      header vlan : vlan_t

      extract(ether);
      if(ether.etherType == 0x0800) {
        extract(ipv4)
      } else {
        if(ether.etherType == 0x8100) {
          extract(vlan);
          if(vlan.etherType == 0x0800) {
            extract(ipv4)
          }
        } 
      }"
  in
  let header_table = HeaderTable.of_decls parser.declarations in
  let ty =
    Parsing.parse_type
      "(x:{y:\\empty|y.pkt_in.length==304 && y.pkt_out.length==0}) -> 
      \\sigma y:ether.(ipv4 + vlan + \\sigma z:vlan.ipv4)"
      header_table
  in
  Test.typecheck header_table parser.command ty

let test_ingress () =
  let prog =
    Parsing.parse_program
      "header_type ether_t { 
        etherType: 16;
      }
      header_type ipv4_t { 
        version: 4; 
      }
      header_type vlan_t {
        etherType: 16;
      }
      header ether : ether_t
      header ipv4 : ipv4_t
      header vlan : vlan_t

      extract(ether);
      if(ether.etherType == 0x0800) {
        extract(ipv4)
      } else {
        if(ether.etherType == 0x8100) {
          extract(vlan);
          if(vlan.etherType == 0x0800) {
            extract(ipv4)
          }
        } 
      };
      if(!vlan.valid) {
        add(vlan);
        if(ipv4.valid) {
          vlan.etherType := 0x0800
        };
        ether.etherType := 0x8100
      }"
  in
  let header_table = HeaderTable.of_decls prog.declarations in
  let ty =
    Parsing.parse_type
      "(x:{y:\\empty|y.pkt_in.length==304 && y.pkt_out.length==0}) -> 
      \\sigma y:ether.(\\sigma z:vlan.(ipv4 + \\empty))"
      header_table
  in
  Test.typecheck header_table prog.command ty

let test_roundtrip () =
  let prog =
    Parsing.parse_program
      "header_type ether_t { 
        etherType: 16;
      }
      header_type ipv4_t { 
        version: 4; 
      }
      header_type vlan_t {
        etherType: 16;
      }
      header ether : ether_t
      header ipv4 : ipv4_t
      header vlan : vlan_t

      extract(ether);
      if(ether.etherType == 0x0800) {
        extract(ipv4)
      } else {
        if(ether.etherType == 0x8100) {
          extract(vlan);
          if(vlan.etherType == 0x0800) {
            extract(ipv4)
          }
        } 
      };
      if(!vlan.valid) {
        add(vlan);
        if(ipv4.valid) {
          vlan.etherType := 0x0800
        };
        ether.etherType := 0x8100
      };
      remit(ether);
      if(vlan.valid) {
        remit(vlan)
      };
      if(ipv4.valid) {
        remit(ipv4)
      };
      reset;
      extract(ether);
      if(ether.etherType == 0x0800) {
        extract(ipv4)
      } else {
        if(ether.etherType == 0x8100) {
          extract(vlan);
          if(vlan.etherType == 0x0800) {
            extract(ipv4)
          }
        } 
      }"
  in
  let header_table = HeaderTable.of_decls prog.declarations in
  let ty =
    Parsing.parse_type
      "(x:{y:\\empty|y.pkt_in.length==304 && y.pkt_out.length==0}) -> 
      {w: \\sigma y:ether.(\\sigma z:vlan.(ipv4 + \\empty))| w =i= x}"
      header_table
  in
  Test.typecheck header_table prog.command ty

let test_roundtrip_violated () =
  let prog =
    Parsing.parse_program
      "header_type ether_t { 
        etherType: 16;
      }
      header_type ipv4_t { 
        version: 4; 
      }
      header_type vlan_t {
        etherType: 16;
      }
      header ether : ether_t
      header ipv4 : ipv4_t
      header vlan : vlan_t

      extract(ether);
      if(ether.etherType == 0x0800) {
        extract(ipv4)
      } else {
        if(ether.etherType == 0x8100) {
          extract(vlan);
          if(vlan.etherType == 0x0800) {
            extract(ipv4)
          }
        } 
      };
      if(!vlan.valid) {
        add(vlan);
        if(ipv4.valid) {
          vlan.etherType := 0x0800
        }
      }"
  in
  let header_table = HeaderTable.of_decls prog.declarations in
  let ty =
    Parsing.parse_type
      "(x:{y:\\empty|y.pkt_in.length==304 && y.pkt_out.length==0}) -> 
      {w: \\sigma y:ether.(\\sigma z:vlan.(ipv4 + \\empty))| w =i= x}"
      header_table
  in
  Test.typecheck header_table prog.command ty

let test_set =
  [ test_case "Single header: Ingress typechecks" `Quick
      test_single_header_ingress;
    test_case "Single header roundtripping - emit" `Quick test_single_header_roundtrip_emit;
    test_case "Single header roundtripping - reset 0" `Quick test_single_header_roundtrip_reset0;
    test_case "Single header roundtripping - reset 1" `Quick test_single_header_roundtrip_reset1;
    test_case "Single header roundtripping" `Quick test_single_header_roundtrip;
    test_case "Single header roundtripping violated" `Quick
      test_single_header_roundtrip_violated;
    test_case "Roundtripping: Parser typechecks" `Quick test_parser;
    test_case "Roundtripping: Ingress typechecks" `Slow test_ingress;
    test_case "Roundtripping property holds" `Slow test_roundtrip
  ]
