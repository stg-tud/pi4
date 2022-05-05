open Alcotest
open Pi4
open Syntax

module TestConfig = struct
  let verbose = true

  let maxlen = ref(320)
end

module Test = Test_utils.TestRunner (TestConfig)

let inst_eth =
  Test_utils.mk_inst "ethernet"
    [ ("dstAddr", 48); ("srcAddr", 48); ("etherType", 16) ]

let inst_ipv4 =
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

let inst_vlan =
  Test_utils.mk_inst "vlan"
    [ ("prio", 3); ("id", 1); ("vlan", 12); ("etherType", 16) ]

let header_table = HeaderTable.populate [ inst_eth; inst_ipv4; inst_vlan ]

let test_parser () =
  let cmd =
    {|
      (extract(ethernet);
      if(ethernet[96:112] == 0x8100) {
        (extract(vlan);
        if(vlan[16:32] == 0x0800) {
          extract(ipv4)
        } else {
          skip
        })
      } else {
        if(ethernet[96:112] == 0x0800) {
          extract(ipv4)
        } else {
          skip
        }
      })
  |}
  in
  let prog = Parsing.parse_command cmd header_table in
  let ty =
    Parsing.parse_type
      "(x:{y:ε|y.pkt_in.length==320}) -> ({y:⊤|y.ethernet.valid ∧ ¬y.ipv4.valid ∧ ¬y.vlan.valid} + 
                                          {y:⊤|y.ethernet.valid ∧ y.ipv4.valid ∧ ¬y.vlan.valid} + 
                                          {y:⊤|y.ethernet.valid ∧ ¬y.ipv4.valid ∧ y.vlan.valid} +
                                          {y:⊤|y.ethernet.valid ∧ y.ipv4.valid ∧ y.vlan.valid})"
      header_table
  in
  Test.typecheck header_table prog ty

let test_parser_sigma () =
  let cmd =
    {|
        (extract(ethernet);
        if(ethernet[96:112] == 0x8100) {
          (extract(vlan);
          if(vlan[16:32] == 0x0800) {
            extract(ipv4)
          } else {
            skip
          })
        } else {
          if(ethernet[96:112] == 0x0800) {
            extract(ipv4)
          } else {
            skip
          }
        })
    |}
  in
  let prog = Parsing.parse_command cmd header_table in
  let ty =
    Parsing.parse_type
      "(x:{y:ε|y.pkt_in.length==320}) -> (ethernet + Σy:ethernet.ipv4 +
         Σy:ethernet.vlan + Σy:ethernet.(Σz:vlan.ipv4))"
      header_table
  in
  Test.typecheck header_table prog ty

let test_simple_parser_ascribed () =
  let ht = HeaderTable.populate [ inst_eth; inst_ipv4 ] in
  let cmd =
    {|
    extract(ethernet) as (x:{y:ε|y.pkt_in.length==272}) → {y: ethernet|y.pkt_in.length==160};
    (if(ethernet[96:112] == 0x0800) {
      extract(ipv4)
    } else {
      skip
    } as (x:{y:⊤|y.ethernet.valid ∧ ¬y.ipv4.valid ∧ y.pkt_in.length==160}) → 
    ({y:⊤|y.ethernet.valid ∧ y.ipv4.valid} + {y:⊤|y.ethernet.valid ∧ ¬y.ipv4.valid}))
  |}
  in
  let header_table = ht in
  let prog = Parsing.parse_command cmd header_table in
  Logs.app (fun m -> m "%a" Pretty.pp_command prog);
  let ty =
    Parsing.parse_type
      "(x:{y:ε|y.pkt_in.length==272}) -> (ethernet + {y:⊤|y.ethernet.valid ∧
         y.ipv4.valid})"
      header_table
  in
  Test.typecheck header_table prog ty

let test_simple_parser_ascribed_sigma () =
  let ht = HeaderTable.populate [ inst_eth; inst_ipv4 ] in
  let cmd =
    {|
      extract(ethernet) as (x:{y:ε|y.pkt_in.length==272}) → {y: ethernet|y.pkt_in.length==160};
      (if(ethernet[96:112] == 0x0800) {
        extract(ipv4)
      } else {
        skip
      } as (x:{y:⊤|y.ethernet.valid ∧ ¬y.ipv4.valid ∧ y.pkt_in.length==160}) → 
      ({y:⊤|y.ethernet.valid ∧ y.ipv4.valid} + {y:⊤|y.ethernet.valid ∧ ¬y.ipv4.valid}))
    |}
  in
  let header_table = ht in
  let prog = Parsing.parse_command cmd header_table in
  Logs.app (fun m -> m "%a" Pretty.pp_command prog);
  let ty =
    Parsing.parse_type
      "(x:{y:ε|y.pkt_in.length==272}) -> (ethernet + Σy:ethernet.ipv4)"
      header_table
  in
  Test.typecheck header_table prog ty

let test_ascribe_simple () =
  let ht = HeaderTable.populate [ inst_eth; inst_ipv4 ] in
  let prog =
    Parsing.parse_command
      {|
        extract(ethernet) as (x:{y:ε|y.pkt_in.length==272}) → {y: ethernet|y.pkt_in.length==160};
        (if(ethernet[96:112] == 0x0800) {
          extract(ipv4)
        } else {
          skip
        } as (x:{y:⊤|y.ethernet.valid ∧ ¬y.ipv4.valid ∧ y.pkt_in.length==160}) → 
        ({y:⊤|y.ethernet.valid ∧ y.ipv4.valid} + {y:⊤|y.ethernet.valid ∧ ¬y.ipv4.valid}))
      |}
      ht
  in
  let ty =
    Parsing.parse_type
      "(x:{y:ε|y.pkt_in.length==272}) -> (ethernet + Σy:ethernet.ipv4)" ht
  in
  Test.typecheck ht prog ty

let test_ingress () =
  let prog =
    Parsing.parse_command
      {|
    if(!vlan.valid) {
      add(vlan);
      if(ipv4.valid) {
        vlan.etherType := 0x0800
      } else {
        vlan.etherType := 0x8100
      }
    }
  |}
      header_table
  in
  let ty =
    Parsing.parse_type
      {|
        (x: ({y:⊤|y.ethernet.valid ∧ ¬y.ipv4.valid ∧ ¬y.vlan.valid} + 
            {y:⊤|y.ethernet.valid ∧ y.ipv4.valid ∧ ¬y.vlan.valid} + 
            {y:⊤|y.ethernet.valid ∧ ¬y.ipv4.valid ∧ y.vlan.valid} +
            {y:⊤|y.ethernet.valid ∧ y.ipv4.valid ∧ y.vlan.valid})) ->
            ({y:⊤|y.ethernet.valid ∧ y.vlan.valid ∧ ¬y.ipv4.valid} + 
            {y:⊤|y.ethernet.valid ∧ y.vlan.valid ∧ y.ipv4.valid}) 
      |}
      header_table
  in
  Test.typecheck header_table prog ty

let test_ingress_sigma_input () =
  let prog =
    Parsing.parse_command
      {|
    if(!vlan.valid) {
      add(vlan);
      if(ipv4.valid) {
        vlan.etherType := 0x0800
      } else {
        vlan.etherType := 0x8100
      }
    }
  |}
      header_table
  in
  let ty =
    Parsing.parse_type
      {|
        (x: (ethernet + Σy:ethernet.ipv4 + Σy:ethernet.vlan + Σy:ethernet.(Σz:vlan.ipv4))) ->
            ({y:⊤|y.ethernet.valid ∧ y.vlan.valid ∧ ¬y.ipv4.valid} + 
            {y:⊤|y.ethernet.valid ∧ y.vlan.valid ∧ y.ipv4.valid}) 
      |}
      header_table
  in
  Test.typecheck header_table prog ty

let test_ingress_sigma_output () =
  let prog =
    Parsing.parse_command
      {|
    if(!vlan.valid) {
      add(vlan);
      if(ipv4.valid) {
        vlan.etherType := 0x0800
      } else {
        vlan.etherType := 0x8100
      }
    }
  |}
      header_table
  in
  let ty =
    Parsing.parse_type
      {|
        (x: ({y:⊤|y.ethernet.valid ∧ ¬y.ipv4.valid ∧ ¬y.vlan.valid} + 
            {y:⊤|y.ethernet.valid ∧ y.ipv4.valid ∧ ¬y.vlan.valid} + 
            {y:⊤|y.ethernet.valid ∧ ¬y.ipv4.valid ∧ y.vlan.valid} +
            {y:⊤|y.ethernet.valid ∧ y.ipv4.valid ∧ y.vlan.valid})) ->
            (Σy:ethernet.(Σz:ipv4.vlan) + Σy:ethernet.vlan)
      |}
      header_table
  in
  Test.typecheck header_table prog ty

let test_ingress_sigma () =
  let prog =
    Parsing.parse_command
      {|
      if(!vlan.valid) {
        add(vlan);
        if(ipv4.valid) {
          vlan.etherType := 0x0800
        } else {
          vlan.etherType := 0x8100
        }
      }
    |}
      header_table
  in
  let ty =
    Parsing.parse_type
      {|
          (x: (ethernet + Σy:ethernet.ipv4 + Σy:ethernet.vlan + Σy:ethernet.(Σz:vlan.ipv4))) ->
            (Σy:ethernet.(Σz:ipv4.vlan) + Σy:ethernet.vlan)
        |}
      header_table
  in
  Test.typecheck header_table prog ty

let test_ingress_ipv4_ethertype () =
  let prog =
    Parsing.parse_command
      {|
        if(!vlan.valid) {
          add(vlan);
          if(ipv4.valid) {
            vlan.etherType := 0x0800
          } else {
            vlan.etherType := 0x8100
          }
        }
      |}
      header_table
  in
  let ty =
    Parsing.parse_type
      {|
        (x: ({y:⊤|y.ethernet.valid ∧ ¬y.ipv4.valid ∧ ¬y.vlan.valid} + 
            {y:⊤|y.ethernet.valid ∧ y.ipv4.valid ∧ ¬y.vlan.valid} + 
            {y:⊤|y.ethernet.valid ∧ ¬y.ipv4.valid ∧ y.vlan.valid} +
            {y:⊤|y.ethernet.valid ∧ y.ipv4.valid ∧ y.vlan.valid ∧ y.vlan.etherType == 0x0800})) ->
            {y:⊤|y.ipv4.valid => y.vlan.etherType == 0x0800}
          |}
      header_table
  in
  Test.typecheck header_table prog ty

let test_ingress_bug () =
  let prog =
    Parsing.parse_command
      {|
        if(!vlan.valid) {
          add(vlan);
          if(ipv4.valid) {
            vlan.etherType := 0x0800
          };
          vlan.etherType := 0x8100
      }
    |}
      header_table
  in
  let ty =
    Parsing.parse_type
      {|
        (x: ({y:⊤|y.ethernet.valid ∧ ¬y.ipv4.valid ∧ ¬y.vlan.valid} + 
            {y:⊤|y.ethernet.valid ∧ y.ipv4.valid ∧ ¬y.vlan.valid} + 
            {y:⊤|y.ethernet.valid ∧ ¬y.ipv4.valid ∧ y.vlan.valid} +
            {y:⊤|y.ethernet.valid ∧ y.ipv4.valid ∧ y.vlan.valid ∧ y.vlan.etherType == 0x0800})) ->
        {y:⊤|y.ipv4.valid => y.vlan.etherType == 0x0800}
      |}
      header_table
  in
  Test.not_typecheck header_table prog ty

let test_complete () =
  let cmd =
    {|
      (extract(ethernet);
      if(ethernet[96:112] == 0x8100) {
        (extract(vlan);
        if(vlan[16:32] == 0x0800) {
          extract(ipv4)
        })
      } else {
        if(ethernet[96:112] == 0x0800) {
          extract(ipv4)
        }
      });
      if(!vlan.valid) {
        add(vlan);
        if(ipv4.valid) {
          vlan.etherType := 0x0800
        } else {
          vlan.etherType := 0x8100
        }
      }
  |}
  in
  let prog = Parsing.parse_command cmd header_table in
  let ty =
    Parsing.parse_type
      {|
        (x:{y:ε|y.pkt_in.length==320}) -> 
        ({y:⊤|y.ethernet.valid ∧ y.vlan.valid ∧ ¬y.ipv4.valid} + 
        {y:⊤|y.ethernet.valid ∧ y.vlan.valid ∧ y.ipv4.valid})
      |}
      header_table
  in
  Test.typecheck header_table prog ty

let test_complete_ascribe_parser () =
  let cmd =
    {|
        ((extract(ethernet);
        if(ethernet.etherType == 0x8100) {
          (extract(vlan);
          if(vlan.etherType == 0x0800) {
            extract(ipv4)
          })
        } else {
          if(ethernet.etherType == 0x0800) {
            extract(ipv4)
          }
        }) as (x:{y:ε|y.pkt_in.length==320}) -> ({y:⊤|y.ethernet.valid ∧ ¬y.ipv4.valid ∧ ¬y.vlan.valid} + 
                                                {y:⊤|y.ethernet.valid ∧ y.ipv4.valid ∧ ¬y.vlan.valid} + 
                                                {y:⊤|y.ethernet.valid ∧ ¬y.ipv4.valid ∧ y.vlan.valid} +
                                                {y:⊤|y.ethernet.valid ∧ y.ipv4.valid ∧ y.vlan.valid}));
        if(!vlan.valid) {
          add(vlan);
          if(ipv4.valid) {
            vlan.etherType := 0x0800
          } else {
            vlan.etherType := 0x8100
          }
        }
    |}
  in
  let prog = Parsing.parse_command cmd header_table in
  let ty =
    Parsing.parse_type
      {|
          (x:{y:ε|y.pkt_in.length==320}) -> 
          ({y:⊤|y.ethernet.valid ∧ y.vlan.valid ∧ ¬y.ipv4.valid} + 
          {y:⊤|y.ethernet.valid ∧ y.vlan.valid ∧ y.ipv4.valid})
        |}
      header_table
  in
  Test.typecheck header_table prog ty

let test_complete_ascribed () =
  let cmd =
    {|
        ((extract(ethernet);
        if(ethernet.etherType == 0x8100) {
          (extract(vlan);
          if(vlan.etherType == 0x0800) {
            extract(ipv4)
          })
        } else {
          if(ethernet.etherType == 0x0800) {
            extract(ipv4)
          }
        }) as (x:{y:ε|y.pkt_in.length==320}) -> ({y:⊤|y.ethernet.valid ∧ ¬y.ipv4.valid ∧ ¬y.vlan.valid} + 
                                                {y:⊤|y.ethernet.valid ∧ y.ipv4.valid ∧ ¬y.vlan.valid} + 
                                                {y:⊤|y.ethernet.valid ∧ ¬y.ipv4.valid ∧ y.vlan.valid} +
                                                {y:⊤|y.ethernet.valid ∧ y.ipv4.valid ∧ y.vlan.valid}));
        ((if(!vlan.valid) {
          add(vlan);
          if(ipv4.valid) {
            vlan.etherType := 0x0800
          } else {
            vlan.etherType := 0x8100
          }
        }) as (x: ({y:⊤|y.ethernet.valid ∧ ¬y.ipv4.valid ∧ ¬y.vlan.valid} + 
        {y:⊤|y.ethernet.valid ∧ y.ipv4.valid ∧ ¬y.vlan.valid} + 
        {y:⊤|y.ethernet.valid ∧ ¬y.ipv4.valid ∧ y.vlan.valid} +
        {y:⊤|y.ethernet.valid ∧ y.ipv4.valid ∧ y.vlan.valid})) → ({y:⊤|y.ethernet.valid ∧ y.vlan.valid ∧ ¬y.ipv4.valid} + 
        {y:⊤|y.ethernet.valid ∧ y.vlan.valid ∧ y.ipv4.valid}))
    |}
  in
  let prog = Parsing.parse_command cmd header_table in
  let ty =
    Parsing.parse_type
      {|
          (x:{y:ε|y.pkt_in.length==320}) -> 
          ({y:⊤|y.ethernet.valid ∧ y.vlan.valid ∧ ¬y.ipv4.valid} + 
          {y:⊤|y.ethernet.valid ∧ y.vlan.valid ∧ y.ipv4.valid})
        |}
      header_table
  in
  Test.typecheck header_table prog ty

let test_set =
  [ test_case "parser typechecks" `Quick test_parser;
    test_case "parser typechecks with Σ-type" `Slow test_parser_sigma;
    test_case "simple parser typechecks with ascribed type" `Quick
      test_simple_parser_ascribed;
    test_case "simple parser typechecks with ascribed Σ-type" `Slow
      test_simple_parser_ascribed_sigma;
    test_case "simple parser typechecks with ascribed type" `Quick
      test_ascribe_simple;
    test_case "ingress typechecks" `Quick test_ingress;
    test_case "ingress typechecks with Σ-type as input type" `Quick
      test_ingress_sigma_input;
    test_case "ingress typechecks with Σ-type as output type" `Slow
      test_ingress_sigma_output;
    test_case "ingress typechecks with Σ-type" `Quick test_ingress_sigma;
    test_case "ingress sets correct etherType if IPv4 is valid" `Quick
      test_ingress_ipv4_ethertype;
    test_case "wrong etherType is detected" `Quick test_ingress_bug;
    test_case "parser + ingress typechecks" `Quick test_complete;
    test_case "ascribed parser + ingress typechecks" `Quick test_complete_ascribe_parser;
    test_case "ascribed parser + ascribed ingress typechecks" `Quick test_complete_ascribed;
  ]
