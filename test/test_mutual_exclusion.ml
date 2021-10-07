open Alcotest
open Pi4
open Syntax
open Parsing

module TestConfig = struct
  let verbose = true

  let maxlen = 48
end

module Test = Test_utils.TestRunner (TestConfig)
module T = Typechecker.Make (Typechecker.SimpleChecker)

let test_exclusion () =
  let prog =
    parse_program_from_file
      "./test/examples/mutual_exclusion/mutual_exclusion.pi4"
  in
  let header_table = HeaderTable.of_decls prog.declarations in
  let ty =
    Parsing.parse_type
      {|
        (y:{x:ε|x.pkt_in.length==48}) -> 
          {z:⊤|!(z.ipv4.valid && z.ipv6.valid)}
      |}
      header_table
  in
  Test.typecheck header_table prog.command ty

let test_exclusion_simple () =
  let prog =
    parse_program_from_file
      "./test/examples/mutual_exclusion/mutual_exclusion.pi4"
  in
  let header_table = HeaderTable.of_decls prog.declarations in
  let ty =
    Parsing.parse_type
      {|
        (y:ε) -> {z:⊤|!(z.ipv4.valid && z.ipv6.valid)} |}
      header_table
  in
  Alcotest.(check Testable.typechecker_result)
    (Fmt.str "%a" (Pretty.pp_type []) ty)
    Typechecker.TypecheckingResult.Success
    (T.check_type prog.command ty header_table)

let test_exclusion1 () =
  let prog =
    parse_program_from_file "./test/examples/mutual_exclusion/violation1.pi4"
  in
  let header_table = HeaderTable.of_decls prog.declarations in
  let ty =
    Parsing.parse_type
      {| 
        (y:{x:ε|x.pkt_in.length==48}) -> 
          {z:⊤|!(z.ipv4.valid ∧ z.ipv6.valid)} 
      |}
      header_table
  in
  Test.not_typecheck header_table prog.command ty

let test_exclusion1_simple () =
  let prog =
    parse_program_from_file
      "./test/examples/mutual_exclusion/violation1.pi4"
  in
  let header_table = HeaderTable.of_decls prog.declarations in
  let ty =
    Parsing.parse_type
      {|
        (y:ε) -> {z:⊤|!(z.ipv4.valid && z.ipv6.valid)} |}
      header_table
  in
  Alcotest.(check bool)
    (Fmt.str "%a" (Pretty.pp_type []) ty)
    true
    (Typechecker.TypecheckingResult.is_error (T.check_type prog.command ty header_table))

let test_exclusion2 () =
  let prog =
    parse_program_from_file "./test/examples/mutual_exclusion/violation2.pi4"
  in
  let header_table = HeaderTable.of_decls prog.declarations in
  let ty =
    Parsing.parse_type
      {|
        (y:{x:ε|x.pkt_in.length==48}) -> 
          {z:⊤|!(z.ipv4.valid ∧ z.ipv6.valid)}
      |}
      header_table
  in
  Test.not_typecheck header_table prog.command ty

let header_table =
  HeaderTable.populate
    [ Test_utils.mk_inst "eth" [ ("etherType", 16) ];
      Test_utils.mk_inst "ipv4" [ ("version", 4); ("ihl", 4) ];
      Test_utils.mk_inst "ipv6" [ ("version", 4); ("class", 8) ]
    ]

let test_subtype_exclusion () =
  let hty_s =
    Parsing.header_type_of_string
      "{x:
          \\sigma y:
                    {z:\\top|z.eth.valid && !z.ipv4.valid && !z.ipv6.valid}.
                    (\\sigma z:
                              {x:\\top|x.ipv4.valid && !x.eth.valid && !x.ipv6.valid}.
                              {x:\\top|x.ipv6.valid && !x.eth.valid && !x.ipv4.valid}) 
          | !(x.ipv4.valid && x.ipv6.valid)}"
      header_table []
  in
  Test.is_subtype hty_s Nothing [] header_table

let test_subtype_exclusion2 () =
  let hty_s =
    Parsing.parse_header_type "Σx:eth.(ipv4 + ipv6)" header_table []
  in
  let hty_t =
    Parsing.parse_header_type
      {|
        {z:⊤|!(z.ipv4.valid ∧ z.ipv6.valid)}
      |}
      header_table []
  in
  Test.is_subtype hty_s hty_t [] header_table

let test_subtype_exclusion3 () =
  let hty_s =
    Parsing.parse_header_type "Σx:eth.(Σy:ipv4.ipv6)" header_table []
  in
  let hty_t =
    Parsing.parse_header_type
      {|
        {z:Σx:eth.(Σy:ipv4.ipv6)|!(z.ipv4.valid ∧ z.ipv6.valid)}
      |}
      header_table []
  in
  Test.not_subtype hty_s hty_t [] header_table

let test_subtype_exclusion4 () =
  let hty_s =
    Parsing.parse_header_type "Σx:eth.(Σy:ipv4.ipv6)" header_table []
  in
  let hty_t =
    Parsing.parse_header_type
      {|
        {z:⊤|!(z.ipv4.valid ∧ z.ipv6.valid)}
      |}
      header_table []
  in
  Test.not_subtype hty_s hty_t [] header_table

let test_subtype_exclusion5 () =
  let hty_s = Parsing.parse_header_type "Σx:eth.ipv4" header_table [] in
  let hty_t =
    Parsing.parse_header_type
      {|
        {z:⊤|!( z.ipv4.valid)}
      |}
      header_table []
  in
  Test.not_subtype hty_s hty_t [] header_table

let test_subtype_exclusion6 () =
  let hty_s =
    Parsing.parse_header_type "{x:⊤|x.eth.valid ∧ x.ipv6.valid }"
      header_table []
  in
  let hty_t =
    Parsing.parse_header_type
      {|
          {z:⊤|!(z.ipv4.valid ∧ z.ipv6.valid)}
        |}
      header_table []
  in
  Test.not_subtype hty_s hty_t [] header_table

let header_table_ssa =
  HeaderTable.populate
    [ Test_utils.mk_inst "ether_0" [ ("etherType", 16) ];
      Test_utils.mk_inst "ether_1" [ ("etherType", 16) ];
      Test_utils.mk_inst "ipv4_0" [ ("version", 4); ("ihl", 4) ];
      Test_utils.mk_inst "ipv4_1" [ ("version", 4); ("ihl", 4) ];
      Test_utils.mk_inst "ipv6_0" [ ("version", 4); ("class", 8) ];
      Test_utils.mk_inst "ipv6_1" [ ("version", 4); ("class", 8) ]
    ]

let test_set =
  [ test_case "Mutual exclusion of IPv4/6 not violated" `Quick test_exclusion;
    test_case "Mutual exclusion of IPv4/6 not violated (simple)" `Quick
      test_exclusion_simple;
    test_case "Mutual exclusion of IPv4/6 violated" `Quick test_exclusion1;
    test_case "Mutual exclusion of IPv4/6 violated (simple)" `Quick test_exclusion1_simple;
    test_case "Mutual exclusion of IPv4/6 violated" `Quick test_exclusion2;
    test_case "Mutual exclusion subtype" `Quick test_subtype_exclusion;
    test_case "Mutual exclusion subtype 2" `Quick test_subtype_exclusion2;
    test_case "Mutual exclusion subtype 3" `Quick test_subtype_exclusion3;
    test_case "Mutual exclusion subtype 4" `Quick test_subtype_exclusion4;
    test_case "Mutual exclusion subtype 5" `Quick test_subtype_exclusion5;
    test_case "Mutual exclusion subtype 6" `Quick test_subtype_exclusion6
  ]
