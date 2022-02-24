open Alcotest
open Pi4
open Syntax

let eth_inst =
 Test_utils.mk_inst "ether" 
 [
  ("dmac", 48);
  ("smac", 48);
  ("etherType", 16) 
]

let header_table = HeaderTable.populate [ eth_inst ]

module TestConfig = struct
 let verbose = true
 let maxlen = 1500
end

module Test = Test_utils.TestRunner (TestConfig)

let test1 () =
 let input =
   Parsing.parse_heap_type header_table []
     {| 
       {y: ε|y.pkt_in.length > 272 ∧ y.pkt_out.length == 1500}
     |}
 in

 let hty =
   Parsing.parse_heap_type header_table
     [ ("x", Env.VarBind input) ]
     {| 
     ({y':
        ⊤
        | (((y'.pkt_in.length == y.pkt_in.length ∧
            y'.pkt_in == y.pkt_in) ∧
            (y'.pkt_out.length == y.pkt_out.length ∧
            y'.pkt_out == y.pkt_out)) ∧
          (true ∧
          ((¬(y'.ether.valid) ∧
            ¬(y.ether.valid)) ∨
          ((y'.ether.valid ∧
            y.ether.valid) ∧
          y'.ether[0:112] == y.ether[0:112]))))})[y ↦
                                                    {y:
                                                      ⊤
                                                      | (((((true ∧
                                                            y.ether.valid) ∧
                                                            y.ether[0:112]@y.pkt_in == x.pkt_in) ∧
                                                          (y.pkt_in.length + 112) == x.pkt_in.length) ∧
                                                          true) ∧
                                                        (y.pkt_out.length == x.pkt_out.length ∧
                                                        y.pkt_out == x.pkt_out))}]      
          |}
 in

 let hty_smpl =
   Parsing.parse_heap_type header_table
     [ ("x", Env.VarBind input) ]
     {|
     {y:
      ⊤
      | ((((y.pkt_in.length + 112) == x.pkt_in.length ∧
          x.pkt_in[0:112]@y.pkt_in == x.pkt_in) ∧
        (y.pkt_out.length == x.pkt_out.length ∧
        y.pkt_out == x.pkt_out)) ∧
        (y.ether.valid ∧
        ((y.ether[0:48] == x.pkt_in[0:48] ∧
        y.ether[48:96] == x.pkt_in[48:96]) ∧
        y.ether[96:112] == x.pkt_in[96:112])))}
     |}
 in
 Test.is_equiv hty_smpl hty [ ("x", Env.VarBind input) ] header_table

let test2 () =
  let input =
    Parsing.parse_heap_type header_table []
      {| 
        {y: ε|y.pkt_in.length > 272 ∧ y.pkt_out.length == 1500}
      |}
  in
  let hty =
    Parsing.parse_heap_type header_table
      [ ("x", Env.VarBind input) ]
      {| 
      {y:
      ⊤
      | y.ether[0:112]@y.pkt_in == x.pkt_in }
      |}
  in
  let hty_smpl =
    Parsing.parse_heap_type header_table
      [ ("x", Env.VarBind input) ]
      {| 
      {y:
      ⊤
      | y.ether[0:48]@y.ether[48:96]@y.ether[96:112]@y.pkt_in == x.pkt_in }
      |}
  in
  Test.is_equiv hty_smpl hty [ ("x", Env.VarBind input) ] header_table


let test_set = 
  [ test_case "Test 1" `Quick test1;
    test_case "Test 2" `Quick test2 ]