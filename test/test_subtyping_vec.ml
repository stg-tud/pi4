open Alcotest
open Pi4
open Syntax
open Formula
open HeapType

module TestConfig = struct
  let verbose = true

  let maxlen = 32
end

module Test = Test_utils.TestRunner (TestConfig)


(*DIFFERENT HEADER TABLE*)
(*
let ahd_inst =
  Test_utils.mk_inst "aheader" [ ("field", 5) ]

let header_table = HeaderTable.populate [ ahd_inst ]
*)



let eth_inst =
  Test_utils.mk_inst "eth" [ ("smac", 48) (* "dmac", 48; "type", 16*) ]


let ipv4_inst = Test_utils.mk_inst "ipv4" [ ("src", 32); ("dst", 32) ]

let ipv6_inst = Test_utils.mk_inst "ipv6" [ ("version", 4); ("class", 8) ]

let tcp_inst = Test_utils.mk_inst "tcp" [ ("sport", 16); ("dport", 16) ]

let h_inst = Test_utils.mk_inst "h" [ ("f", 8); ("g", 16) ]

let header_table = HeaderTable.populate [ eth_inst; ipv4_inst; h_inst ]


let hty_empty = HeapType.empty header_table "x"

let hty_inst inst = HeapType.instance inst header_table "x"

let pred_pkt_out_empty binder =
  Eq (ArithExpr (Length (binder, PktOut)), ArithExpr (Num 0))

let pred_pkt_in_empty binder =
  Eq (ArithExpr (Length (binder, PktIn)), ArithExpr (Num 0))

let pred_pkt_in_out_empty binder =
  And (pred_pkt_in_empty binder, pred_pkt_out_empty binder)


let test_slice0 () =
  let s = Refinement ("x", hty_empty,        
    (Eq (BvExpr (Packet (0, PktOut)), BvExpr ( Slice ( bv_s "00001010" , 4, 8) )    ))
  
    ) in
  let t =
    Refinement
      ( "x",
        hty_empty,
        Eq (BvExpr (Slice ( Packet (0, PktOut) , 0,4)) , BvExpr (bv_s "1010") ))
  in
  Test.is_subtype s t [] header_table   
  
  
let test_slice1 () =
  let s = Refinement ("x", hty_empty,        
    (Eq (BvExpr (Packet (0, PktOut)), 
    BvExpr (  Slice ( Concat (bv_s "001" ,bv_s "1101" ), 2, 6)      ) 
                
        )
    )

    ) in
  let t =
    Refinement
      ( "x",
        hty_empty,
        Eq (BvExpr (Slice (Packet (0, PktOut), 0, 4)), BvExpr (bv_s "1110")) )
  in
  Test.is_subtype s t [] header_table

let test_slice2 () =
  let s = Refinement ("x", hty_empty,        
    (Eq (BvExpr (Packet (0, PktOut)), 
    BvExpr (  Slice ( Concat ( bv_s "001", Concat ( bv_s "1101", bv_s "0001")) , 2, 9)      ) 
                
        )
    )

    ) in
  let t =
    Refinement
      ( "x",
        hty_empty,
        Eq (BvExpr (Slice (Packet (0, PktOut), 0, 7)), BvExpr (bv_s "1110100")) )
  in
  Test.is_subtype s t [] header_table

  let test_slice3 () =
  let s = Refinement ("x", hty_empty,        
    (Eq (BvExpr (Packet (0, PktOut)), 
    BvExpr (Concat ( Slice ( Concat (bv_s "1110" ,bv_s "0010" ), 2, 6), Packet (0, PktIn) )      ) 
                
        )
    )
    ) in
  let t =
    Refinement
      ( "x",
        hty_empty,
        Eq (BvExpr (Packet (0, PktOut)) ,
        BvExpr (Concat (  bv_s "1000" , Packet (0, PktIn))) ))
  in
  Test.is_subtype s t [] header_table


let test_slice_parsed4 () =
  let hty_s =
    Parsing.parse_heap_type header_table []
      "{x:ε|x.pkt_out==(0b001@(0b1101@0b0011))[2:9]}"
  in
  let hty_t =
    Parsing.parse_heap_type header_table []
      "{x:ε|x.pkt_out[0:7]==0b1110100}"
  in
    Test.is_subtype hty_s hty_t [] header_table


let test_slice_packet_length5 () =
  let hty_s =
    Parsing.parse_heap_type header_table []
      "{x:ε|x.pkt_out==(x.pkt_in@0b101)[2:6] && x.pkt_out.length==4 && x.pkt_in.length==4 }"
  in
  let hty_t =
    Parsing.parse_heap_type header_table []
      "{x:ε|x.pkt_out==(x.pkt_in)[2:4]@0b10}"
  in
    Test.is_subtype hty_s hty_t [] header_table   

let test_slice_parsed6 () =
  let hty_s =
    Parsing.parse_heap_type header_table []
      "{x:ε|x.pkt_out==(0b1@x.pkt_in)[0:5]}"
  in
  let hty_t =
    Parsing.parse_heap_type header_table []
      "{x:ε|(x.pkt_out)[0:5]==0b1@x.pkt_in[0:4]}"
  in
    Test.is_subtype hty_s hty_t [] header_table    

 let test_slice_parsed7 () =
  let hty_s =
    Parsing.parse_heap_type header_table []
      "{x:ε|x.pkt_out==(x.pkt_in)[0:15]@0b11110 && x.pkt_out.length==20 && x.pkt_in.length==15 }"
  in
  let hty_t =
    Parsing.parse_heap_type header_table []
      "{x:ε|x.pkt_out==(x.pkt_in@ 0b11110)[0:20]}"
  in
    Test.is_subtype hty_s hty_t [] header_table  
 
    (* 11110001010100100101010011110001010100100101010000 50 bits*)
    (*  0111100010101001001010100 25bits *)
    let test_slice_packet8 () =
      let s = Refinement ("x", hty_empty,        
        (Eq (BvExpr (Packet (0, PktOut)), 
        BvExpr ( Slice ( (Concat ( bv_s "1" , Concat ( Packet (0, PktIn) ,Packet (0, PktOut) )) , 2, 4) ) )
    
          )
        )
        ) in
      let t =
        Refinement
          ( "x",
            hty_empty,
            Eq (BvExpr (Packet (0, PktOut)) ,
            BvExpr ( Slice ( Concat (Packet (0, PktIn) , Packet (0, PktOut) ), 1, 3) )))
      in
      let hty_s =
        Parsing.parse_heap_type header_table [] "{x:ε | x.pkt_out==(x.pkt_in@x.pkt_out)[1:3]}"
      in
      Fmt.pr "%a\n" (Pretty.pp_header_type[]) hty_s;
      Fmt.pr "%s\n" (Sexplib.Sexp.to_string_hum(Syntax.HeapType.sexp_of_t hty_s));
      Test.is_subtype s t [] header_table
    
    let test_slice_parsed9 () =
      let hty_s =
        Parsing.parse_heap_type header_table []
          "{x:eth|x.pkt_out==(x.pkt_in@x.pkt_out)[10:30]}"
      in
      let hty_t =
        Parsing.parse_heap_type header_table []
          "{x:eth|x.pkt_out[0:20]==(x.pkt_in)[10:20]@(x.pkt_out)[0:10]}"
      in
        Test.not_subtype hty_s hty_t [] header_table  
    
    let test_slice_parsed10 () =
      let hty_s =
        Parsing.parse_heap_type header_table []
          "{x:eth|x.pkt_out==(x.pkt_in@x.pkt_out)[10:30] && x.pkt_in.length==20}"
      in
      let hty_t =
        Parsing.parse_heap_type header_table []
          "{x:eth|x.pkt_out[0:20]==(x.pkt_in)[10:20]@(x.pkt_out)[0:10]}"
      in
        Test.is_subtype hty_s hty_t [] header_table
    
    
    let test_slice_parsed11 () =
      let hty_s =
        Parsing.parse_heap_type header_table []
          "{x:ε|x.pkt_out==(x.pkt_in@x.pkt_out)[5:15]}"
      in
      let hty_t =
        Parsing.parse_heap_type header_table []
          "{x:ε|x.pkt_out[0:10]==(x.pkt_in@x.pkt_out)[5:15]}"
      in
        Test.is_subtype hty_s hty_t [] header_table      
    
    let test_slice_parsed12 () =
      let hty_s =
        Parsing.parse_heap_type header_table []
          "{x:ε|x.pkt_out==(x.pkt_in@(0b01@x.pkt_out))[5:15]}"
      in
      let hty_t =
        Parsing.parse_heap_type header_table []
          "{x:ε|x.pkt_out[0:10]==(x.pkt_in@(0b01@x.pkt_out))[5:15]}"
      in
        Test.is_subtype hty_s hty_t [] header_table  
        
        
let test_set =
  [ 
    test_case "{x:ε| x.pkt_out=00001010[4:8]} <: {x:ε | x.pkt_out[0:4]=0101}" `Quick 
    test_slice0;
    test_case "{x:ε| x.pkt_out=(001@1101)[2:6]} <: {x:ε | x.pkt_out[0:4]=1110}" `Quick
    test_slice1;
    test_case "{x:ε| x.pkt_out=(001@1101@0001)[2:9]} <:˝{x:ε | x.pkt_out[0:7]=1110100}" `Quick
    test_slice2;
    test_case "{x:ε| x.pkt_out=(1110@0010)[2:6]@x.pkt_in} <: {x:ε|x.pkt_out=1000@x.pkt_in}" `Quick
    test_slice3;
    test_case "{x:ε|x.pkt_out=(001@(1101@0011))[2:9]}<:{x:ε|x.pkt_out[0:7]=1110100}" `Quick 
    test_slice_parsed4;
    test_case "{x:ε|x.pkt_out=(x.pkt_in@101)[2:6] &&|x.pkt_in|=4 &&|x.pkt_out|=4} <: {x:ε | x.pkt_out=x.pkt_in[2:4]@10}" `Quick 
    test_slice_packet_length5;
    test_case "{x:ε|x.pkt_out=(1@x.pkt_in)[0:5]}<:{x:ε|x.pkt_out[0:5]==1@x.pkt_in[0:4]}" `Quick 
    test_slice_parsed6;
    
    test_case "{x:ε|x.pkt_out=(x.pkt_in)[0:4]@1&&|x.pkt_in|=4&&|x.pkt_out|=5}<:{x:ε|x.pkt_out==(x.pkt_in@1)[0:5]}" `Quick 
    test_slice_parsed7;
    test_case "{x:ε| x.pkt_out=1@(x.pkt_in@x.pkt_out)[2:4]} <: {x:ε|x.pkt_out=x.pkt_in@x.pkt_out[1:3]}" `Quick
    test_slice_packet8;
    
    test_case "not({x:eth|x.pkt_out=(x.pkt_in@x.pkt_out)[10:30]}<:{x:eth|x.pkt_out[0:20]=(x.pkt_in)[10:20]@(x.pkt_out)[0:10]})" `Quick 
    test_slice_parsed9;
    test_case "{x:eth|x.pkt_out=(x.pkt_in@x.pkt_out)[10:30]&&|x.pkt_in|=20}<:{x:eth|x.pkt_out[0:20]=(x.pkt_in)[10:20]@(x.pkt_out)[0:10]}" `Quick 
    test_slice_parsed10;
    test_case "{x:ε|x.pkt_out=(x.pkt_in@x.pkt_out)[5:15]} <: {x:ε|x.pkt_out[0:10]=(x.pkt_in@x.pkt_out)[5:15]}" `Quick 
    test_slice_parsed11;
    test_case "{x:ε|x.pkt_out=(x.pkt_in@(0b01@x.pkt_out))[5:15]}<:{x:ε|x.pkt_out[0:10]=(x.pkt_in@(0b01@x.pkt_out))[5:15]}" `Quick 
    test_slice_parsed12;
  ]
