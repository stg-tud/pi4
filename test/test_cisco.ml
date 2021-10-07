open Alcotest
open Pi4
open Syntax

module TestConfig = struct
  let verbose = true

  let maxlen = 360
end

module Test = Test_utils.TestRunner (TestConfig)

let parse_typecheck check prog_str typ_str =
  let prog = Parsing.parse_program prog_str in
  let header_table = HeaderTable.of_decls prog.declarations in
  let ty = Parsing.parse_type typ_str header_table in
  check header_table prog.command ty

let cisco_ingress () =
  parse_typecheck Test.typecheck
    {|
    header_type meta_t {
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
      egress_global_timestamp: 48;
      mcast_grp: 16;
      egress_rid: 16;
      checksum_error: 1;
      priority: 3;
    }
    header_type vlan_t {
      prio: 3;
      id: 1;
      vid: 12;
      etherType: 16;
    }
    header meta : meta_t
    header vlan : vlan_t
    extract(vlan)
  |}
    "(x : {y:meta | y.pkt_in.length == 32}) -> \\sigma z : meta . vlan"

let cisco_egress () =
  parse_typecheck Test.typecheck
    {|
    header_type meta_t {
       egress : 1;
    }
    header_type vlan_t {
      typ : 2;
    }
    header meta : meta_t
    header vlan : vlan_t
    remit(vlan)
  |}
    {|(x:{z:⊤|z.meta.valid ∧ z.vlan.valid}) -> {z:⊤|z.meta.valid ∧ z.vlan.valid}|}

let intype_composes () =
  let prog_str =
    {| header_type meta_t {
         egress : 1;
       }
       header_type vlan_t {
         vid : 2;
       }
       header meta : meta_t
       header vlan : vlan_t
       skip
    |}
  in
  let prog = Parsing.parse_program prog_str in
  let header_table = HeaderTable.of_decls prog.declarations in
  let sub =
    Parsing.header_type_of_string {|\sigma z : meta . vlan|} header_table []
  in
  let sup =
    Parsing.header_type_of_string {|\sigma z : meta . vlan|} header_table []
  in
  Test.is_subtype sub sup [] header_table

let outtype_composes () =
  let prog_str =
    {| header_type meta_t {
         egress: 1;
       }
       header_type vlan_t {
         vid : 2;
       }
       header meta : meta_t
       header vlan : vlan_t
       skip
    |}
  in
  let prog = Parsing.parse_program prog_str in
  let header_table = HeaderTable.of_decls prog.declarations in
  let tau =
    (* Parsing.header_type_of_string "\\sigma x : meta . vlan" header_table [] *)
    Parsing.header_type_of_string "{x:⊤|x.meta.valid ∧ x.vlan.valid}" header_table []
  in
  let ctx = [ ("x", Env.VarBind tau) ] in
  let sub =
    Parsing.header_type_of_string
      (* "{w : \\sigma z : meta . vlan | w.vlan.vid == x.vlan.vid}" header_table *)
      "{w:⊤| w.meta.valid ∧ w.vlan.valid ∧ w.vlan.vid == x.vlan.vid}" header_table
      ctx
  in
  let sup =
    (* Parsing.header_type_of_string {|\sigma z : meta . vlan|} header_table [] *)
    Parsing.header_type_of_string {| {z:⊤| z.meta.valid ∧ z.vlan.valid} |} header_table []
  in
  Test.is_subtype sub sup ctx header_table

let inner_ok_cust () =
  parse_typecheck Test.typecheck
    {|
    header_type meta_t {
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
      egress_global_timestamp: 48;
      mcast_grp: 16;
      egress_rid: 16;
      checksum_error: 1;
      priority: 3;
    }
    header_type vlan_t {
      prio: 3;
      id: 1;
      vid: 12;
      etherType: 16;
    }
    header meta : meta_t                                  
    header vlan : vlan_t
    skip|}
    "(x : {z:⊤|z.meta.valid ∧ z.vlan.valid}) -> {w : ⊤ | w.meta.valid ∧ w.vlan.valid ∧ w.vlan.vid == x.vlan.vid}"

let inner_bad_cust () =
  parse_typecheck Test.not_typecheck
    {|
     header_type meta_t {
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
      egress_global_timestamp: 48;
      mcast_grp: 16;
      egress_rid: 16;
      checksum_error: 1;
      priority: 3;
     }
     header_type vlan_t {
      prio: 3;
      id: 1;
      vid: 12;
      etherType: 16;
     }
     header meta : meta_t
     header vlan : vlan_t
     vlan.vid := 0b000000000000|}
    "(x : {z:⊤|z.meta.valid ∧ z.vlan.valid}) -> {w : \\sigma z : ?meta . ?vlan | w.vlan.vid == x.vlan.vid}"

let inner_ok_cust2 () =
  parse_typecheck Test.typecheck
    {|
    header_type meta_t {
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
      egress_global_timestamp: 48;
      mcast_grp: 16;
      egress_rid: 16;
      checksum_error: 1;
      priority: 3;
    }
    header_type vlan_t {
      prio: 3;
      id: 1;
      vid: 12;
      etherType: 16;
    }
    header meta : meta_t
    header vlan : vlan_t
    meta.egress_spec := 0b000000001|}
    {|(x : {z:⊤|z.meta.valid ∧ z.vlan.valid}) -> {w:⊤ | w.meta.valid ∧ w.vlan.valid ∧ x.vlan.vid == w.vlan.vid}|}

let inner_ok_cust_table () =
  parse_typecheck Test.typecheck
    {|
     header_type vlan_t {
       vid: 2;
     }
     header_type meta_t {
       egress: 1; 
     }
     header_type vlan_tbl_t {
       vid: 2;
       act: 1;     
     }
     header vlan : vlan_t
     header meta : meta_t
     header vlan_tbl : vlan_tbl_t
     add(vlan_tbl);                                  
     if (vlan.vid == vlan_tbl.vid) {
       if (vlan_tbl.act == 0b0) {
          meta.egress := 0b0
       } else {
          meta.egress := 0b1
       }
     } else {
         skip
     }|}
    (* {| (x : \sigma z : meta . vlan) -> {w : \sigma z : ?meta . ?vlan | x.vlan.vid == w.vlan.vid} |} *)
    {| (x : {x:⊤|x.meta.valid ∧ x.vlan.valid ∧ ¬x.vlan_tbl.valid}) -> {w : \top | w.meta.valid ∧ w.vlan.valid ∧ x.vlan.vid == w.vlan.vid} |}

let inner_bad_cust_table_path () =
  parse_typecheck Test.not_typecheck
    {|
    header_type vlan_t {
     vid: 2;
     }
     header_type meta_t {
       egress: 1; 
     }
     header_type vlan_tbl_t {
     vid: 2;
     act: 1;     
     }
     header vlan : vlan_t
     header meta : meta_t
     header vlan_tbl : vlan_tbl_t
     add(vlan_tbl);
     if (vlan.vid == vlan_tbl.vid) {
       if (vlan_tbl.act == 0b0) {
         meta.egress := 0b1
       } else {
         vlan.vid := 0b11
       }
     } else {
         skip
     }|}
    {|(x : \sigma z : meta . vlan) -> {w : \sigma z : ?meta . ?vlan | x.vlan.vid == w.vlan.vid}|}

let inner_bad_cust_table () =
  parse_typecheck Test.not_typecheck
    "header_type vlan_t {
       vid: 2;
     }
     header_type meta_t {
       egress: 1; 
     }
     header_type vlan_tbl_t {
       vid: 2;
       act: 1;     
     }
     header vlan : vlan_t
     header meta : meta_t
     header vlan_tbl : vlan_tbl_t
     add(vlan_tbl);          
     if (vlan.vid == 0x0) {
       if (vlan_tbl.act == 0b0) {
         vlan.vid := 0b00
       } else {
         vlan.vid := 0b11
       }
     } else {
         vlan.vid := 0b10
     }     
     "
    "(x : \\sigma y : meta . vlan) -> {w : \\sigma z : ?meta . ?vlan | x.vlan.vid == w.vlan.vid}"

let test_set =
  [ test_case "customer violates vlan integrity" `Quick inner_bad_cust;
    test_case "customer maintains vlan integrity" `Quick inner_ok_cust;
    test_case "customer modifies unconstrained field" `Quick inner_ok_cust2;
    test_case "customer applies table that _may_ change vlan" `Quick
      inner_bad_cust_table_path;
    test_case "customer applies table that _must_ change vlan" `Quick
      inner_bad_cust_table;
    test_case "ingress" `Quick cisco_ingress;
    test_case "customer applies table & doesn't change vlan" `Quick
      inner_ok_cust_table;
    test_case "egress" `Quick cisco_egress;
    test_case
      "customer facing intype type is a supertype of ingress output type" `Quick
      intype_composes;
    test_case "customer facing output type is a subtype of egress input type"
      `Quick outtype_composes
  ]
