open Alcotest
open Pi4
open Syntax

module Config = struct
  let maxlen = 1500
end

module P = Prover.Make (Encoding.FixedWidthBitvectorEncoding (Config))
module T = Typechecker.Make (Typechecker.SemanticChecker (Config))

let test_typecheck header_table cmd ty =
  Prover.make_prover "z3";
  Alcotest.(check Testable.typechecker_result)
    (Fmt.str "%a" (Pretty.pp_type []) ty)
    Typechecker.TypecheckingResult.Success
    (T.check_type cmd ty header_table)

let test_typecheck_fails header_table cmd ty =
  Prover.make_prover "z3";
  Alcotest.(check bool)
    (Fmt.str "%a" (Pretty.pp_type []) ty)
    true
    (Typechecker.TypecheckingResult.is_error (T.check_type cmd ty header_table))

let safe_parser_string =
  {|  
    header_type ether_t {
      dstAddr: 48;
      srcAddr: 48;
      etherType: 16;
    }
    header_type ipv4_t {
      version: 4; 
      ihl: 4; 
      tos: 8; 
      len: 16; 
      id: 16; 
      flags: 3; 
      frag: 13; 
      ttl: 8; 
      proto: 8; 
      chksum: 16; 
      src: 32; 
      dst: 32;
    }
    header_type vlan_t {
      prio: 3; 
      id: 1; 
      vlan: 12; 
      etherType: 16;
    }
    header ether : ether_t
    header ipv4 : ipv4_t
    header vlan : vlan_t

    extract(ether);
    if(ether.etherType == 0x8100) {
      extract(vlan);
      if(vlan.etherType == 0x0800) {
        extract(ipv4)
      }
    } else {
      if(ether.etherType == 0x0800) {
        extract(ipv4)
      }
    }
  |}

let safe_parser_type_string =
  {|
    (x:{y:⊤|!y.ether.valid && 
            !y.ipv4.valid && 
            !y.vlan.valid && 
            y.pkt_in.length > 304 && 
            y.pkt_out.length == 0}) -> 
        {y:⊤|y.ether.valid && 
              y.ether.etherType != 0x0800 && 
              y.ether.etherType != 0x8100 && 
              !y.ipv4.valid && 
              !y.vlan.valid && 
              y.pkt_in.length > 192 && 
              y.pkt_out.length == 0} + 
        {y:⊤|y.ether.valid && 
              y.ether.etherType == 0x8100 && 
              !y.ipv4.valid && y.vlan.valid && 
              y.vlan.etherType != 0x0800 && 
              y.pkt_in.length > 160 && 
              y.pkt_out.length == 0} + 
        {y:⊤|y.ether.valid && 
              y.ether.etherType == 0x0800 && 
              y.ipv4.valid && 
              !y.vlan.valid && 
              y.pkt_in.length > 32 && 
              y.pkt_out.length == 0} + 
        {y:⊤|y.ether.valid && 
              y.ether.etherType == 0x8100 && 
              y.ipv4.valid && y.vlan.valid && 
              y.vlan.etherType == 0x0800 && 
              y.pkt_in.length > 0 && 
              y.pkt_out.length == 0}
    |}

let safe_ingress_string =
  {|
  header_type ether_t {
    dstAddr: 48;
    srcAddr: 48;
    etherType: 16;
  }
  header_type ipv4_t {
    version: 4; 
    ihl: 4; 
    tos: 8; 
    len: 16; 
    id: 16; 
    flags: 3; 
    frag: 13; 
    ttl: 8; 
    proto: 8; 
    chksum: 16; 
    src: 32; 
    dst: 32;
  }
  header_type vlan_t {
    prio: 3; 
    id: 1; 
    vlan: 12; 
    etherType: 16;
  }
  header ether : ether_t
  header ipv4 : ipv4_t
  header vlan : vlan_t
  
  if(!vlan.valid) {
    add(vlan);
    ether.etherType := 0x8100;
    if(ipv4.valid) {
      vlan.etherType := 0x0800
    }
  }
|}

let safe_ingress_type_string =
  {|
    (x:({y:⊤|y.ether.valid && 
              y.ether.etherType != 0x0800 && 
              y.ether.etherType != 0x8100 && 
              !y.ipv4.valid && 
              !y.vlan.valid && 
              y.pkt_in.length > 192 && 
              y.pkt_out.length == 0} + 
        {y:⊤|y.ether.valid && 
              y.ether.etherType == 0x8100 && 
              !y.ipv4.valid && y.vlan.valid && 
              y.vlan.etherType != 0x0800 && 
              y.pkt_in.length > 160 && 
              y.pkt_out.length == 0} + 
        {y:⊤|y.ether.valid && 
              y.ether.etherType == 0x0800 && 
              y.ipv4.valid && 
              !y.vlan.valid && 
              y.pkt_in.length > 32 && 
              y.pkt_out.length == 0} +
        {y:⊤|y.ether.valid && 
              y.ether.etherType == 0x8100 && 
              y.ipv4.valid && y.vlan.valid && 
              y.vlan.etherType == 0x0800 && 
              y.pkt_in.length > 0 && 
              y.pkt_out.length == 0})) ->
                {z:⊤|z.ether.valid && 
                      z.ether.etherType == 0x8100 && 
                      z.vlan.valid && 
                      (z.ipv4.valid => z.vlan.etherType == 0x0800) && 
                      ((!z.ipv4.valid) => z.vlan.etherType != 0x0800) && 
                      z.pkt_out.length == 0 && 
                      z.pkt_in.length > 0}
  |}

let safe_roundtrip_string =
  {|
  header_type ether_t {
    dstAddr: 48;
    srcAddr: 48;
    etherType: 16;
  }
  header_type ipv4_t {
    version: 4; 
    ihl: 4; 
    tos: 8; 
    len: 16; 
    id: 16; 
    flags: 3; 
    frag: 13; 
    ttl: 8; 
    proto: 8; 
    chksum: 16; 
    src: 32; 
    dst: 32;
  }
  header_type vlan_t {
    prio: 3; 
    id: 1; 
    vlan: 12; 
    etherType: 16;
  }
  header ether : ether_t
  header ipv4 : ipv4_t
  header vlan : vlan_t

  if(ether.valid) {
    remit(ether)
  };
  if(vlan.valid) {
    remit(vlan)
  };
  if(ipv4.valid) {
    remit(ipv4)
  };
  reset;
  extract(ether);
  if(ether.etherType == 0x8100) {
    extract(vlan);
    if(vlan.etherType == 0x0800) {
      extract(ipv4)
    }
  } else {
    if(ether.etherType == 0x0800) {
      extract(ipv4)
    }
  }
|}

let safe_roundtrip_type_string =
  {|
    (x:{y:⊤|y.ether.valid && 
            y.ether.etherType == 0x8100 && 
            y.vlan.valid && 
            (y.ipv4.valid => y.vlan.etherType == 0x0800) && 
            ((!y.ipv4.valid) => (y.vlan.etherType != 0x0800)) && 
            y.pkt_out.length == 0 && 
            y.pkt_in.length > 0}) -> 
        {y:⊤|y.ether.valid && 
              y.ether == x.ether && 
              y.vlan.valid && 
              y.vlan == x.vlan && 
              (x.ipv4.valid => (y.ipv4.valid && y.vlan.etherType == 0x0800 && y.ipv4 == x.ipv4)) &&
              ((!x.ipv4.valid) => (!y.ipv4.valid && y.vlan.etherType != 0x0800))}
  |}

let safe_roundtrip_complete_string =
  {|
    header_type ether_t {
      dstAddr: 48;
      srcAddr: 48;
      etherType: 16;
    }
    header_type ipv4_t {
      version: 4; 
      ihl: 4; 
      tos: 8; 
      len: 16; 
      id: 16; 
      flags: 3; 
      frag: 13; 
      ttl: 8; 
      proto: 8; 
      chksum: 16; 
      src: 32; 
      dst: 32;
    }
    header_type vlan_t {
      prio: 3; 
      id: 1; 
      vlan: 12; 
      etherType: 16;
    }
    header ether : ether_t
    header ipv4 : ipv4_t
    header vlan : vlan_t

    extract(ether);
    if(ether.etherType == 0x8100) {
      extract(vlan);
      if(vlan.etherType == 0x0800) {
        extract(ipv4)
      }
    } else {
      if(ether.etherType == 0x0800) {
        extract(ipv4)
      }
    };
    if(!vlan.valid) {
      add(vlan);
      ether.etherType := 0x8100;
      if(ipv4.valid) {
        vlan.etherType := 0x0800
      }
    };
   ((if(ether.valid) {
      remit(ether)
    };
    if(vlan.valid) {
      remit(vlan)
    };
    if(ipv4.valid) {
      remit(ipv4)
    };
    reset;
    extract(ether);
    if(ether.etherType == 0x8100) {
      extract(vlan);
      if(vlan.etherType == 0x0800) {
        extract(ipv4)
      }
    } else {
      if(ether.etherType == 0x0800) {
        extract(ipv4)
      }
    }) as (x :  
          {z:ether~| 
               z.ether.etherType == 0x8100 && 
               z.vlan.valid && 
               (z.ipv4.valid => z.vlan.etherType == 0x0800) && 
               ((!z.ipv4.valid) => z.vlan.etherType != 0x0800) && 
               z.pkt_out.length == 0 && 
               z.pkt_in.length > 0}
    ) -> {y:⊤| x === y })
   |}

let safe_roundtrip_complete_type_string =
  {|
    (x:{y:ε|y.pkt_out.length == 0 && y.pkt_in.length > 304}) -> ⊤
   |}
        (* {y:⊤|y.ether.valid && 
         *       y.vlan.valid && 
         *       y.ether.etherType == 0x8100 && 
         *       (y.ipv4.valid => y.vlan.etherType == 0x0800) &&
         *       ((!y.ipv4.valid) => y.vlan.etherType != 0x0800)} *)
  

let unsafe_ingress_string =
  {|
  header_type ether_t {
    dstAddr: 48;
    srcAddr: 48;
    etherType: 16;
  }
  header_type ipv4_t {
    version: 4; 
    ihl: 4; 
    tos: 8; 
    len: 16; 
    id: 16; 
    flags: 3; 
    frag: 13; 
    ttl: 8; 
    proto: 8; 
    chksum: 16; 
    src: 32; 
    dst: 32;
  }
  header_type vlan_t {
    prio: 3; 
    id: 1; 
    vlan: 12; 
    etherType: 16;
  }
  header ether : ether_t
  header ipv4 : ipv4_t
  header vlan : vlan_t
  
  if(!vlan.valid) {
    add(vlan);
    if(ipv4.valid) {
      vlan.etherType := 0x0800
    }
  }
|}

let unsafe_ingress_type_string =
  {|
    (x:({y:⊤|y.ether.valid && 
      y.ether.etherType != 0x0800 && 
      y.ether.etherType != 0x8100 && 
      !y.ipv4.valid && 
      !y.vlan.valid && 
      y.pkt_in.length > 192 && 
      y.pkt_out.length == 0} + 
    {y:⊤|y.ether.valid && 
      y.ether.etherType == 0x8100 && 
      !y.ipv4.valid && y.vlan.valid && 
      y.vlan.etherType != 0x0800 && 
      y.pkt_in.length > 160 && 
      y.pkt_out.length == 0} + 
    {y:⊤|y.ether.valid && 
      y.ether.etherType == 0x0800 && 
      y.ipv4.valid && 
      !y.vlan.valid && 
      y.pkt_in.length > 32 && 
      y.pkt_out.length == 0} +
    {y:⊤|y.ether.valid && 
      y.ether.etherType == 0x8100 && 
      y.ipv4.valid && y.vlan.valid && 
      y.vlan.etherType == 0x0800 && 
      y.pkt_in.length > 0 && 
      y.pkt_out.length == 0})) ->
        {z:⊤|z.ether.valid && 
              z.vlan.valid && 
              (x.ipv4.valid => (z.ipv4.valid && z.vlan.etherType == 0x0800)) && 
              ((!x.ipv4.valid) => (!z.ipv4.valid && z.vlan.etherType != 0x0800)) && 
              z.pkt_out.length == 0 && 
              z.pkt_in.length > 0}
  |}

let unsafe_roundtrip_string =
  {|
    header_type ether_t {
      dstAddr: 48;
      srcAddr: 48;
      etherType: 16;
    }
    header_type ipv4_t {
      version: 4; 
      ihl: 4; 
      tos: 8; 
      len: 16; 
      id: 16; 
      flags: 3; 
      frag: 13; 
      ttl: 8; 
      proto: 8; 
      chksum: 16; 
      src: 32; 
      dst: 32;
    }
    header_type vlan_t {
      prio: 3; 
      id: 1; 
      vlan: 12; 
      etherType: 16;
    }
    header ether : ether_t
    header ipv4 : ipv4_t
    header vlan : vlan_t

    extract(ether);
    if(ether.etherType == 0x8100) {
      extract(vlan);
      if(vlan.etherType == 0x0800) {
        extract(ipv4)
      }
    } else {
      if(ether.etherType == 0x0800) {
        extract(ipv4)
      }
    };
    if(!vlan.valid) {
      add(vlan);
      if(ipv4.valid) {
        vlan.etherType := 0x0800
      }
    };
    ((if(ether.valid) {
      remit(ether)
    };
    if(vlan.valid) {
      remit(vlan)
    };
    if(ipv4.valid) {
      remit(ipv4)
    };
    reset;
    extract(ether);
    if(ether.etherType == 0x8100) {
      extract(vlan);
      if(vlan.etherType == 0x0800) {
        extract(ipv4)
      }
    } else {
      if(ether.etherType == 0x0800) {
        extract(ipv4)
      }
    }) as (x :  
          {z:ether~| 
               z.ether.etherType == 0x8100 && 
               z.vlan.valid && 
               (z.ipv4.valid => z.vlan.etherType == 0x0800) && 
               ((!z.ipv4.valid) => z.vlan.etherType != 0x0800) && 
               z.pkt_out.length == 0 && 
               z.pkt_in.length > 0}
    ) -> {y:⊤| x === y })
  |}

let test_safe_parser () =
  let program = Parsing.parse_program safe_parser_string in
  Logs.debug (fun m -> m "%a" Pretty.pp_command program.command);
  let header_table = HeaderTable.of_decls program.declarations in
  let ty = Parsing.parse_type safe_parser_type_string header_table in
  test_typecheck header_table program.command ty

let test_safe_ingress () =
  let program = Parsing.parse_program safe_ingress_string in
  Logs.debug (fun m -> m "%a" Pretty.pp_command program.command);
  let header_table = HeaderTable.of_decls program.declarations in
  let ty = Parsing.parse_type safe_ingress_type_string header_table in
  test_typecheck header_table program.command ty

let test_safe_roundtrip () =
  let program = Parsing.parse_program safe_roundtrip_string in
  Logs.debug (fun m -> m "%a" Pretty.pp_command program.command);
  let header_table = HeaderTable.of_decls program.declarations in
  let ty = Parsing.parse_type safe_roundtrip_type_string header_table in
  test_typecheck header_table program.command ty

let test_safe_roundtrip_complete () =
  let program = Parsing.parse_program safe_roundtrip_complete_string in
  Logs.debug (fun m -> m "%a" Pretty.pp_command program.command);
  let header_table = HeaderTable.of_decls program.declarations in
  let ty =
    Parsing.parse_type safe_roundtrip_complete_type_string header_table
  in
  test_typecheck header_table program.command ty

let test_unsafe_ingress () =
  let program = Parsing.parse_program unsafe_ingress_string in
  Logs.debug (fun m -> m "%a" Pretty.pp_command program.command);
  let header_table = HeaderTable.of_decls program.declarations in
  let ty = Parsing.parse_type unsafe_ingress_type_string header_table in
  test_typecheck header_table program.command ty

let test_unsafe_roundtrip () =
  let program = Parsing.parse_program unsafe_roundtrip_string in
  Logs.debug (fun m -> m "%a" Pretty.pp_command program.command);
  let header_table = HeaderTable.of_decls program.declarations in
  let ty =
    Parsing.parse_type safe_roundtrip_complete_type_string header_table
  in
  test_typecheck_fails header_table program.command ty

let test_set =
  [ test_case "Safe parser" `Quick test_safe_parser;
    test_case "Safe ingress" `Quick test_safe_ingress;
    test_case "Safe roundtrip" `Quick test_safe_roundtrip;
    test_case "Safe roundtrip complete" `Quick test_safe_roundtrip_complete;
    test_case "Unsafe ingress" `Quick test_unsafe_ingress;
    test_case "Unsafe roundtrip does not typecheck" `Quick test_unsafe_roundtrip
  ]
