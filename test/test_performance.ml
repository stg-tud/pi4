open Alcotest
open Pi4
open Syntax

module Config = struct
  let maxlen = ref(12000)
end

module P = Prover.Make (Encoding.FixedWidthBitvectorEncoding (Config))
module T = Typechecker.Make (Typechecker.SemanticChecker (Config))

let time f =
  let t = Unix.gettimeofday () in
  let res = f () in
  Printf.printf "Execution time: %f seconds\n"
                (Unix.gettimeofday () -. t);
  res

let test_typecheck header_table cmd ty smpl_subs incl_c len_c dyn_len =
  Prover.make_prover "z3";
  Alcotest.(check Testable.typechecker_result)
    (Fmt.str "%a" (Pretty.pp_pi_type []) ty)
    Typechecker.TypecheckingResult.Success(
    time(
      fun() -> (
        T.check_type cmd ty header_table 
          ~smpl_subs:smpl_subs 
          ~incl_cache:incl_c
          ~len_cache:len_c
          ~dynamic_maxlen:dyn_len
      )
    ))

let roundtrip_str = 
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
  ) -> {y:⊤| x =i= y })
  |}

let roundtrip_hty_str =
  {|(x:{y:ε|y.pkt_out.length == 0 && y.pkt_in.length > 304}) -> ⊤|}
  (* {|(x:{y:ε|y.pkt_out.length == 0 && y.pkt_in.length > 304}) -> {z:⊤ | x.pkt_in.length > 304}|} *)


let ipv4_ttl_str = 
  {|
    header_type ipv4_t {
      ttl: 8; 
    }
    header_type standard_metadata_t {
      egress_spec: 9;
    }
    header ipv4 : ipv4_t
    header meta : standard_metadata_t

    if(ipv4.valid) {
      if(ipv4.ttl == 0x00) {
        meta.egress_spec := 0b111111111
      } else {
        meta.egress_spec := 0b000000001;
        ipv4.ttl := ipv4.ttl - 0x01
      }
    }
  |}

let ipv4_ttl_hty_str = 
  {|
  (x:{y:⊤| y.ipv4.valid && y.meta.valid}) -> 
    {y:⊤|y.ipv4.valid &&y.meta.valid && ((x.ipv4.ttl==0x00) => (y.meta.egress_spec==0b111111111))}
  |}

let vlan_decap_str = 
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
      header_type forward_table_t {
        ipv4_dst_key: 32;
        act: 1;
        data_eth_src: 48;
        data_eth_dst: 48;
      }
      header ether : ether_t
      header ipv4 : ipv4_t
      header vlan : vlan_t
      header forward_table : forward_table_t

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
      if(ipv4.valid) {
        if(forward_table.act == 0b1) {
          ether.dstAddr := forward_table.data_eth_dst;
          ether.srcAddr := forward_table.data_eth_src;
          ipv4.ttl := ipv4.ttl - 0x01
        }
      };
      if(vlan.valid) {
        ether.etherType := vlan.etherType;
        remove(vlan)
      }
    |}

let vlan_decap_hty_str = 
  "(x:{y:forward_table |y.pkt_in.length > 304}) → {z:⊤|¬z.vlan.valid}"

let vlan_decap_hty_str_cplx = 
  {|
  (x:{y:forward_table |y.pkt_in.length > 304}) → 
  {z:⊤|
    ¬z.vlan.valid ∧
    x.pkt_in.length > 304
  }
  |}
  let test str t_str smpl_subs incl_c len_c dyn_len () =
  let program = Parsing.parse_program str in
  Logs.debug (fun m -> m "%a" Pretty.pp_command program.command);
  let header_table = HeaderTable.of_decls program.declarations in
  let ty = Parsing.parse_type t_str header_table in
  test_typecheck header_table program.command ty smpl_subs incl_c len_c dyn_len


let test_set =
  [ 
    test_case "Roundtrip Unoptimized" 
      `Quick (test roundtrip_str roundtrip_hty_str false false false false);
    test_case "Roundtrip +subs_folding" 
      `Quick (test roundtrip_str roundtrip_hty_str true false false false);
    test_case "Roundtrip +incl_cache" 
      `Quick (test roundtrip_str roundtrip_hty_str false true false false);
    test_case "Roundtrip +len_cache" 
      `Quick (test roundtrip_str roundtrip_hty_str false false true false);
    test_case "Roundtrip +dyn_maxlen" 
      `Quick (test roundtrip_str roundtrip_hty_str false false false true);
    test_case "Roundtrip Optimized" 
      `Quick (test roundtrip_str roundtrip_hty_str true true true true);
    test_case "IPv4 ttl Unoptimized" 
      `Quick (test ipv4_ttl_str ipv4_ttl_hty_str false false false false);
    test_case "IPv4 ttl +subs_folding" 
      `Quick (test ipv4_ttl_str ipv4_ttl_hty_str true false false false);
    test_case "IPv4 ttl +incl_cache" 
      `Quick (test ipv4_ttl_str ipv4_ttl_hty_str false true false false);
    test_case "IPv4 ttl +len_cache" 
      `Quick (test ipv4_ttl_str ipv4_ttl_hty_str false false true false);
    test_case "IPv4 ttl +dyn_maxlen" 
      `Quick (test ipv4_ttl_str ipv4_ttl_hty_str false false false true);
    test_case "IPv4 ttl Optimized" 
      `Quick (test ipv4_ttl_str ipv4_ttl_hty_str true true true true);
      test_case "VLAN decap Unoptimized" 
      `Quick (test vlan_decap_str vlan_decap_hty_str false false false false);
    test_case "VLAN decap +subs_folding" 
      `Quick (test vlan_decap_str vlan_decap_hty_str true false false false);
    test_case "VLAN decap +incl_cache" 
      `Quick (test vlan_decap_str vlan_decap_hty_str false true false false);
    test_case "VLAN decap +len_cache" 
      `Quick (test vlan_decap_str vlan_decap_hty_str false false true false);
    test_case "VLAN decap +dyn_maxlen" 
      `Quick (test vlan_decap_str vlan_decap_hty_str false false false true);
    test_case "VLAN decap Optimized" 
      `Quick (test vlan_decap_str vlan_decap_hty_str true true true true);
  ]