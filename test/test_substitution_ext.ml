open Alcotest
open Pi4
open Syntax
open Core_kernel
open Result
module Log = (val Logs.src_log Logging.substitution_src : Logs.LOG)

module TestConfig = struct
  let verbose = true

  let maxlen = ref(800)
end

module Config = struct
  let maxlen = TestConfig.maxlen
end

module P = Prover.Make (Encoding.FixedWidthBitvectorEncoding (Config))
module C = Typechecker.SemanticChecker (Config)

module Test = Test_utils.TestRunner (TestConfig)

let types_equiv program_str type_str ()= 
  let program = Parsing.parse_program program_str in
  let header_table = HeaderTable.of_decls program.declarations in
  let ty = Parsing.parse_type type_str header_table in
  match ty with
  | Pi (x, annot_tyin, _) ->  
    let tycout = C.compute_type program.command (x, annot_tyin) [] header_table ~smpl_subs:false in
    let simplified = C.compute_type program.command (x, annot_tyin) [] header_table ~smpl_subs:true in
    match tycout, simplified with
    | Ok ht, Ok smpl -> 
      let ctx = [ (x, Env.VarBind annot_tyin) ] in
      Log.info(fun m -> m "SMPL RAW: %a" Pretty.pp_header_type_raw smpl);
      Test.is_equiv ht smpl ctx header_table
    | _, Ok _  -> Alcotest.(check bool) "Failed type computation" false true
    | Ok _, _  -> Alcotest.(check bool) "Failed type computation for inlined type" false true
    | _ -> Alcotest.(check bool) "Failed type computation for both types" false true


let ipv4_ttl_hty_str = 
  {|
  (x:{y:⊤| y.ipv4.valid && y.meta.valid}) -> 
    {y:⊤|y.ipv4.valid &&y.meta.valid && ((x.ipv4.ttl==0x00) => (y.meta.egress_spec==0b111111111))}
  |}
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

let ipv4_opt_str = 
  {|
    header_type ethernet_t {
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
    header_type ipv4opt_t {
      type: 8;
    }
    header ether : ethernet_t
    header ipv4 : ipv4_t
    header ipv4opt : ipv4opt_t

    extract(ether);
    if(ether.etherType == 0x0800) {
      extract(ipv4);
      if(ipv4.ihl != 0x5) {
        extract(ipv4opt)
      }
    }
|}


let ipv4_opt_hty_str = 
{|
(x:{y:ε | y.pkt_in.length > 280}) -> 
  {y:⊤|((y.ipv4.valid && y.ipv4.ihl!=0x5) => y.ipv4opt.valid) && ((y.ipv4.valid && y.ipv4.ihl==0x5) => !y.ipv4opt.valid)}
|}

let mod_router_table_str = 
  {|
    header_type vlan_t {
      vid: 2;
    }
    header_type meta_t {
      egress_spec: 9;
    }
    header_type vlan_tbl_t {
      vid: 2;
      act: 1;
    }

    header vlan : vlan_t
    header meta : meta_t
    header vlan_tbl : vlan_tbl_t

    if (vlan.vid == vlan_tbl.vid) {
      if (vlan_tbl.act == 0b0) {
        meta.egress_spec := 0b111111111
      } else {
        meta.egress_spec := 0b000000001
      }
    }
  |}
  
let mod_router_table_hty_str = 
  {|
  (x : {x:⊤| x.meta.valid ∧ x.vlan.valid ∧ x.vlan_tbl.valid }) -> { y:⊤ | y.vlan.valid ∧ x.vlan.vid == y.vlan.vid}
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


let asc_roundtrip_str = 
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

let asc_roundtrip_hty = 
  {|(x:{y:ε|y.pkt_out.length == 0 && y.pkt_in.length > 304}) -> ⊤|}

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
let vlan_decap_type = 
  "(x:{y: forward_table |y.pkt_in.length > 304}) → {z:⊤|¬z.vlan.valid}"

let det_forward_str = 
{|
header_type ipv4_t {
  version: 4;
  ihl: 4;
  tos: 8;
  len: 16;
  id: 16;
  flg: 3;
  off: 13;
  src: 32;
  dst: 32;
  ttl: 8
}
header_type standard_metadata_t {
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
  mcast_grp: 16;
  egress_rid: 16;
  checksum_error: 1;
  priority: 3;
}
header ipv4 : ipv4_t
header stdmeta : standard_metadata_t

if(ipv4.valid) {
  if(ipv4.dst != 0x0A0A0A0A) {
    stdmeta.egress_spec := 0b000000001
  } else {
    stdmeta.egress_spec := 0b111111111
  }
}
|}

let det_forward_type =
  "(x:{y:ipv4~| y.stdmeta.valid}) -> {y:⊤| y.stdmeta.egress_spec != 0b000000000}"

let header_dep_str = 
{|
header_type ethernet_t {
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
header ether : ethernet_t
header ipv4 : ipv4_t

extract(ether);
if(ether.etherType == 0x0800) {
  extract(ipv4)
}
|}

let header_dep_type = 
"(x:{y:⊤|!y.ether.valid && !y.ipv4.valid && y.pkt_in.length > 272}) -> {y:⊤|y.ipv4.valid => y.ether.etherType == 0x0800}"

let tut_basic_str = 
{|
header_type ether_t {
  dst: 48;
  src: 48;
  type: 16;
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
header_type standard_metadata_t {
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
  mcast_grp: 16;
  egress_rid: 16;
  checksum_error: 1;
  priority: 3;
  drop: 1;
}
header_type forward_table_t {
  ipv4_dst_key: 32;
  act_ipv4_forward: 1;
  dst: 48;
  port: 9;
  ttl: 8;
}

header ether : ether_t
header ipv4 : ipv4_t
header stdmeta : standard_metadata_t
header forward_table : forward_table_t

extract(ether);
if(ether.type == 0x0800) {
  extract(ipv4)
};

if(ipv4.valid) {
  if(ipv4.dst == forward_table.ipv4_dst_key) {
    if(forward_table.act_ipv4_forward == 0b1) {
      stdmeta.egress_spec := forward_table.port;
      ether.src := ether.dst;
      ether.dst := forward_table.dst;
      ipv4.ttl := ipv4.ttl
    } else {
      stdmeta.drop := 0b1;
      stdmeta.mcast_grp := 0x0000
    }
  } else {
    stdmeta.drop := 0b1;
    stdmeta.mcast_grp := 0x0000
  }
};

if(stdmeta.drop != 0b1) {
  if(ether.valid){
    remit(ether)
  };
  if(ipv4.valid) {
    remit(ipv4)
  }
}

|}

let tut_basic_hty = 
{|
(x:{y:⊤|
    y.pkt_out.length == 0 ∧
    !y.ether.valid ∧
    !y.ipv4.valid ∧
    y.pkt_in.length > 272 ∧
    y.stdmeta.valid ∧
    y.forward_table.valid
    }) -> {y:⊤ | (y.stdmeta.drop == 0b1) => (y.pkt_out.length == 0)}
|}

let tut_basic_tunnel_str =
{|
header_type ether_t {
    dst: 48;
    src: 48;
    type: 16;
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
header_type standard_metadata_t {
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
    mcast_grp: 16;
    egress_rid: 16;
    checksum_error: 1;
    priority: 3;
    drop: 1;
}
header_type forward_table_t {
    ipv4_dst_key: 32;
    act_ipv4_forward: 1;
    dst: 48;
    port: 9;
}
header_type tunnel_table_t {
    dest_id_key: 16;
    act: 1;
    port: 9;
}
header_type my_tunnel_t{
    proto_id: 16;
    dst_id: 16;
}

header ether : ether_t
header ipv4 : ipv4_t
header stdmeta : standard_metadata_t
header forward_table : forward_table_t
header tunnel_table : tunnel_table_t
header my_tnl : my_tunnel_t

extract(ether);
if(ether.type == 0x1212) {
    extract(my_tnl);
    if(my_tnl.proto_id == 0x0800){
        extract(ipv4)
    }
};

if(ipv4.valid) {
    if(!my_tnl.valid){
        if(ipv4.dst == forward_table.ipv4_dst_key) {
          if(forward_table.act_ipv4_forward == 0b1) {
            stdmeta.egress_spec := forward_table.port;
            ether.src := ether.dst;
            ether.dst := forward_table.dst;
            ipv4.ttl := ipv4.ttl - 0b00000001
          } else {
            stdmeta.drop := 0b1;
            stdmeta.mcast_grp := 0x0000
          }
        } else {
          stdmeta.drop := 0b1;
          stdmeta.mcast_grp := 0x0000
        }
    } else {
        stdmeta.drop := 0b1;
        stdmeta.mcast_grp := 0x0000
    }
};

if(my_tnl.valid){
    if(my_tnl.dst_id == tunnel_table.dest_id_key){
      if(tunnel_table.act == 0b1){
        stdmeta.egress_spec := tunnel_table.port
      } else {
        stdmeta.drop := 0b1;
        stdmeta.mcast_grp := 0x0000
      }
    }
};

if(stdmeta.drop != 0b1) {
  if(ether.valid){
    remit(ether)
  };
  if(my_tnl.valid){
    remit(my_tnl)
  };
  if(ipv4.valid){
    remit(ipv4)
  }
}

|}

let tut_basic_tunnel_hty =
  {|
  (x:{y:⊤|
  y.pkt_out.length == 0 ∧
  y.pkt_in.length > 304 ∧
  ¬y.ether.valid ∧
  ¬y.ipv4.valid ∧
  y.stdmeta.valid ∧
  y.forward_table.valid ∧
  y.tunnel_table.valid ∧
  ¬y.my_tnl.valid
  }) -> ⊤

  |}



let tut_load_balance_str = 
{|

header_type ether_t {
  dst: 48;
  src: 48;
  type: 16;
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
header_type tcp_t {
  srcPort: 16;
  dstPort: 16;
  seqNo: 32;
  ackNo: 32;
  dataOffset: 4;
  res: 3;
  ecn: 3;
  ctrl: 6;
  window: 16;
  checksum: 16;
  urgentPtr: 16;
}

header_type standard_metadata_t {
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
  mcast_grp: 16;
  egress_rid: 16;
  checksum_error: 1;
  priority: 3;
  drop: 1;
}
header_type ecmp_table_t {
  ipv4_dst_key: 32;
  act_ipv4_forward: 1;
  ecmp_hash: 14;
}
header_type nhop_table_t {
  ecmp_hash_key: 14;
  act_nhop: 1;
  nhop_dmac: 48;
  nhop_ipv4: 32;
  port: 9;
  ttl: 8;
}
header_type egress_table_t{
  port_key: 9;
  act_egress: 1;
  smac: 48;
}
header_type meta_t {
  ecmp_select: 14;
}

header ether : ether_t
header ipv4 : ipv4_t
header tcp : tcp_t
header stdmeta : standard_metadata_t
header ecmp_table : ecmp_table_t
header nhop_table : nhop_table_t
header egress_table : egress_table_t
header meta : meta_t

extract(ether);
if(ether.type == 0x0800) {
  extract(ipv4);
  if(ipv4.proto == 0b00001001){
    extract(tcp)
  }
};

if(ipv4.valid) {
  if(ecmp_table.ipv4_dst_key == ipv4.dst){
    if(ecmp_table.act_ipv4_forward == 0b1){
      meta.ecmp_select := ecmp_table.ecmp_hash
    } else {
      stdmeta.drop := 0b1;
      stdmeta.mcast_grp := 0x0000
    }
  };

  if(meta.ecmp_select == nhop_table.ecmp_hash_key) {
    if(nhop_table.act_nhop == 0b1){
      ether.dst := nhop_table.nhop_dmac;
      ipv4.dst := nhop_table.nhop_ipv4;
      stdmeta.egress_spec := nhop_table.port;
      ipv4.ttl := nhop_table.ttl
    } else {
      stdmeta.drop := 0b1;
      stdmeta.mcast_grp := 0x0000
    }
  }
}

|}

let tut_load_balance_hty =
  {|
  (x:{y:⊤|
    y.pkt_out.length == 0 ∧
    y.pkt_in.length > 432 ∧
    ¬y.ether.valid ∧
    ¬y.ipv4.valid ∧
    ¬y.tcp.valid ∧
    y.stdmeta.valid ∧
    y.ecmp_table.valid ∧
    y.nhop_table.valid ∧
    y.egress_table.valid ∧
    y.meta.valid
    }) -> ⊤

  |}

let tut_basic_min_str = 
{|

header_type ipv4_t {
    ihl: 2;
    ttl: 4
    flg: 2;
}

header ipv4 : ipv4_t

  extract(ipv4);
  ipv4.ttl := 0b1010
|}

let tut_basic_min_hty =
  "(x:{y: ⊤ | y.pkt_in.length > 8}) -> {q:⊤ | true}"

let test_set = 
  [
    test_case "ipv4_ttl" `Quick (types_equiv ipv4_ttl_str ipv4_ttl_hty_str);
    test_case "ipv4_opt" `Quick (types_equiv ipv4_opt_str ipv4_opt_hty_str);
    test_case "mod_router_table" `Quick (types_equiv mod_router_table_str mod_router_table_hty_str);
    test_case "roundtrip" `Quick (types_equiv safe_roundtrip_string safe_roundtrip_type_string);
    test_case "asc_roundtrip" `Quick (types_equiv asc_roundtrip_str asc_roundtrip_hty);
    test_case "vlan_decap" `Quick (types_equiv vlan_decap_str vlan_decap_type);
    test_case "determined forwarding" `Quick (types_equiv det_forward_str det_forward_type);
    test_case "header dependency" `Quick (types_equiv header_dep_str header_dep_type);
    test_case "tut basic" `Quick (types_equiv tut_basic_str tut_basic_hty);
    test_case "tut basic tunnel" `Quick (types_equiv tut_basic_tunnel_str tut_basic_tunnel_hty);
    test_case "tut load_balance" `Quick (types_equiv tut_load_balance_str tut_load_balance_hty);
  ]
