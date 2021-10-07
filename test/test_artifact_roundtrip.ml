open Alcotest
open Pi4
open Syntax

module Config = struct
  let maxlen = 320
end

module P = Prover.Make (Encoding.FixedWidthBitvectorEncoding (Config))
module T = Typechecker.MakeSSAChecker (Typechecker.CompleteChecker (Config))
            
let test_typecheck_ssa header_table cmd ty =
  Prover.make_prover "z3";
  Alcotest.(check Testable.typechecker_result)
    (Fmt.str "%a" (Pretty.pp_type []) ty)
    Typechecker.TypecheckingResult.Success
    (T.check_type cmd ty header_table)

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
    header ether_0 : ether_t
    header ether_1 : ether_t
    header ipv4_0 : ipv4_t
    header ipv4_1 : ipv4_t
    header vlan_0 : vlan_t
    header vlan_1 : vlan_t

    (extract(ether_1) as (x:{y:⊤|!y.ether_0.valid && !y.ether_1.valid && !y.ipv4_0.valid && !y.ipv4_1.valid && !y.vlan_0.valid && !y.vlan_1.valid && y.pkt_in.length > 304}) -> {y:⊤|!y.ether_0.valid && y.ether_1.valid && !y.ipv4_0.valid && !y.ipv4_1.valid && !y.vlan_0.valid && !y.vlan_1.valid && y.pkt_in.length > 192});
    if(ether_1.etherType == 0x8100) {
      (extract(vlan_1);
      if(vlan_1.etherType == 0x0800) {
        extract(ipv4_1)
      } else {
        if(ipv4_0.valid) {
          add(ipv4_1);
          ipv4_1[0:160] := ipv4_0[0:160]
        } else {
          skip
          }
        })
    } else {
      if(ether_1.etherType == 0x0800) {
          extract(ipv4_1)
      } else {
        if(ipv4_0.valid) {
          add(ipv4_1);
          ipv4_1[0:160] := ipv4_0[0:160]
        } else {
          skip
        }
      };
      if(vlan_0.valid) {
        add(vlan_1);
        vlan_1[0:32] := vlan_0[0:32]
      } else {
        skip
      }
    }
  |}  

let safe_parser_type_string = 
{|
  (x:{y:⊤|!y.ether_0.valid && !y.ether_1.valid && !y.ipv4_0.valid && !y.ipv4_1.valid && !y.vlan_0.valid && !y.vlan_1.valid && y.pkt_in.length > 304}) -> ({y:⊤|!y.ether_0.valid && y.ether_1.valid && (!y.ether_1.etherType == 0x0800) && (!y.ether_1.etherType == 0x8100) && !y.ipv4_0.valid && !y.ipv4_1.valid && !y.vlan_0.valid && !y.vlan_1.valid} + 
  {y:⊤|!y.ether_0.valid && y.ether_1.valid && y.ether_1.etherType == 0x8100 && !y.ipv4_0.valid && !y.ipv4_1.valid && !y.vlan_0.valid && y.vlan_1.valid && (!y.vlan_1.etherType == 0x0800)} + 
  {y:⊤|!y.ether_0.valid && y.ether_1.valid && y.ether_1.etherType == 0x0800 && !y.ipv4_0.valid && y.ipv4_1.valid && !y.vlan_0.valid && !y.vlan_1.valid} + 
  {y:⊤|!y.ether_0.valid && y.ether_1.valid && y.ether_1.etherType == 0x8100 && !y.ipv4_0.valid && y.ipv4_1.valid && !y.vlan_0.valid && y.vlan_1.valid && y.vlan_1.etherType == 0x0800})
|}  

let safe_ingress_string = {|
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
  header ether_0 : ether_t
  header ether_1 : ether_t
  header ipv4_0 : ipv4_t
  header vlan_0 : vlan_t
  header vlan_1 : vlan_t
  header vlan_2 : vlan_t

  if(!vlan_0.valid) {
    (((((add(vlan_1) as (x: {y:⊤|y.ether_0.valid && (!y.ether_0.etherType == 0x0800) && (!y.ether_0.etherType == 0x8100) && !y.ether_1.valid && !y.ipv4_0.valid && !y.vlan_0.valid && !y.vlan_1.valid && !y.vlan_2.valid} +
    {y:⊤|y.ether_0.valid && y.ether_0.etherType == 0x0800 && !y.ether_1.valid && y.ipv4_0.valid && !y.vlan_0.valid && !y.vlan_1.valid && !y.vlan_2.valid}) -> 
    {y:⊤|y.ether_0.valid && (!y.ether_0.etherType == 0x0800) && (!y.ether_0.etherType == 0x8100) && !y.ether_1.valid && !y.ipv4_0.valid && !y.vlan_0.valid && y.vlan_1.valid && !y.vlan_2.valid} +
    {y:⊤|y.ether_0.valid && y.ether_0.etherType == 0x0800 && !y.ether_1.valid && y.ipv4_0.valid && !y.vlan_0.valid && y.vlan_1.valid && !y.vlan_2.valid});
    ((if(ipv4_0.valid) {
      (((add(vlan_2) as (x:{y:⊤|y.ether_0.valid && y.ether_0.etherType == 0x0800 && !y.ether_1.valid && y.ipv4_0.valid && !y.vlan_0.valid && y.vlan_1.valid && !y.vlan_2.valid}) -> {y:⊤|y.ether_0.valid && y.ether_0.etherType == 0x0800 && !y.ether_1.valid && y.ipv4_0.valid && !y.vlan_0.valid && y.vlan_1.valid && y.vlan_2.valid});
      vlan_2[16:32] := 0x0800;
      vlan_2[0:16] := vlan_1[0:16]) as (x:{y:⊤|y.ether_0.valid && y.ether_0.etherType == 0x0800 && !y.ether_1.valid && y.ipv4_0.valid && !y.vlan_0.valid && y.vlan_1.valid && !y.vlan_2.valid}) -> {y:⊤|y.ether_0.valid && y.ether_0.etherType == 0x0800 && !y.ether_1.valid && y.ipv4_0.valid && !y.vlan_0.valid && y.vlan_1.valid && y.vlan_2.valid && y.vlan_2.etherType == 0x0800})
    } else {
      ((if(vlan_1.valid) {
        add(vlan_2);
        vlan_2[0:32] := vlan_1[0:32]
      } else {
        skip
      }) as (x:{y:⊤|y.ether_0.valid && (!y.ether_0.etherType == 0x0800) && (!y.ether_0.etherType == 0x8100) && !y.ether_1.valid && !y.ipv4_0.valid && !y.vlan_0.valid && y.vlan_1.valid && !y.vlan_2.valid}) -> {y:⊤|y.ether_0.valid && (!y.ether_0.etherType == 0x0800) && (!y.ether_0.etherType == 0x8100) && !y.ether_1.valid && !y.ipv4_0.valid && !y.vlan_0.valid && y.vlan_1.valid && y.vlan_2.valid})
    }) as (x: {y:⊤|y.ether_0.valid && (!y.ether_0.etherType == 0x0800) && (!y.ether_0.etherType == 0x8100) && !y.ether_1.valid && !y.ipv4_0.valid && !y.vlan_0.valid && y.vlan_1.valid && !y.vlan_2.valid} + {y:⊤|y.ether_0.valid && y.ether_0.etherType == 0x0800 && !y.ether_1.valid && y.ipv4_0.valid && !y.vlan_0.valid && y.vlan_1.valid && !y.vlan_2.valid}) -> {y:⊤|y.ether_0.valid && y.ether_0.etherType == 0x0800 && !y.ether_1.valid && y.ipv4_0.valid && !y.vlan_0.valid && y.vlan_1.valid && y.vlan_2.valid && y.vlan_2.etherType == 0x0800} + {y:⊤|y.ether_0.valid && (!y.ether_0.etherType == 0x0800) && (!y.ether_0.etherType == 0x8100) && !y.ether_1.valid && !y.ipv4_0.valid && !y.vlan_0.valid && y.vlan_1.valid && y.vlan_2.valid})) as (x: {y:⊤|y.ether_0.valid && (!y.ether_0.etherType == 0x0800) && (!y.ether_0.etherType == 0x8100) && !y.ether_1.valid && !y.ipv4_0.valid && !y.vlan_0.valid && !y.vlan_1.valid && !y.vlan_2.valid} +
    {y:⊤|y.ether_0.valid && y.ether_0.etherType == 0x0800 && !y.ether_1.valid && y.ipv4_0.valid && !y.vlan_0.valid && !y.vlan_1.valid && !y.vlan_2.valid}) -> {y:⊤|y.ether_0.valid && y.ether_0.etherType == 0x0800 && !y.ether_1.valid && y.ipv4_0.valid && !y.vlan_0.valid && y.vlan_1.valid && y.vlan_2.valid && y.vlan_2.etherType == 0x0800} + {y:⊤|y.ether_0.valid && (!y.ether_0.etherType == 0x0800) && (!y.ether_0.etherType == 0x8100) && !y.ether_1.valid && !y.ipv4_0.valid && !y.vlan_0.valid && y.vlan_1.valid && y.vlan_2.valid});
    (add(ether_1) as (x:{y:⊤|y.ether_0.valid && y.ether_0.etherType == 0x0800 && !y.ether_1.valid && y.ipv4_0.valid && !y.vlan_0.valid && y.vlan_1.valid && y.vlan_2.valid && y.vlan_2.etherType == 0x0800} + {y:⊤|y.ether_0.valid && (!y.ether_0.etherType == 0x0800) && (!y.ether_0.etherType == 0x8100) && !y.ether_1.valid && !y.ipv4_0.valid && !y.vlan_0.valid && y.vlan_1.valid && y.vlan_2.valid}) -> {y:⊤|y.ether_0.valid && y.ether_0.etherType == 0x0800 && y.ether_1.valid && y.ipv4_0.valid && !y.vlan_0.valid && y.vlan_1.valid && y.vlan_2.valid && y.vlan_2.etherType == 0x0800} + {y:⊤|y.ether_0.valid && (!y.ether_0.etherType == 0x0800) && (!y.ether_0.etherType == 0x8100) && y.ether_1.valid && !y.ipv4_0.valid && !y.vlan_0.valid && y.vlan_1.valid && y.vlan_2.valid})) as (x: {y:⊤|y.ether_0.valid && (!y.ether_0.etherType == 0x0800) && (!y.ether_0.etherType == 0x8100) && !y.ether_1.valid && !y.ipv4_0.valid && !y.vlan_0.valid && !y.vlan_1.valid && !y.vlan_2.valid} +
    {y:⊤|y.ether_0.valid && y.ether_0.etherType == 0x0800 && !y.ether_1.valid && y.ipv4_0.valid && !y.vlan_0.valid && !y.vlan_1.valid && !y.vlan_2.valid}) -> {y:⊤|y.ether_0.valid && y.ether_0.etherType == 0x0800 && y.ether_1.valid && y.ipv4_0.valid && !y.vlan_0.valid && y.vlan_1.valid && y.vlan_2.valid && y.vlan_2.etherType == 0x0800} + {y:⊤|y.ether_0.valid && (!y.ether_0.etherType == 0x0800) && (!y.ether_0.etherType == 0x8100) && y.ether_1.valid && !y.ipv4_0.valid && !y.vlan_0.valid && y.vlan_1.valid && y.vlan_2.valid});
    ether_1[96:112] := 0x8100;
    ether_1[0:96] := ether_0[0:96]
  } else {
    if(vlan_0.valid) {
      add(vlan_1);
      vlan_1[0:32] := vlan_0[0:32]
    } else {
      skip
    };
    if(vlan_1.valid) {
      add(vlan_2);
      vlan_2[0:32] := vlan_1[0:32]
    } else {
      skip
    };
    if(ether_0.valid) {
      add(ether_1);
      ether_1[0:112] := ether_0[0:112]
    } else {
      skip
    }
  }
|}

let safe_ingress_type_string = {|
(x: {y:⊤|y.ether_0.valid && (!y.ether_0.etherType == 0x0800) && (!y.ether_0.etherType == 0x8100) && !y.ether_1.valid && !y.ipv4_0.valid && !y.vlan_0.valid && !y.vlan_1.valid && !y.vlan_2.valid} +
{y:⊤|y.ether_0.valid && y.ether_0.etherType == 0x8100 && !y.ether_1.valid && !y.ipv4_0.valid && y.vlan_0.valid && (!y.vlan_0.etherType == 0x0800) && !y.vlan_1.valid && !y.vlan_2.valid} +
{y:⊤|y.ether_0.valid && y.ether_0.etherType == 0x0800 && !y.ether_1.valid && y.ipv4_0.valid && !y.vlan_0.valid && !y.vlan_1.valid && !y.vlan_2.valid} + 
{y:⊤|y.ether_0.valid && y.ether_0.etherType == 0x8100 && !y.ether_1.valid && y.ipv4_0.valid && y.vlan_0.valid && y.vlan_0.etherType == 0x0800 && !y.vlan_1.valid && !y.vlan_2.valid}) ->
  {y:⊤|y.ether_0.valid && (!y.ether_0.etherType == 0x0800) && (!y.ether_0.etherType == 0x8100) && y.ether_1.valid && y.ether_1.etherType == 0x8100 && !y.ipv4_0.valid && !y.vlan_0.valid && y.vlan_1.valid && y.vlan_2.valid} + 
  {y:⊤|y.ether_0.valid && y.ether_0.etherType == 0x8100 && y.ether_1.valid && !y.ipv4_0.valid && y.vlan_0.valid && (!y.vlan_0.etherType == 0x0800) && y.vlan_1.valid && y.vlan_2.valid} + 
  {y:⊤|y.ether_0.valid && y.ether_0.etherType == 0x0800 && y.ether_1.valid && y.ether_1.etherType == 0x8100 && y.ipv4_0.valid && !y.vlan_0.valid && y.vlan_1.valid && y.vlan_2.valid && y.vlan_2.etherType == 0x0800} + 
  {y:⊤|y.ether_0.valid && y.ether_0.etherType == 0x8100 && y.ether_1.valid && y.ipv4_0.valid && y.vlan_0.valid && y.vlan_0.etherType == 0x0800 && y.vlan_1.valid && y.vlan_2.valid}
|}

let safe_roundtrip_string = {|
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
  header ether_0 : ether_t
  header ether_1 : ether_t
  header ipv4_0 : ipv4_t
  header ipv4_1 : ipv4_t
  header vlan_0 : vlan_t
  header vlan_1 : vlan_t

  ((((if(ether_0.valid) {
    remit(ether_0)
  } else {
    skip
  };
  if(vlan_0.valid) {
    remit(vlan_0)
  } else {
    skip
  };
  if(ipv4_0.valid) {
    remit(ipv4_0)
  } else {
    skip
  }) as (x:{y:⊤|y.ether_0.valid && y.ether_0.etherType == 0x8100 && !y.ether_1.valid && !y.ipv4_0.valid && !y.ipv4_1.valid && y.vlan_0.valid && (!y.vlan_0.etherType == 0x0800) && !y.vlan_1.valid && y.pkt_in.length == 0 && y.pkt_out.length == 0} + 
  {y:⊤|y.ether_0.valid && y.ether_0.etherType == 0x8100 && !y.ether_1.valid && y.ipv4_0.valid && !y.ipv4_1.valid && y.vlan_0.valid && (y.vlan_0.etherType == 0x0800) && !y.vlan_1.valid && y.pkt_in.length == 0 && y.pkt_out.length == 0}) ->
    {y:⊤|y.ether_0.valid && y.ether_0.etherType == 0x8100 && !y.ether_1.valid && !y.ipv4_0.valid && !y.ipv4_1.valid && y.vlan_0.valid && (!y.vlan_0.etherType == 0x0800) && !y.vlan_1.valid && y.pkt_in.length == 0 && y.pkt_out.length == 144 && y.pkt_out[96:112]==0x8100 && (!y.pkt_out[128:144] == 0x0800)} + 
    {y:⊤|y.ether_0.valid && y.ether_0.etherType == 0x8100 && !y.ether_1.valid && y.ipv4_0.valid && !y.ipv4_1.valid && y.vlan_0.valid && (y.vlan_0.etherType == 0x0800) && !y.vlan_1.valid && y.pkt_in.length == 0 && y.pkt_out.length == 304 && y.pkt_out[96:112]==0x8100 && y.pkt_out[128:144] == 0x0800});
  reset) as (x:{y:⊤|y.ether_0.valid && y.ether_0.etherType == 0x8100 && !y.ether_1.valid && !y.ipv4_0.valid && !y.ipv4_1.valid && y.vlan_0.valid && (!y.vlan_0.etherType == 0x0800) && !y.vlan_1.valid && y.pkt_in.length == 0 && y.pkt_out.length == 0} + 
  {y:⊤|y.ether_0.valid && y.ether_0.etherType == 0x8100 && !y.ether_1.valid && y.ipv4_0.valid && !y.ipv4_1.valid && y.vlan_0.valid && (y.vlan_0.etherType == 0x0800) && !y.vlan_1.valid && y.pkt_in.length == 0 && y.pkt_out.length == 0}) -> {y:⊤|!y.ether_0.valid && !y.ether_1.valid && !y.ipv4_0.valid && !y.ipv4_1.valid && !y.vlan_0.valid && !y.vlan_1.valid && y.pkt_in.length == 304 && y.pkt_out.length == 0 && y.pkt_in[96:112]==0x8100 && y.pkt_in[128:144] == 0x0800} + 
  {y:⊤|!y.ether_0.valid && !y.ether_1.valid && !y.ipv4_0.valid && !y.ipv4_1.valid && !y.vlan_0.valid && !y.vlan_1.valid && y.pkt_in.length == 144 && y.pkt_out.length == 0 && y.pkt_in[96:112]==0x8100 && (!y.pkt_in[128:144] == 0x0800)});
  (extract(ether_1));
  if(ether_1.etherType == 0x8100) {
    (extract(vlan_1);
    if(vlan_1.etherType == 0x0800) {
      extract(ipv4_1)
    } else {
      if(ipv4_0.valid) {
        add(ipv4_1);
        ipv4_1[0:160] := ipv4_0[0:160]
      } else {
        skip
        }
      })
  } else {
    if(ether_1.etherType == 0x0800) {
        extract(ipv4_1)
    } else {
      if(ipv4_0.valid) {
        add(ipv4_1);
        ipv4_1[0:160] := ipv4_0[0:160]
      } else {
        skip
      }
    };
    if(vlan_0.valid) {
      add(vlan_1);
      vlan_1[0:32] := vlan_0[0:32]
    } else {
      skip
    }
  }
|}

let safe_roundtrip_type_string = {|
(x:{y:⊤|y.ether_0.valid && y.ether_0.etherType == 0x8100 && !y.ether_1.valid && y.ether_0 == y.ether_1 && !y.ipv4_0.valid && !y.ipv4_1.valid && y.vlan_0.valid && (!y.vlan_0.etherType == 0x0800) && !y.vlan_1.valid && y.pkt_in.length == 0 && y.pkt_out.length == 0} + 
  {y:⊤|y.ether_0.valid && y.ether_0.etherType == 0x8100 && !y.ether_1.valid  && y.ether_0 == y.ether_1 && y.ipv4_0.valid && !y.ipv4_1.valid && y.vlan_0.valid && (y.vlan_0.etherType == 0x0800) && !y.vlan_1.valid && y.pkt_in.length == 0 && y.pkt_out.length == 0}) -> 
    {y:⊤|!y.ether_0.valid && y.ether_1.valid && y.ether_1.etherType == 0x8100 && !y.ipv4_0.valid && y.ipv4_1.valid && !y.vlan_0.valid && y.vlan_1.valid && y.vlan_1.etherType == 0x0800 && y.pkt_in.length == 0 && y.pkt_out.length == 0} + 
    {y:⊤|!y.ether_0.valid && y.ether_1.valid && y.ether_1.etherType == 0x8100 && !y.ipv4_0.valid && !y.ipv4_1.valid && !y.vlan_0.valid && y.vlan_1.valid && (!y.vlan_1.etherType == 0x0800) && y.pkt_in.length == 0 && y.pkt_out.length == 0}
|}

let safe_parser_after_reset_string =
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
  header ether_0 : ether_t
  header ether_1 : ether_t
  header ipv4_0 : ipv4_t
  header ipv4_1 : ipv4_t
  header vlan_0 : vlan_t
  header vlan_1 : vlan_t

  (extract(ether_1) as (x: ) -> );
  if(ether_1.etherType == 0x8100) {
    (extract(vlan_1);
    if(vlan_1.etherType == 0x0800) {
      extract(ipv4_1)
    } else {
      if(ipv4_0.valid) {
        add(ipv4_1);
        ipv4_1[0:160] := ipv4_0[0:160]
      } else {
        skip
        }
      })
  } else {
    if(ether_1.etherType == 0x0800) {
        extract(ipv4_1)
    } else {
      if(ipv4_0.valid) {
        add(ipv4_1);
        ipv4_1[0:160] := ipv4_0[0:160]
      } else {
        skip
      }
    };
    if(vlan_0.valid) {
      add(vlan_1);
      vlan_1[0:32] := vlan_0[0:32]
    } else {
      skip
    }
  }
|}  

let safe_parser_after_reset_type_string =
{|
(x:{y:⊤|!y.ether_0.valid && !y.ether_1.valid && !y.ipv4_0.valid && !y.ipv4_1.valid && !y.vlan_0.valid && !y.vlan_1.valid && y.pkt_in.length == 304 && y.pkt_out.length == 0 && y.pkt_in[96:112]==0x8100 && y.pkt_in[128:144] == 0x0800} + 
{y:⊤|!y.ether_0.valid && !y.ether_1.valid && !y.ipv4_0.valid && !y.ipv4_1.valid && !y.vlan_0.valid && !y.vlan_1.valid && y.pkt_in.length == 144 && y.pkt_out.length == 0 && y.pkt_in[96:112]==0x8100 && (!y.pkt_in[128:144] == 0x0800)}) -> 
  {y:⊤|!y.ether_0.valid && y.ether_1.valid && !y.ipv4_0.valid && y.ipv4_1.valid && !y.vlan_0.valid && y.vlan_1.valid && y.pkt_in.length == 0 && y.pkt_out.length == 0} + 
  {y:⊤|!y.ether_0.valid && y.ether_1.valid && !y.ipv4_0.valid && !y.ipv4_1.valid && !y.vlan_0.valid && y.vlan_1.valid && y.pkt_in.length == 0 && y.pkt_out.length == 0 }
|}  

let unsafe_roundtrip_string = {|
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
  header ether_0 : ether_t
  header ether_1 : ether_t
  header ipv4_0 : ipv4_t
  header ipv4_1 : ipv4_t
  header vlan_0 : vlan_t
  header vlan_1 : vlan_t
  ((((if(ether_0.valid) {
    remit(ether_0)
  } else {
    skip
  };
  if(vlan_0.valid) {
    remit(vlan_0)
  } else {
    skip
  };
  if(ipv4_0.valid) {
    remit(ipv4_0)
  } else {
    skip
  })  as (x:{y:⊤|y.ether_0.valid && y.ether_0.etherType == 0x8100 && !y.ether_1.valid && !y.ipv4_0.valid && !y.ipv4_1.valid && y.vlan_0.valid && (!y.vlan_0.etherType == 0x0800) && !y.vlan_1.valid && y.pkt_in.length == 0 && y.pkt_out.length == 0} + 
  {y:⊤|y.ether_0.valid && y.ether_0.etherType == 0x8100 && !y.ether_1.valid && y.ipv4_0.valid && !y.ipv4_1.valid && y.vlan_0.valid && (y.vlan_0.etherType == 0x0800) && !y.vlan_1.valid && y.pkt_in.length == 0 && y.pkt_out.length == 0}) ->
    {y:⊤|y.ether_0.valid && y.ether_0.etherType == 0x8100 && !y.ether_1.valid && !y.ipv4_0.valid && !y.ipv4_1.valid && y.vlan_0.valid && (!y.vlan_0.etherType == 0x0800) && !y.vlan_1.valid && y.pkt_in.length == 0 && y.pkt_out.length == 144 && y.pkt_out[96:112]==0x8100 && (!y.pkt_out[128:144] == 0x0800)} + 
    {y:⊤|y.ether_0.valid && y.ether_0.etherType == 0x8100 && !y.ether_1.valid && y.ipv4_0.valid && !y.ipv4_1.valid && y.vlan_0.valid && (y.vlan_0.etherType == 0x0800) && !y.vlan_1.valid && y.pkt_in.length == 0 && y.pkt_out.length == 304 && y.pkt_out[96:112]==0x8100 && y.pkt_out[128:144] == 0x0800});
  reset) as (x:{y:⊤|y.ether_0.valid && y.ether_0.etherType == 0x8100 && !y.ether_1.valid && !y.ipv4_0.valid && !y.ipv4_1.valid && y.vlan_0.valid && (!y.vlan_0.etherType == 0x0800) && !y.vlan_1.valid && y.pkt_in.length == 0 && y.pkt_out.length == 0} + 
  {y:⊤|y.ether_0.valid && y.ether_0.etherType == 0x8100 && !y.ether_1.valid && y.ipv4_0.valid && !y.ipv4_1.valid && y.vlan_0.valid && (y.vlan_0.etherType == 0x0800) && !y.vlan_1.valid && y.pkt_in.length == 0 && y.pkt_out.length == 0}) -> {y:⊤|!y.ether_0.valid && !y.ether_1.valid && !y.ipv4_0.valid && !y.ipv4_1.valid && !y.vlan_0.valid && !y.vlan_1.valid && y.pkt_in.length == 304 && y.pkt_out.length == 0 && y.pkt_in[96:112]==0x8100 && y.pkt_in[128:144] == 0x0800} + 
  {y:⊤|!y.ether_0.valid && !y.ether_1.valid && !y.ipv4_0.valid && !y.ipv4_1.valid && !y.vlan_0.valid && !y.vlan_1.valid && y.pkt_in.length == 144 && y.pkt_out.length == 0 && y.pkt_in[96:112]==0x8100 && (!y.pkt_in[128:144] == 0x0800)});
  extract(ether_1);
  if(ether_1.etherType == 0x8100) {
    extract(vlan_1);
    if(vlan_1.etherType == 0x0800) {
      extract(ipv4_1)
    } else {
      if(ipv4_0.valid) {
        add(ipv4_1);
        ipv4_1[0:160] := ipv4_0[0:160]
      } else {
        skip
      }
    }
  } else {
    if(ether_1.etherType == 0x0800) {
      extract(ipv4_1)
    } else {
      if(ipv4_0.valid) {
        add(ipv4_1);
        ipv4_1[0:160] := ipv4_0[0:160]
      } else {
        skip
      }
    };
    if(vlan_0.valid) {
      add(vlan_1);
      vlan_1[0:32] := vlan_0[0:32]
    } else {
      skip
    }
  }
|}

let unsafe_roundtrip_type_string = {|
(x:{y:⊤|y.ether_0.valid && (!y.ether_0.etherType == 0x0800) && (!y.ether_0.etherType == 0x8100) && !y.ether_1.valid && !y.ipv4_0.valid && !y.ipv4_1.valid && y.vlan_0.valid && !y.vlan_1.valid && y.pkt_in.length == 0 && y.pkt_out.length == 0} + 
{y:⊤|y.ether_0.valid && y.ether_0.etherType == 0x8100 && !y.ether_1.valid && !y.ipv4_0.valid && !y.ipv4_1.valid && y.vlan_0.valid && (!y.vlan_0.etherType == 0x0800) && !y.vlan_1.valid && y.pkt_in.length == 0 && y.pkt_out.length == 0} +
{y:⊤|y.ether_0.valid && y.ether_0.etherType == 0x0800 && !y.ether_1.valid && y.ipv4_0.valid && !y.ipv4_1.valid && y.vlan_0.valid && y.vlan_0.etherType == 0x0800 && !y.vlan_1.valid && y.pkt_in.length == 0 && y.pkt_out.length == 0} +
{y:⊤|y.ether_0.valid && y.ether_0.etherType == 0x8100 && !y.ether_1.valid  && y.ipv4_0.valid && !y.ipv4_1.valid && y.vlan_0.valid && y.vlan_0.etherType == 0x0800 && !y.vlan_1.valid && y.pkt_in.length == 0 && y.pkt_out.length == 0}) ->
  {y:⊤|!y.ether_0.valid && y.ether_1.valid && y.ether_1.etherType == 0x8100 && !y.ipv4_0.valid && y.ipv4_1.valid && !y.vlan_0.valid && y.vlan_1.valid && y.vlan_1.etherType == 0x0800 && y.pkt_in.length == 0 && y.pkt_out.length == 0} + 
  {y:⊤|!y.ether_0.valid && y.ether_1.valid && y.ether_1.etherType == 0x8100 && !y.ipv4_0.valid && !y.ipv4_1.valid && !y.vlan_0.valid && y.vlan_1.valid && (!y.vlan_1.etherType == 0x0800) && y.pkt_in.length == 0 && y.pkt_out.length == 0}
|}

let test_safe_parser () = 
  let program = Parsing.parse_program safe_parser_string in
  Logs.debug (fun m -> m "%a" Pretty.pp_command program.command);
  let header_table = HeaderTable.of_decls program.declarations in
  let ty = Parsing.parse_type safe_parser_type_string header_table  in 
  test_typecheck_ssa header_table program.command ty

let test_safe_ingress () = 
  let program = Parsing.parse_program safe_ingress_string in
  Logs.debug (fun m -> m "%a" Pretty.pp_command program.command);
  let header_table = HeaderTable.of_decls program.declarations in
  let ty = Parsing.parse_type safe_ingress_type_string header_table  in 
  test_typecheck_ssa header_table program.command ty

let test_safe_roundtrip () = 
  let program = Parsing.parse_program safe_roundtrip_string in
  Logs.debug (fun m -> m "%a" Pretty.pp_command program.command);
  let header_table = HeaderTable.of_decls program.declarations in
  let ty = Parsing.parse_type safe_roundtrip_type_string header_table  in 
  test_typecheck_ssa header_table program.command ty

let test_safe_parser_after_reset () = 
  let program = Parsing.parse_program safe_parser_after_reset_string in
  Logs.debug (fun m -> m "%a" Pretty.pp_command program.command);
  let header_table = HeaderTable.of_decls program.declarations in
  let ty = Parsing.parse_type safe_parser_after_reset_type_string header_table  in 
  test_typecheck_ssa header_table program.command ty
 
let test_unsafe_roundtrip () = 
  let program = Parsing.parse_program unsafe_roundtrip_string in
  Logs.debug (fun m -> m "%a" Pretty.pp_command program.command);
  let header_table = HeaderTable.of_decls program.declarations in
  let ty = Parsing.parse_type unsafe_roundtrip_type_string header_table  in 
  test_typecheck_ssa header_table program.command ty

let test_set =
  [
  test_case "Safe parser" `Quick test_safe_parser;
  test_case "Safe ingress" `Quick test_safe_ingress;
  test_case "Safe roundtrip" `Quick test_safe_roundtrip;
  test_case "Safe parser after reset" `Quick test_safe_parser_after_reset;
  test_case "Unsafe roundtrip" `Quick test_unsafe_roundtrip;
]
