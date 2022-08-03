open Alcotest

module TestConfig = struct
  let verbose = true
  let maxlen = ref(12000)
end

module Test = Test_utils.TestRunner (TestConfig)

let test_complete () =
  let program =
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

      add(forward_table);
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
  in
  let typ = "(x:{y:ε|y.pkt_in.length > 304}) → {z:⊤|¬z.vlan.valid}" in
  Test.check_program Test.typecheck program typ

let test_set = [ test_case "Complete program typechecks" `Quick test_complete ]
