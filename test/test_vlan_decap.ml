open Alcotest

module TestConfig = struct
  let verbose = true
  let maxlen = 12000
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
      header_type MyIngress_ipv4_lpm_table_t {
        act:1;
        ipv4_forward_port:9;
        ipv4_forward_dstAddr:48;
        ipv4_dstAddr_key:32;
      } 
      header_type standard_metadata_t {
        ingress_port:9;
        egress_spec:9;
        egress_port:9;
        instance_type:32;
        packet_length:32;
        enq_timestamp:32;
        enq_qdepth:19;
        deq_timedelta:32;
        deq_qdepth:19;
        ingress_global_timestamp:48;
        egress_global_timestamp:48;
        mcast_grp:16;
        egress_rid:16;
        checksum_error:1;
        priority:3;
      }

      header ethernet : ether_t
      header ipv4 : ipv4_t
      header vlan : vlan_t
      header MyIngress_ipv4_lpm_table : MyIngress_ipv4_lpm_table_t
      header standard_metadata: standard_metadata_t

      extract(ethernet);
      if(ethernet[96:112] == 0b1000000100000000) {
        extract(vlan);
        if(vlan[16:32] == 0b0000100000000000) {
          extract(ipv4)
        }
      } else {
        if(ethernet[96:112] == 0b0000100000000000) {
          extract(ipv4)
        }
      };
      if(ipv4.valid) {
        add(MyIngress_ipv4_lpm_table);
        if(MyIngress_ipv4_lpm_table[58:90] == ipv4[128:160]) {
          if(MyIngress_ipv4_lpm_table[0:1] == 0b0) {
            standard_metadata[9:18] := MyIngress_ipv4_lpm_table[1:10];
            ethernet[48:96] := ethernet[0:48];
            ethernet[0:48] := MyIngress_ipv4_lpm_table[10:58];
            ipv4[64:72] := (ipv4[64:72] - 0b00000001)
          }
        }
      };
      if(vlan.valid) {
        ethernet[96:112] := vlan[16:32];
        remove(vlan)
      }
    |}
  in
  let typ = "(x:{y:standard_metadata|y.pkt_in.length > 304}) → {z:⊤|¬z.vlan.valid}" in
  Test.check_program Test.typecheck program typ

let test_set = [ test_case "Complete program typechecks" `Quick test_complete ]
