#include <core.p4>
#include <v1model.p4>

header ethernet_t {
    bit<48> dstAddr;
    bit<48> srcAddr;
    bit<16> etherType;
}

header ipv4_t {
    bit<4> version; 
    bit<4> ihl; 
    bit<8> tos; 
    bit<16> len; 
    bit<16> id; 
    bit<3> flags; 
    bit<13> frag; 
    bit<8> ttl; 
    bit<8> proto; 
    bit<16> chksum; 
    bit<32> src; 
    bit<32> dst;
}

header vlan_t {
    bit<3> prio; 
    bit<1> id; 
    bit<12> vlan; 
    bit<16> etherType;
}

struct metadata { }
struct headers { 
    ethernet_t ethernet;
    ipv4_t ipv4;
    vlan_t vlan;
}

@pi4("(Parser;Ingress;((Deparser;reset;Parser) as (x:{z:ethernet~| z.ethernet.etherType == 0x8100 && z.vlan.valid && (z.ipv4.valid => z.vlan.etherType == 0x0800) && ((!z.ipv4.valid) => z.vlan.etherType != 0x0800) && z.pkt_out.length == 0 && z.pkt_in.length > 0}) -> {y:⊤| x =i= y })) as (x:{y:ε|y.pkt_out.length == 0 && y.pkt_in.length > 304}) -> ⊤")
parser Parser(packet_in packet,
                out headers hdr,
                inout metadata meta,
                inout standard_metadata_t standard_metadata) {
    state start {
        packet.extract(hdr.ethernet);
        transition select(hdr.ethernet.etherType) {
            0x0800: parse_ipv4;
            0x8100: parse_vlan;
            default: accept;
        }
    }

    state parse_vlan {
        packet.extract(hdr.vlan);
        transition select(hdr.vlan.etherType) {
            0x0800: parse_ipv4;
            default: accept;
        }
    }

    state parse_ipv4 {
        packet.extract(hdr.ipv4);
        transition accept;
    }
}

control MyChecksum(inout headers hdr, inout metadata meta) {
    apply { }
}

control Ingress(inout headers hdr,
                  inout metadata meta,
                  inout standard_metadata_t standard_metadata) {
    apply {
        if(!hdr.vlan.isValid()) {
          hdr.vlan.setValid();
          if(hdr.ipv4.isValid()) {
            hdr.vlan.etherType = 0x0800;
          }
        }
    }
}

control MyEgress(inout headers hdr,
                 inout metadata meta,
                 inout standard_metadata_t standard_metadata) {
    apply { }
}

control Deparser(packet_out packet, in headers hdr) {
    apply { 
      packet.emit(hdr.ethernet);
      packet.emit(hdr.vlan);
      packet.emit(hdr.ipv4);
    }
}

V1Switch(MyParser(), MyChecksum(), MyIngress(), MyEgress(), MyChecksum(), MyDeparser()) main;
