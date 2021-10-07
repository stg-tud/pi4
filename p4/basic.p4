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

// @pi4("(x:ε) → (ethernet + Σy:ethernet.ipv4 + Σy:ethernet.vlan + Σy:ethernet.(Σz:vlan.ipv4))")
@pi4("(x:ε) → ethernet~")
// @pi4("(x:{y:ε|y.pkt_in.length=320}) → ethernet~")
// @pi4("(x:{y:ε|y.pkt_in.length=320}) → (ethernet + Σy:ethernet.ipv4 + Σy:ethernet.vlan + Σy:ethernet.(Σz:vlan.ipv4))")
parser MyParser(packet_in packet,
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

control MyIngress(inout headers hdr,
                  inout metadata meta,
                  inout standard_metadata_t standard_metadata) {
    apply {
        standard_metadata.egress_spec = 9;
    }
}

control MyEgress(inout headers hdr,
                 inout metadata meta,
                 inout standard_metadata_t standard_metadata) {
    apply { }
}

control MyDeparser(packet_out packet, in headers hdr) {
    apply { }
}

V1Switch(MyParser(), MyChecksum(), MyIngress(), MyEgress(), MyChecksum(), MyDeparser()) main;
