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

header ipv6_t {
    bit<4> version;
    bit<8> trafficClass;
    bit<20> flowLable;
    bit<16> payloadLength;
    bit<8> nextHeader;
    bit<8> hopLimit;
    bit<128> srcAddr;
    bit<128> dstAddr; 
}

struct metadata { }
struct headers { 
    ethernet_t ethernet;
    ipv4_t ipv4;
    ipv6_t ipv6;
}

@pi4("(x:{y:ε|y.pkt_in.length > 432}) -> {y:⊤|!(y.ipv4.valid && y.ipv6.valid)}")
parser MyParser(packet_in packet,
                out headers hdr,
                inout metadata meta,
                inout standard_metadata_t standard_metadata) {
    state start {
        packet.extract(hdr.ethernet);
        transition select(hdr.ethernet.etherType) {
            0x0800: parse_ipv4;
            0x86dd: parse_ipv6;
            default: accept;
        }
    }

    state parse_ipv4 {
        packet.extract(hdr.ipv4);
        transition accept;
    }

    state parse_ipv6 {
        packet.extract(hdr.ipv6);
        transition accept;
    }
}

@pi4("(x:ethernet + {y:⊤|y.ethernet.valid ∧ y.ipv4.valid ∧ !y.ipv6.valid} + {y:⊤|y.ethernet.valid ∧ !y.ipv4.valid ∧ y.ipv6.valid}) -> {y:⊤|!(y.ipv4.valid && y.ipv6.valid)}")
control Ingress(inout headers hdr,
                  inout metadata meta,
                  inout standard_metadata_t standard_metadata) {
    apply {
      hdr.ipv6.setValid();
      hdr.ethernet.etherType = 0x86dd;
    }
}

control MyChecksum(inout headers hdr, inout metadata meta) {
    apply { }
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
