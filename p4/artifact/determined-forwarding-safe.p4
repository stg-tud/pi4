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

struct metadata { }
struct headers { 
    ethernet_t ethernet;
    ipv4_t ipv4;
}

parser MyParser(packet_in packet,
                out headers hdr,
                inout metadata meta,
                inout standard_metadata_t standard_metadata) {
    state start {
        packet.extract(hdr.ethernet);
        transition select(hdr.ethernet.etherType) {
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

@pi4("(x:{y:⊤|y.ethernet.valid ∧ y.ipv4.valid ∧ y.standard_metadata.valid}) -> {y:⊤|y.ethernet.valid ∧ y.ipv4.valid  ∧ y.standard_metadata.valid ∧ !(y.standard_metadata.egress_spec = 0)}")
control Ingress(inout headers hdr,
                  inout metadata meta,
                  inout standard_metadata_t standard_metadata) {
    apply {
        if(hdr.ipv4.isValid()) {
          if(hdr.ipv4.dst == 0x0a0a0a0a) {
            standard_metadata.egress_spec = 0x1ff;
          } else {
            standard_metadata.egress_spec = 0x1;
          }
        }
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
