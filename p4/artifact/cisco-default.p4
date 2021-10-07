#include <core.p4>
#include <v1model.p4>

header ethernet_t {
    bit<48> dstAddr;
    bit<48> srcAddr;
    bit<16> etherType;
}

header vlan_t {
    bit<3> prio; 
    bit<1> id; 
    bit<12> vid; 
    bit<16> etherType;
}

struct headers { 
    ethernet_t ethernet;
    vlan_t vlan;
}

parser MyParser(packet_in packet,
                out headers hdr,
                inout metadata meta,
                inout standard_metadata_t standard_metadata) {
    state start {
        packet.extract(hdr.ethernet);
        transition select(hdr.ethernet.etherType) {
            0x8100: parse_vlan;
            default: accept;
        }
    }

    state parse_vlan {
        packet.extract(hdr.vlan);
        transition accept;
    }
}

control MyChecksum(inout headers hdr, inout metadata meta) {
    apply { }
}

@pi4("(x:{y:⊤|y.ethernet.valid ∧ y.vlan.valid ∧ y.standard_metadata.valid} -> {y:⊤|y.ethernet.valid ∧ y.vlan.valid ∧ y.standard_metadata.valid ∧ y.vlan.vid = x.vlan.vid}")
control MyIngress(inout headers hdr,
                  inout metadata meta,
                  inout standard_metadata_t standard_metadata) {
    apply { }
}

control MyEgress(inout headers hdr,
                 inout metadata meta,
                 inout standard_metadata_t standard_metadata) {
    apply { }
}

control MyDeparser(packet_out packet, in headers hdr) {
    apply { 
      packet.emit(hdr.ethernet);
      packet.emit(hdr.vlan);
    }
}

V1Switch(MyParser(), MyChecksum(), MyIngress(), MyEgress(), MyChecksum(), MyDeparser()) main;
