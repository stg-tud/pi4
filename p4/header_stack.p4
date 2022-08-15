#include <core.p4>
#include <v1model.p4>

header ethernet_t {
    bit<48> dstAddr;
    bit<48> srcAddr;
    bit<16> etherType;
}

header int_value_t {
    bit<1>  bos;
    bit<31> val;
}

struct metadata { }
struct headers { 
    ethernet_t      ethernet;
    int_value_t[4] int_val;
}
@pi4("(MyParser) as (x:{y:standard_metadata|y.pkt_in.length > 304}) -> ethernet~")
parser MyParser(packet_in packet,
                out headers hdr,
                inout metadata meta,
                inout standard_metadata_t standard_metadata) {
    state start {
        packet.extract(hdr.ethernet);
        transition select(hdr.ethernet.etherType) {
            16w0x1234: parse_int_val;
            default: accept;
        }
    }

    state parse_int_val {
        packet.extract(hdr.int_val.next);
        transition select(hdr.int_val.last.bos) {
            1w0: parse_int_val;
            default: accept;
        }
    }
}

control MyChecksum(inout headers hdr, inout metadata meta) {
    apply { }
}

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
    apply { }
}

V1Switch(MyParser(), MyChecksum(), MyIngress(), MyEgress(), MyChecksum(), MyDeparser()) main;
