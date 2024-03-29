/*
 * Copyright 2017-present Open Networking Foundation
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <core.p4>
#include <v1model.p4>

#include "../header.p4"

control Filtering (inout headers hdr,
                   inout metadata meta,
                   inout standard_metadata_t standard_metadata) {

    /*
     * Ingress Port VLAN Table.
     *
     * Filter packets based on ingress port and VLAN tag.
     */
    // direct_counter(CounterType.packets_and_bytes) ingress_port_vlan_counter;

    action deny() {
        // Packet from unconfigured port. Skip forwarding and next block.
        // Do ACL table in case we want to punt to cpu.
        meta.skip_forwarding = _TRUE;
        meta.skip_next = _TRUE;
        meta.port_type = PORT_TYPE_UNKNOWN;
        // ingress_port_vlan_counter.count();
    }

    action permit(port_type_t port_type) {
        // Allow packet as is.
        meta.port_type = port_type;
        // ingress_port_vlan_counter.count();
    }

    action permit_with_internal_vlan(vlan_id_t vlan_id, port_type_t port_type) {
        meta.vlan_id = vlan_id;
        // permit(port_type);
        meta.port_type = port_type;
    }

    // FIXME: remove the use of ternary match on inner VLAN.
    // Use multi-table approach to remove ternary matching
    table ingress_port_vlan {
        key = {
            standard_metadata.ingress_port : exact @name("ig_port");
            hdr.vlan_tag.isValid()         : exact @name("vlan_is_valid");
            hdr.vlan_tag.vlan_id           : ternary @name("vlan_id");
#ifdef WITH_DOUBLE_VLAN_TERMINATION
            hdr.inner_vlan_tag.vlan_id     : ternary @name("inner_vlan_id");
#endif // WITH_DOUBLE_VLAN_TERMINATION
        }
        actions = {
            deny();
            permit();
            permit_with_internal_vlan();
        }
        const default_action = deny();
        // counters = ingress_port_vlan_counter;
        size = PORT_VLAN_TABLE_SIZE;
    }

    /*
     * Forwarding Classifier.
     *
     * Set which type of forwarding behavior to execute in the next control block.
     * There are six types of tables in Forwarding control block:
     * - Bridging: default forwarding type
     * - MPLS: destination mac address is the router mac and ethernet type is
     *   MPLS(0x8847)
     * - IP Multicast: destination mac address is multicast address and ethernet
     *   type is IP(0x0800 or 0x86dd)
     * - IP Unicast: destination mac address is router mac and ethernet type is
     *   IP(0x0800 or 0x86dd)
     */
    // direct_counter(CounterType.packets_and_bytes) fwd_classifier_counter;

    action set_forwarding_type(fwd_type_t fwd_type) {
        meta.fwd_type = fwd_type;
        // fwd_classifier_counter.count();
    }

    table fwd_classifier {
        key = {
            standard_metadata.ingress_port : exact @name("ig_port");
            hdr.ethernet.dst_addr          : ternary @name("eth_dst");
            hdr.eth_type.value             : ternary @name("eth_type");
            meta.ip_eth_type    : exact @name("ip_eth_type");
        }
        actions = {
            set_forwarding_type;
        }
        const default_action = set_forwarding_type(FWD_BRIDGING);
        // counters = fwd_classifier_counter;
        size = FWD_CLASSIFIER_TABLE_SIZE;
    }

    apply {
        // Initialize lookup metadata. Packets without a VLAN header will be
        // treated as belonging to a default VLAN ID (see parser).
        if (hdr.vlan_tag.isValid()) {
            meta.vlan_id = hdr.vlan_tag.vlan_id;
            meta.vlan_pri = hdr.vlan_tag.pri;
            meta.vlan_cfi = hdr.vlan_tag.cfi;
        }
        #ifdef WITH_DOUBLE_VLAN_TERMINATION
        if (hdr.inner_vlan_tag.isValid()) {
            meta.inner_vlan_id = hdr.inner_vlan_tag.vlan_id;
            meta.inner_vlan_pri = hdr.inner_vlan_tag.pri;
            meta.inner_vlan_cfi = hdr.inner_vlan_tag.cfi;
        }
        #endif // WITH_DOUBLE_VLAN_TERMINATION
        if (!hdr.mpls.isValid()) {
            // Packets with a valid MPLS header will have
            // meta.mpls_ttl set to the packet's MPLS ttl value (see
            // parser). In any case, if we are forwarding via MPLS, ttl will be
            // decremented in egress.
            meta.mpls_ttl = 65;
        }

        if (hdr.vlan_tag.isValid()) {
            ingress_port_vlan.apply();
        }
        fwd_classifier.apply();
    }
}
