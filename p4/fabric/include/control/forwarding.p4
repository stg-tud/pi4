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

#include "../define.p4"
#include "../header.p4"


control Forwarding (inout headers hdr,
                    inout metadata meta,
                    inout standard_metadata_t standard_metadata) {

    action set_next_id_bridging(next_id_t next_id) {
        meta.next_id = next_id;
    }

    // FIXME: using ternary for eth_dst prevents our ability to scale in
    //  bridging heavy environments. Do we really need ternary? Can we come up
    //  with a multi-table/algorithmic approach?
    table bridging {
        key = {
            meta.vlan_id: exact @name("vlan_id");
            hdr.ethernet.dst_addr: ternary @name("eth_dst");
        }
        actions = {
            set_next_id_bridging;
            @defaultonly NoAction; 
        }
        const default_action = NoAction();
        size = BRIDGING_TABLE_SIZE;
    }

    /*
     * MPLS Table.
     */
    action pop_mpls_and_next(next_id_t next_id) {
        meta.mpls_label = 0;
        meta.next_id = next_id;
    }

    table mpls {
        key = {
            meta.mpls_label: exact @name("mpls_label");
        }
        actions = {
            pop_mpls_and_next;
            @defaultonly NoAction;
        }
        const default_action = NoAction();
        size = MPLS_TABLE_SIZE;
    }

    /*
     * IPv4 Routing Table.
     */

    action set_next_id_routing_v4(next_id_t next_id) {
        meta.next_id = next_id;
    }

    action nop_routing_v4() {
    }
    
    table routing_v4 {
        key = {
            meta.ipv4_dst_addr: lpm @name("ipv4_dst");
        }
        actions = {
            set_next_id_routing_v4;
            nop_routing_v4;
            @defaultonly NoAction;
        }
        default_action = NoAction();
        size = ROUTING_V4_TABLE_SIZE;
    }

#ifdef WITH_IPV6
    action set_next_id_routing_v6(next_id_t next_id) {
        meta.next_id = next_id;
    }

    table routing_v6 {
        key = {
            hdr.ipv6.dst_addr: lpm @name("ipv6_dst");
        }
        actions = {
            set_next_id_routing_v6;
            @defaultonly NoAction;
        }
        const default_action = NoAction();
        size = ROUTING_V6_TABLE_SIZE;
    }
#endif // WITH_IPV6

    apply {
        if (meta.fwd_type == FWD_BRIDGING) bridging.apply();
        else if (meta.fwd_type == FWD_MPLS) mpls.apply();
        else if (meta.fwd_type == FWD_IPV4_UNICAST) routing_v4.apply();
#ifdef WITH_IPV6
        else if (meta.fwd_type == FWD_IPV6_UNICAST && hdr.ipv6.isValid()) routing_v6.apply();
#endif // WITH_IPV6
    }
}
