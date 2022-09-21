# Evaluation

## Experiments

### 1. Performance Optimizations

In this experiment, we evaluate the effect of disabling the includes cache and the substitution inlining

```
hyperfine \
  -L program p4tut_basic_tunnel,p4tut_basic,p4tut_ecn,p4tut_load_balance,p4tut_multicast,p4tut_qos,roundtripping-safe,vlan_decap \
  --export-json ./evaluation/01/header_validty_small_programs.json \
  --runs 2 \
  'dune exec bin/main.exe -- -i ./p4/includes ./evaluation/p4/01/{program}.p4' \
  'dune exec bin/main.exe -- -i ./p4/includes -disable-cache ./evaluation/p4/01/{program}.p4' \
  'dune exec bin/main.exe -- -i ./p4/includes -disable-inlining ./evaluation/p4/01/{program}.p4' \
  'dune exec bin/main.exe -- -i ./p4/includes -disable-cache -disable-inlining ./evaluation/p4/01/{program}.p4' 
```

```
hyperfine \
  --export-json ./evaluation/01/measurements_fabric.json \
  --runs 2 \
  'dune exec bin/main.exe -- -i ./p4/includes -i ./evaluation/p4/01/fabric/include ./evaluation/p4/01/fabric/fabric.p4' \
  'dune exec bin/main.exe -- -i ./p4/includes -i ./evaluation/p4/01/fabric/include -disable-cache ./evaluation/p4/01/fabric/fabric.p4' \
  'dune exec bin/main.exe -- -i ./p4/includes -i ./evaluation/p4/01/fabric/include -disable-inlining ./evaluation/p4/01/fabric/fabric.p4' \
  'dune exec bin/main.exe -- -i ./p4/includes -i ./evaluation/p4/01/fabric/include -disable-cache -disable-inlining ./evaluation/p4/01/fabric/fabric.p4' 
```

```
hyperfine \
  --export-json ./evaluation/01/measurements_ngsdn.json \
  --runs 1\
  'dune exec bin/main.exe -- -m 704 -ir -typ ./examples/ngsdn.pi4_type ./examples/ngsdn.pi4'
```

### 2. Effect of MTU

In this experiment, we vary the MTU from 1500 to 12000 bits in steps of 1500

```
hyperfine \
  -P maxlen 1500 12000 -D 1500 \
  --runs 2 \
  --export-json ./evaluation/02/measurements_small_programs.json \
  'dune exec bin/main.exe -- -i ./p4/includes -m {maxlen} ./evaluation/p4/01/p4tut_basic_tunnel.p4' \
  'dune exec bin/main.exe -- -i ./p4/includes -m {maxlen} ./evaluation/p4/01/p4tut_basic.p4' \
  'dune exec bin/main.exe -- -i ./p4/includes -m {maxlen} ./evaluation/p4/01/p4tut_ecn.p4' \
  'dune exec bin/main.exe -- -i ./p4/includes -m {maxlen} ./evaluation/p4/01/p4tut_load_balance.p4' \
  'dune exec bin/main.exe -- -i ./p4/includes -m {maxlen} ./evaluation/p4/01/p4tut_multicast.p4' \
  'dune exec bin/main.exe -- -i ./p4/includes -m {maxlen} ./evaluation/p4/01/p4tut_qos.p4' \
  'dune exec bin/main.exe -- -i ./p4/includes -m {maxlen} ./evaluation/p4/01/roundtripping-safe.p4' \
  'dune exec bin/main.exe -- -i ./p4/includes -m {maxlen} ./evaluation/p4/01/vlan_decap.p4'
```

```
hyperfine \
  -P maxlen 1500 12000 -D 1500 \
  --runs 2 \
  --export-json ./evaluation/02/measurements_fabric.json \
  'dune exec bin/main.exe -- -i ./p4/includes -i ./evaluation/p4/01/fabric/include -m {maxlen} ./evaluation/p4/01/fabric/fabric.p4'
```
### 3. Modular Verification

#### 3.1 NG-SDN

```
hyperfine \
  --export-json ./evaluation/03/ngsdn_parser.json \
  --runs 2\
  'dune exec bin/main.exe -- -m 1500 -ir -typ ./examples/ngsdn_parser.pi4_type ./examples/ngsdn_parser.pi4'
```

```
hyperfine \
  --export-json ./evaluation/03/ngsdn_ingress.json \
  --runs 2\
  'dune exec bin/main.exe -- -m 1500 -ir -typ ./examples/ngsdn_ingress.pi4_type ./examples/ngsdn_ingress.pi4'
```

```
hyperfine \
  --export-json ./evaluation/03/ngsdn_egress.json \
  --runs 2\
  'dune exec bin/main.exe -- -m 1500 -ir -typ ./examples/ngsdn_egress.pi4_type ./examples/ngsdn_egress.pi4'
```

```
hyperfine \
  --export-json ./evaluation/03/ngsdn_deparser.json \
  --runs 2\
  'dune exec bin/main.exe -- -m 1500 -ir -typ ./examples/ngsdn.pi4_type ./examples/ngsdn_deparser.pi4'
```

```
hyperfine \
  --export-json ./evaluation/03/ngsdn_ascribed.json \
  --runs 2\
  'dune exec bin/main.exe -- -m 1500 -ir -typ ./examples/ngsdn.pi4_type ./examples/ngsdn_ascribed.pi4'
```

```
hyperfine \
  --export-json ./evaluation/03/ngsdn.json \
  --runs 5\
  'dune exec bin/main.exe -- -m 1500 -ir -typ ./examples/ngsdn_parser.pi4_type ./examples/ngsdn_parser.pi4' \
  'dune exec bin/main.exe -- -m 1500 -ir -typ ./examples/ngsdn_ingress.pi4_type ./examples/ngsdn_ingress.pi4' \
  'dune exec bin/main.exe -- -m 1500 -ir -typ ./examples/ngsdn_egress.pi4_type ./examples/ngsdn_egress.pi4' \
  'dune exec bin/main.exe -- -m 1500 -ir -typ ./examples/ngsdn.pi4_type ./examples/ngsdn_deparser.pi4' \
  'dune exec bin/main.exe -- -m 1500 -ir -typ ./examples/ngsdn.pi4_type ./examples/ngsdn_ascribed.pi4'
```

#### 3.2 Fabric

```
hyperfine \
  --export-json ./evaluation/03/fabric_parser.json \
  --runs 5\
  'dune exec bin/main.exe -- -m 1500 -ir -typ ./examples/fabric_parser.pi4_type ./examples/fabric_parser.pi4'
```

```
hyperfine \
  --export-json ./evaluation/03/fabric_ingress.json \
  --runs 5\
  'dune exec bin/main.exe -- -m 1500 -ir -typ ./examples/fabric_ingress.pi4_type ./examples/fabric_ingress.pi4'
```

```
hyperfine \
  --export-json ./evaluation/03/fabric_ingress_filtering.json \
  --runs 5\
  'dune exec bin/main.exe -- -m 1500 -ir -typ ./examples/fabric_ingress_filtering.pi4_type ./examples/fabric_ingress_filtering.pi4'
```

```
hyperfine \
  --export-json ./evaluation/03/fabric_deparser.json \
  --runs 1\
  'dune exec bin/main.exe -- -m 1500 -ir -typ ./examples/fabric_deparser.pi4_type ./examples/fabric_deparser.pi4'
```

```
hyperfine \
  --export-json ./evaluation/03/fabric_complete.json \
  --runs 1\
  'dune exec bin/main.exe -- -m 1500 -ir -typ ./examples/fabric.pi4_type ./examples/fabric.pi4'
```

<!-- ### 3. Full pipeline of fabric.p4
```
hyperfine \
  --runs 1 \
  --output inherit \
  --export-json ./evaluation/03.json \
  'dune exec bin/main.exe -- -i ./p4/includes -i ./evaluation/p4/01/fabric/include ./evaluation/p4/01/fabric/fabric.p4'
``` -->
