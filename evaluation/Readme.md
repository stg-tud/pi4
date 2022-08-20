# Evaluation

## Experiments

### 1. Performance Optimizations

In this experiment, we evaluate the effect of disabling the includes cache and the substitution inlining

```
hyperfine \
  -L program p4tut_basic_tunnel,p4tut_basic,p4tut_ecn,p4tut_load_balance,p4tut_multicast,p4tut_qos,roundtripping-safe,vlan_decap \
  --export-json ./01/measurements.json \
  --output inherit \
  './pi4.exe -i ./p4/includes ./01/p4/{program}.p4 > ./01/{program}.log 2>&1' \
  './pi4.exe -i ./p4/includes -disable-cache ./01/p4/{program}.p4 > ./01/{program}.log 2>&1' \
  './pi4.exe -i ./p4/includes -disable-inlining ./01/p4/{program}.p4 > ./01/{program}.log 2>&1' \
  './pi4.exe -i ./p4/includes -disable-cache -disable-inlining ./01/p4/{program}.p4 > ./01/{program}.log 2>&1' 
```

```
hyperfine \
  --export-json ./01/measurements_fabric.json \
  --output inherit \
  './pi4.exe -i ./p4/includes -i ./01/p4/fabric/include ./01/p4/fabric/fabric.p4 > ./01/fabric.log 2>&1' \
  './pi4.exe -i ./p4/includes -i ./01/p4/fabric/include -disable-cache ./01/p4/fabric/fabric.p4 > ./01/fabric.log 2>&1' \
  './pi4.exe -i ./p4/includes -i ./01/p4/fabric/include -disable-inlining ./01/p4/fabric/fabric.p4 > ./01/fabric.log 2>&1' \
  './pi4.exe -i ./p4/includes -i ./01/p4/fabric/include -disable-cache -disable-inlining ./01/p4/fabric/fabric.p4 > ./01/fabric.log 2>&1' 
```

```
hyperfine \
  --export-json ./01/measurements_ngsdn.json \
  --runs 1\
  --output inherit \
  './pi4.exe -m 704 -ir -typ ./ngsdn.pi4_type ./ngsdn.pi4'
```

### 2. Effect of MTU

In this experiment, we vary the MTU from 1500 to 12000 bits in steps of 1500

```
hyperfine \
  -P maxlen 1500 12000 -D 1500 \
  --runs 5 \
  --export-json ./02/measurements2.json \
  --show-output\
  './pi4.exe -i ./p4/includes -m {maxlen} ./01/p4/p4tut_basic_tunnel.p4' \
  './pi4.exe -i ./p4/includes -m {maxlen} ./01/p4/p4tut_basic.p4' \
  './pi4.exe -i ./p4/includes -m {maxlen} ./01/p4/p4tut_ecn.p4' \
  './pi4.exe -i ./p4/includes -m {maxlen} ./01/p4/p4tut_load_balance.p4' \
  './pi4.exe -i ./p4/includes -m {maxlen} ./01/p4/p4tut_multicast.p4' \
  './pi4.exe -i ./p4/includes -m {maxlen} ./01/p4/p4tut_qos.p4' \
  './pi4.exe -i ./p4/includes -m {maxlen} ./01/p4/roundtripping-safe.p4' \
  './pi4.exe -i ./p4/includes -m {maxlen} ./01/p4/vlan_decap.p4' \
  './pi4.exe -i ./p4/includes -i ./01/p4/fabric/include -m {maxlen} ./01/p4/fabric/fabric.p4'
```

```
hyperfine \
  --runs 1 \
  --export-json ./02/measurements3.json \
  './pi4.exe -i ./p4/includes -m 12000 ./01/p4/p4tut_basic_tunnel.p4' \
  './pi4.exe -i ./p4/includes -m 12000 ./01/p4/p4tut_basic.p4' \
  './pi4.exe -i ./p4/includes -m 12000 ./01/p4/p4tut_ecn.p4' \
  './pi4.exe -i ./p4/includes -m 12000 ./01/p4/p4tut_load_balance.p4' \
  './pi4.exe -i ./p4/includes -m 12000 ./01/p4/p4tut_multicast.p4' \
  './pi4.exe -i ./p4/includes -m 12000 ./01/p4/p4tut_qos.p4' \
  './pi4.exe -i ./p4/includes -m 12000 ./01/p4/roundtripping-safe.p4' \
  './pi4.exe -i ./p4/includes -m 12000 ./01/p4/vlan_decap.p4' \
  './pi4.exe -i ./p4/includes -i ./01/p4/fabric/include -m 12000 ./01/p4/fabric/fabric.p4'
```

```
hyperfine \
  --runs 1 \
  --export-json ./02/measurement_fabric_7500.json \
  './pi4.exe -i ./p4/includes -i ./01/p4/fabric/include -m 7500 ./01/p4/fabric/fabric.p4'
```

### 3. Full pipeline of fabric.p4
```
hyperfine \
  --runs 1 \
  --output inherit \
  --export-json ./evaluation/03.json \
  'dune exec bin/main.exe -- -i ./p4/includes -i ./evaluation/p4/01/fabric/include ./evaluation/p4/01/fabric/fabric.p4'
```
