import subprocess
import re
import pandas as pd

clear_line = '                                         '
programs = [
    'tut_basic',
    'tut_tunnel',
    'tut_load_balance',
    'determined_forwarding',
    'header_dependency',
    'ipv4_opt',
    'ipv4_ttl',
    'mutual_exclusion_ingress',
    'roundtripping',
    'vlan_decap'
]

suffixes = [
    '_safe',
    '_unsafe'
]

out_file = './cache.csv'

results = pd.DataFrame({'program': [], 'inst_hit': [], 'inst_miss': [], 'len_hit': [], 'len_miss': []})

for prog in programs:
    for suf in suffixes:
        print('Running: ' + prog + suf + ' ' + ' -f -i -n ')
        rslt = subprocess.run([
                                  '../_build/default/benchmark/benchmark.exe',
                                  './programs/' + prog + suf + '.pi4',
                                  '-t', './programs/' + prog + suf + '.pi4_type',
                                  '-c', '-f', '-i', '-n'],
                              capture_output=True,
                              text=True)
        i_hit = len(re.findall('.*INSTANCE CACHE: HIT\n', rslt.stderr))
        i_miss = len(re.findall('.*INSTANCE CACHE: MISS\n', rslt.stderr))
        l_hit = len(re.findall('.*LENGTH CACHE: HIT\n', rslt.stderr))
        l_miss = len(re.findall('.*LENGTH CACHE: MISS\n', rslt.stderr))
        print(i_hit + i_miss + l_hit + l_miss)
        results = results.append(
            pd.DataFrame(
                {'program': [prog + suf],
                 'inst_hit': [i_hit],
                 'inst_miss': [i_miss],
                 'len_hit': [l_hit],
                 'len_miss': [l_miss]},
            ),
            ignore_index=True
        )

print(results)
results.to_csv(out_file)
