import subprocess
import pandas as pd
import re

runs_pp = 10

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

flags = [
    [],
    ['-f'],
    ['-i'],
    ['-n'],
    ['-f', '-i', '-n']
]

out_file = './results.csv'

results = pd.DataFrame({'program': [], 'Optimizations': [], 'runtime': []})
results.to_csv(out_file, index=False)


regex_time = r'[0-9]*.[0-9*]'
regex_rslt = r'true|false'

for prog in programs:
    for suf in suffixes:
        results = pd.DataFrame({'program': [], 'Optimizations': [], 'runtime': []})
        for flag in flags:
            for i in range(runs_pp):
                print(
                    'Running: ' + prog + suf + ' ' + ' '.join(flag) +
                    ' [' + str(i + 1) + '/' + str(runs_pp) + ']')
                rslt = subprocess.run([
                                          '../_build/default/benchmark/benchmark.exe',
                                          './programs/' + prog + suf + '.pi4',
                                          '-t', './programs/' + prog + suf + '.pi4_type']
                                      + flag,
                                      stdout=subprocess.PIPE,
                                      text=True)

                time = re.findall(regex_time, rslt.stdout.strip(), re.MULTILINE)[0]
                result = re.findall(regex_rslt, rslt.stdout.strip(), re.MULTILINE)[0]
                print(result + ' in ' + time + ' ms')
                if((suf == '_safe' and result != 'true') or (suf == '_unsafe' and result != 'false') ):
                    results = results.append(
                        pd.DataFrame(
                            {'program': [prog + suf], 'Optimizations': [' '.join(flag)], 'runtime': ['Err']}),
                        ignore_index=True)
                    print('Invalid Result for:' + prog + suf)
                    break
                results = results.append(
                    pd.DataFrame(
                        {'program': [prog + suf], 'Optimizations': [' '.join(flag)], 'runtime': [time]}),
                    ignore_index=True)
        results.to_csv(out_file, mode='a', index=False, header=False)
