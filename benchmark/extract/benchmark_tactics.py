import os
from itertools import chain, combinations
import subprocess

tactics = [
    'ufbv',
    '(then simplify aig ufbv)',
    '(then simplify aig solve-eqs ufbv)',
    '(then simplify ufbv)'
]

out_dir = '/home/meichholz/results_benchmark_extract/'
for tactic in tactics:
    if tactic.startswith('(then'):
        file = '_'.join(tactic[6:-1].split(' '))
    else:
        file = tactic
    filename = os.path.join(out_dir, file + '.csv')
    subprocess.Popen([
        '/home/meichholz/benchmark_extract_optimized.exe',
        '-z3', '/home/meichholz/z3-4.8.10-x64-ubuntu-18.04/bin/z3',
        '-t', tactic,
        '-o', filename,
        '16', '1500'])
