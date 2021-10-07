import os
import subprocess
from itertools import chain, combinations

tactics = [
    'ufbv',
    '(then aig solve-eqs ufbv)',
    '(then simplify aig ufbv)',
    '(then solve-eqs ufbv)',
    '(then solve-eqs simplify ufbv)',
    '(then solve-eqs aig ufbv)',
    '(then simplify solve-eqs ufbv)',
    '(then simplify aig solve-eqs ufbv)',
    '(then solve-eqs aig simplify ufbv)',
    '(then simplify solve-eqs aig ufbv)',
    '(then solve-eqs simplify aig ufbv)',
    '(then aig solve-eqs simplify ufbv)',
    '(then aig simplify solve-eqs ufbv)',
    '(then aig ufbv)',
    '(then simplify ufbv)',
    '(then aig simplify ufbv)',
]

benchmarks = ['subtype', 'supertype', 'supertype_opt']

out_dir = '/home/meichholz/benchmark_model_tactics'

for tactic in tactics:
    if tactic.startswith('(then'):
        tactic_str = '_'.join(tactic[6:-1].split(' '))
    else:
        tactic_str = tactic
    path = os.path.join(out_dir, tactic_str)
    os.mkdir(path)
    for b in benchmarks:
        outfile = os.path.join(path, b + '.csv')
        subprocess.Popen([
            '/home/meichholz/benchmark_model.exe',
            '-z3', '/home/meichholz/z3-4.8.10-x64-ubuntu-18.04/bin/z3',
            '-t', tactic,
            '-o', outfile,
            b,
            '16:1500'])
