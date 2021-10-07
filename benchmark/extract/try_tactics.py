import concurrent.futures
import os
import signal
import subprocess
from itertools import chain, combinations, permutations


def powerset(iterable):
    s = list(iterable)
    return chain.from_iterable(combinations(s, r) for r in range(len(s) + 1))


def run(tactic, filename):
    with subprocess.Popen(
        [
            '/home/meichholz/benchmark_extract_optimized.exe',
            # '/home/matthias/Documents/papers/safe-p4-paper/paper/dependent-types/implementation/_build/default/benchmark/extract/optimized.exe',
            '-r', '1',
            '-t', tactic,
            # '-o', '/home/matthias/Desktop/safep4/benchmarks/data/test/' + filename,
            '-z3', '/home/meichholz/z3-4.8.10-x64-ubuntu-18.04/bin/z3',
            '-o', '/home/meichholz/tactics/' + filename,
            '8', '8'],
            stdout=subprocess.PIPE, stderr=subprocess.PIPE) as process:
        try:
            exit_code = process.wait(timeout=15)
            if exit_code == 0:
                return tactic
        except subprocess.TimeoutExpired:
            pgrp = os.getpgid(process.pid)
            os.killpg(pgrp, signal.SIGTERM)


tactics = ['aig', 'bit-blast', 'qe', 'simplify', 'solve-eqs']
perms = [item for t in powerset(tactics) for item in permutations(t)]

with concurrent.futures.ThreadPoolExecutor(max_workers=100) as executor:
    futures = []
    for t in perms:
        filename = '{}.csv'.format(
            'ufbv' if not t else '{}_ufbv'.format('_'.join(t)))
        tactic = 'ufbv' if not t else '(then {} ufbv)'.format(' '.join(t))
        futures.append(executor.submit(run, tactic=tactic, filename=filename))

    for future in concurrent.futures.as_completed(futures):
      result = future.result()
      if result:
        print(result)
