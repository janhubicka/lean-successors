#!/usr/bin/env python3
"""Test actual finite meet/parameter closure using complete induced L+ records.

E columns and permitted asymmetric L relations are generated independently.
Crossing parameters are extracted by reindexing the successor record itself,
not by looking up the parameter the theorem predicts. This is a finite
regression, not a replacement for the Lean proof.
"""
from __future__ import annotations
from collections import Counter
from itertools import combinations_with_replacement, product
import json


def record(ids, binary, unary, diagonal, e):
    return (len(ids)-1, tuple(unary[x] for x in ids),
            tuple(diagonal[x] for x in ids),
            tuple(binary[x][y] for x in ids for y in ids),
            tuple(e[x][y] for x in ids for y in ids))


def induced(q, ids):
    n = q[0]+1
    return (len(ids)-1, tuple(q[1][x] for x in ids),
            tuple(q[2][x] for x in ids),
            tuple(q[3][x*n+y] for x in ids for y in ids),
            tuple(q[4][x*n+y] for x in ids for y in ids))


def prefix(q, d):
    assert 0 <= d <= q[0]
    return induced(q, [*range(d), q[0]])


def meet(a, b):
    if prefix(a, 0) != prefix(b, 0):
        return None
    return next(prefix(a, d) for d in range(min(a[0], b[0]), -1, -1)
                if prefix(a, d) == prefix(b, d))


def parameter(q, i):
    assert 0 <= i < q[0]
    successor = prefix(q, i+1)
    n = successor[0]+1
    f = next(x for x in range(i+1) if not successor[4][x*n+i])
    return None if f == 0 else induced(successor, [*range(f), i])


def main():
    counts = Counter()
    missing_principal = None
    for n in (3, 4, 5):
        for cuts in product(*(range(max(1, v)) for v in range(n))):
            E = [[x < cuts[y] for y in range(n)] for x in range(n)]
            edges = [(x, y) for y in range(n) for x in range(cuts[y])]
            all_codes = 1 << (2*len(edges))
            codes = range(all_codes) if n < 5 else sorted(set(
                (0, all_codes-1, all_codes//3, 2*all_codes//3,
                 all_codes//2, max(0, all_codes//2-1), 1 % all_codes)))
            for code in codes:
                B = [[False]*n for _ in range(n)]
                for j, (x, y) in enumerate(edges):
                    B[x][y] = bool(code & (1 << (2*j)))
                    B[y][x] = bool(code & (1 << (2*j+1)))
                for singletons in range(4):
                    U = [bool(singletons & 1) and bool(v % 2) for v in range(n)]
                    D = [bool(singletons & 2) and bool(v % 3) for v in range(n)]
                    originals = [record([*range(cuts[v]), v], B, U, D, E)
                                 for v in range(n)]
                    nodes = {prefix(q, d) for q in originals for d in range(q[0]+1)}
                    params = {(q, i): parameter(q, i) for q in nodes for i in range(q[0])}
                    meets = {(a, b): meet(a, b) for a in nodes for b in nodes}
                    # Check all possible extracted crossings against the actual
                    # ordinary vertex; the expected answer did not define params.
                    for (q, i), p in params.items():
                        assert p == (originals[i] if cuts[i] else None)
                        counts['crossings'] += 1
                    counts['models'] += 1
                    for selected in range(1 << n):
                        I = {i for i in range(n) if selected & (1 << i)}
                        for seed in range(n):
                            V = {seed} | {i for i in I if cuts[i] > 0}
                            allowed = {prefix(originals[v], d) for v in V
                                       for d in range(originals[v][0]+1)}
                            closure = {originals[seed]}
                            rounds = 0
                            while True:
                                nxt = set(closure)
                                for a in closure:
                                    for i in I:
                                        if i < a[0] and params[a, i] is not None:
                                            nxt.add(params[a, i])
                                for a, b in combinations_with_replacement(closure, 2):
                                    if meets[a, b] is not None:
                                        nxt.add(meets[a, b])
                                assert nxt <= allowed
                                rounds += 1
                                if nxt == closure:
                                    break
                                counts['added_nodes'] += len(nxt)-len(closure)
                                closure = nxt
                            counts['stages'] += 1
                            counts['max_rounds'] = max(counts['max_rounds'], rounds)
                            for a, b in combinations_with_replacement(closure, 2):
                                m = meets[a, b]
                                if m is not None and m != a and m != b:
                                    reps_a = [v for v in V if a[0] <= cuts[v]
                                              and prefix(originals[v], a[0]) == a]
                                    reps_b = [v for v in V if b[0] <= cuts[v]
                                              and prefix(originals[v], b[0]) == b]
                                    assert reps_a and reps_b
                                    for v in reps_a:
                                        for w in reps_b:
                                            assert meet(originals[v], originals[w]) == m
                                            counts['meet_original_pairs'] += 1
                            # Detect why merely keeping the seed is insufficient.
                            seed_prefixes = {prefix(originals[seed], d)
                                             for d in range(cuts[seed]+1)}
                            if missing_principal is None and not closure <= seed_prefixes:
                                missing_principal = dict(size=n, cuts=cuts,
                                    binary_code=code, singleton_code=singletons,
                                    selected=sorted(I), seed=seed,
                                    stage_pool=sorted(V), closure_size=len(closure))
    assert counts['added_nodes'] > 0
    assert counts['meet_original_pairs'] > 0
    assert counts['max_rounds'] >= 3, 'Need genuinely iterated closure examples'
    assert missing_principal is not None
    print(json.dumps(dict(counts=counts, missing_principal_example=missing_principal,
                         result='all complete-record closure assertions passed'), indent=2))


if __name__ == '__main__':
    main()
