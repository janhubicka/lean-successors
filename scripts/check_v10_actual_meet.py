#!/usr/bin/env python3
"""Finite regression for complete L+ records and genuine prefix meets.

All relations are inserted using the literal real-pair generators. Type
keys include the entire induced socle, singleton/diagonal data, and both
L and E cross directions. Meets are found by comparing complete keys;
no bundledTrace or purported meet formula is used to construct a meet.
The assertions test the theorem afterwards. This is not a Lean proof.
"""
from collections import Counter
from itertools import combinations
import json


def geometry(n, k):
    N = 2 * (k + 1) * n
    real = {2 * ((k + 1) * i + g): (i, g)
            for i in range(n) for g in range(k + 1)}
    E = [[False] * N for _ in range(N)]
    generators = []
    for x, (i, q) in real.items():
        for y, (j, m) in real.items():
            if i < j and (q < m or q == m == k):
                generators.append((x, y, i, j))
                for u in range(x + 1):
                    E[u][y] = True
    cuts = [next(u for u in range(N) if not E[u][v]) for v in range(N)]
    return N, real, E, cuts, generators


def main():
    counts = Counter()
    witness = None
    for n, k, max_binary, singleton_codes in [
            (3, 1, 64, range(64)), (3, 2, 64, range(64)),
            (3, 3, 64, range(64)), (4, 2, 4096, (0, 85, 170, 255))]:
        N, real, E, cuts, generators = geometry(n, k)
        arcs = [(i, j) for i in range(n) for j in range(n) if i != j]
        for binary_code in range(max_binary):
            base = [[False] * n for _ in range(n)]
            for bit, (i, j) in enumerate(arcs):
                base[i][j] = bool(binary_code & (1 << bit))
            B = [[False] * N for _ in range(N)]
            for x, y, i, j in generators:
                B[x][y], B[y][x] = base[i][j], base[j][i]
            for singleton_code in singleton_codes:
                U = [False] * N
                D = [False] * N
                for v, (i, _) in real.items():
                    U[v] = bool(singleton_code & (1 << (2 * i)))
                    D[v] = bool(singleton_code & (1 << (2 * i + 1)))
                # ALL tuples within the common socle, stored once per cut.
                socles = [(tuple(U[:d]), tuple(D[:d]),
                           tuple(B[x][y] for x in range(d) for y in range(d)),
                           tuple(E[x][y] for x in range(d) for y in range(d)))
                          for d in range(max(cuts) + 1)]
                records = [[(socles[d], U[v], D[v], B[v][v], E[v][v],
                             tuple((B[x][v], B[v][x], E[x][v], E[v][x])
                                   for x in range(d)))
                            for d in range(cuts[v] + 1)] for v in range(N)]
                counts['models'] += 1
                for a, b in combinations(range(N), 2):
                    counts['original_pairs'] += 1
                    if records[a][0] != records[b][0]:
                        counts['distinct_roots'] += 1
                        continue
                    limit = min(cuts[a], cuts[b])
                    equal_cuts = [d for d in range(limit + 1)
                                  if records[a][d] == records[b][d]]
                    meet = max(equal_cuts)
                    assert equal_cuts == list(range(meet + 1))
                    if meet == cuts[a] or meet == cuts[b]:
                        counts['comparable_originals'] += 1
                        continue
                    counts['nontrivial_meets'] += 1
                    assert E[meet][a] and E[meet][b]
                    assert records[a][meet + 1] != records[b][meet + 1]
                    assert (B[meet][a], B[a][meet]) != (B[meet][b], B[b][meet])
                    assert meet in real, 'Fake coordinate first differed'
                    p, r = real[meet]
                    if r == 0:
                        counts['generation_zero_meets'] += 1
                        continue
                    counts['positive_generation_meets'] += 1
                    i, ga = real[a]
                    j, gb = real[b]
                    assert ga > 0 and gb > 0 and ga != gb
                    assert r == min(ga, gb)
                    high, low = (i, j) if ga > gb else (j, i)
                    assert p < high and p + 1 < low
                    first = next(u for u in range(high)
                                 if base[u][high] or base[high][u])
                    assert p == first
                    if not base[p][high] and base[high][p]:
                        counts['reverse_only_charges'] += 1
                    # All pairs of nontrivial represented prefixes: compare
                    # the full keys again, not a presumed minimum formula.
                    for da in range(meet + 1, cuts[a] + 1):
                        for db in range(meet + 1, cuts[b] + 1):
                            actual = max(d for d in range(min(da, db) + 1)
                                         if records[a][d] == records[b][d])
                            assert actual == meet
                            counts['nontrivial_prefix_pairs'] += 1
                    if witness is None:
                        witness = dict(n=n, k=k, base_binary=base,
                                       singleton_code=singleton_code,
                                       originals=[a, b], meet=meet,
                                       neighbour=p, generation=r)
    assert counts['positive_generation_meets'] and counts['reverse_only_charges']
    assert counts['distinct_roots'] and counts['nontrivial_prefix_pairs']
    print(json.dumps(dict(counts=counts, example=witness,
                         result='all complete-record assertions passed'), indent=2))


if __name__ == '__main__':
    main()
