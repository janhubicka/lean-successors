#!/usr/bin/env python3
"""Exhaust the first-incident classification using literal H generators.

This is a finite regression, not a Lean certificate. H is built by inserting
allowed ordered tuples; E is built by closing the allowed pairs downward.
The checker never uses the bundledTrace formula to construct the test data.
"""
from __future__ import annotations
from itertools import combinations
import json


def positions(n: int, k: int):
    return [(2 * ((k + 1) * i + g), i, g)
            for i in range(n) for g in range(k + 1)]


def geometry(n: int, k: int):
    vertices = positions(n, k)
    size = 2 * n * (k + 1)
    E = [[False] * size for _ in range(size)]
    generators = []
    for x, i, q in vertices:
        for y, j, m in vertices:
            if i < j and (q < m or q == m == k):
                generators.append((x, y, i, j))
                for t in range(x + 1):
                    E[t][y] = True
    cuts = {v: next(t for t in range(size) if not E[t][v])
            for v, _, _ in vertices}
    for y in range(size):
        for x in range(size):
            if E[x][y]:
                assert x + 1 < y
                assert all(E[t][y] for t in range(x))
    pairs = []
    for left, right in combinations(vertices, 2):
        if left[2] and right[2]:
            limit = min(cuts[left[0]], cuts[right[0]])
            pairs.append((left, right, limit))
    return size, generators, pairs


def main():
    report = dict(base_structures=0, original_pairs=0, positive_mismatches=0,
                  generation_zero_mismatches=0, equal_generation_pairs=0,
                  reverse_only_witnesses=0, no_binary_symbol_pairs=0)
    reverse_example = None
    # Full asymmetric one-symbol languages on 3/4 vertices; a full
    # asymmetric two-symbol language on 3 vertices; and the empty signature.
    cases = [(3, 1, (1, 2, 3, 4)), (4, 1, (1, 2, 3)),
             (3, 2, (2,)), (3, 0, (1, 2, 3))]
    for n, symbols, ks in cases:
        arcs = [(i, j) for i in range(n) for j in range(n) if i != j]
        bitmask = (1 << symbols) - 1
        for k in ks:
            size, generators, pairs = geometry(n, k)
            for code in range(1 << (symbols * len(arcs))):
                B = [[0] * n for _ in range(n)]
                for a, (i, j) in enumerate(arcs):
                    B[i][j] = (code >> (symbols * a)) & bitmask
                H = [[0] * size for _ in range(size)]
                for x, y, i, j in generators:
                    H[x][y] = B[i][j]
                    H[y][x] = B[j][i]
                report['base_structures'] += 1
                for (a, i, ga), (b, j, gb), limit in pairs:
                    report['original_pairs'] += 1
                    if symbols == 0:
                        report['no_binary_symbol_pairs'] += 1
                    if ga == gb:
                        report['equal_generation_pairs'] += 1
                    first = next((x for x in range(limit)
                                  if (H[x][a], H[a][x]) !=
                                     (H[x][b], H[b][x])), None)
                    if first is None:
                        continue
                    assert first % 2 == 0, 'A fake coordinate distinguished types'
                    p, r = divmod(first // 2, k + 1)
                    if r == 0:
                        report['generation_zero_mismatches'] += 1
                        continue
                    report['positive_mismatches'] += 1
                    assert ga != gb, 'Equal generations first differed positively'
                    assert r == min(ga, gb)
                    high, low = (i, j) if ga > gb else (j, i)
                    assert p < i and p < j
                    assert p + 1 < low, 'Sharp free-cut guard failed'
                    incident = next((u for u in range(high)
                                     if B[u][high] or B[high][u]), None)
                    assert p == incident, (n, k, code, i, ga, j, gb, first)
                    if not B[p][high] and B[high][p]:
                        report['reverse_only_witnesses'] += 1
                        if reverse_example is None:
                            reverse_example = dict(n=n, k=k, binary_table=B,
                                left=[i, ga], right=[j, gb],
                                coordinate=first, neighbour=p)
    assert report['positive_mismatches'] > 0
    assert report['reverse_only_witnesses'] > 0
    assert report['no_binary_symbol_pairs'] > 0
    report['reverse_only_example'] = reverse_example
    report['result'] = 'all assertions passed'
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
