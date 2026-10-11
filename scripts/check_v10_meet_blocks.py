#!/usr/bin/env python3
"""Finite adversarial check of the block order in the v10 meet repair.

Enumerates every simple graph on up to five base vertices for k=1..4.
This tests the concrete H-type trace, not a replacement for the proof.
"""
from itertools import combinations


class H:
    def __init__(self, n, k, pairs):
        self.n, self.k, self.pairs = n, k, pairs
        self.N = 2 * (k + 1) * n

    def pos(self, i, g):
        return 2 * (self.k + 1) * i + 2 * g

    def coord(self, v):
        return v // (2 * (self.k + 1)), (v // 2) % (self.k + 1)

    def gen(self, v):
        return 0 if v % 2 else self.coord(v)[1]

    def free(self, v):
        if v % 2:
            return 0
        i, g = self.coord(v)
        if i == 0 or g == 0:
            return 0
        return self.pos(i - 1, g if g == self.k else g - 1) + 1

    def pair(self, u, v):
        if u == v or u % 2 or v % 2:
            return 0
        if u > v:
            return self.pair(v, u)
        i, m = self.coord(u)
        j, n = self.coord(v)
        return int(i < j and (m < n or m == n == self.k)
                   and self.pairs.get((i, j), 0))

    def trace(self, v):
        return tuple(self.pair(u, v) for u in range(self.free(v)))

    def first_neighbour(self, v):
        i, _ = self.coord(v)
        return next((j for j in range(i)
                     if self.pairs.get((j, i), 0)), None)


def main():
    counts = dict(models=0, nontrivial_meets=0,
                  positive_meets=0, checked_charges=0)
    for n in range(1, 6):
        edges = list(combinations(range(n), 2))
        for mask in range(1 << len(edges)):
            pairs = {e: 1 for i, e in enumerate(edges) if mask >> i & 1}
            for k in range(1, 5):
                h = H(n, k, pairs)
                originals = [h.pos(i, g) for i in range(n)
                             for g in range(1, k + 1)]
                counts['models'] += 1
                for a, b in combinations(originals, 2):
                    ta, tb = h.trace(a), h.trace(b)
                    d = next((x for x in range(min(len(ta), len(tb)))
                              if ta[x] != tb[x]), None)
                    if d is None:
                        continue
                    counts['nontrivial_meets'] += 1
                    if h.gen(d) == 0:
                        continue
                    counts['positive_meets'] += 1
                    small, large = ((a, b) if h.gen(a) < h.gen(b)
                                    else (b, a))
                    j, m = h.coord(small)
                    i, s = h.coord(large)
                    p = h.first_neighbour(large)
                    assert m < s
                    assert p is not None and p < min(i, j)
                    assert h.pair(h.pos(p, 0), small) == h.pair(
                        h.pos(p, 0), large) != 0
                    assert d == h.pos(p, m)
                    counts['checked_charges'] += 1
    assert counts == dict(models=4396, nontrivial_meets=161820,
                          positive_meets=49060, checked_charges=49060), counts
    print("PASS", counts)


if __name__ == "__main__":
    main()
