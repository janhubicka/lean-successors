#!/usr/bin/env python3
"""Independent finite regression for the sharp E-gap guard in Lemma 6.34.

Generate partial structures satisfying E1--E3, delete m only when
fl(m+1)<m, and independently verify the induced E spacing, downward
closure, E3 and projection of every irreducible/singleton L-pattern.
"""
import itertools
import random


def random_partial(rng, N):
    f = [rng.randrange(max(1, v)) if v > 1 else 0 for v in range(N)]
    B = [[False] * N for _ in range(N)]
    for j in range(N):
        B[j][j] = bool(rng.getrandbits(1))
        for i in range(j):
            if i < f[j]:
                B[i][j], B[j][i] = (
                    bool(rng.getrandbits(1)), bool(rng.getrandbits(1)))
    U = [bool(rng.getrandbits(1)) for _ in range(N)]
    D = [bool(rng.getrandbits(1)) for _ in range(N)]
    return f, B, U, D


def atoms(B, U, D, X):
    return (tuple(U[x] for x in X), tuple(D[x] for x in X),
            tuple(B[x][y] for x in X for y in X if x != y))


def main():
    rng = random.Random(20261011)
    tests = copies = 0
    for N in range(3, 9):
        for _ in range(4000):
            f, B, U, D = random_partial(rng, N)
            for m in range(1, N - 1):
                if f[m + 1] >= m:
                    continue
                def address(u):
                    return u if u < m else u + 1
                C = [[B[address(u)][address(v)] for v in range(N - 1)]
                     for u in range(N - 1)]
                V = [U[address(u)] for u in range(N - 1)]
                W = [D[address(u)] for u in range(N - 1)]
                def E(u, v):
                    return address(u) < f[address(v)]
                assert all(not E(u,v) or u + 1 < v
                           for v in range(N-1) for u in range(N-1))
                assert all(not E(u,v) or all(E(z,v) for z in range(u))
                           for v in range(N-1) for u in range(N-1))
                assert all(not (C[u][v] or C[v][u]) or E(u,v)
                           for v in range(N-1) for u in range(v))
                for k in range(1, min(6, N - 1) + 1):
                    for X in itertools.combinations(range(N-1), k):
                        if k > 1 and not all(C[u][v] or C[v][u]
                               for u,v in itertools.combinations(X,2)):
                            continue
                        Y = tuple(address(u) for u in X)
                        assert tuple(sorted(Y)) == Y
                        assert atoms(C,V,W,X) == atoms(B,U,D,Y)
                        copies += 1
                tests += 1
    print(f"PASS: {tests} guarded deletions; {copies} induced "
          "irreducible/singleton patterns; all E1-E3")


if __name__ == "__main__":
    main()
