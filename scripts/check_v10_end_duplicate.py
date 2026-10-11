#!/usr/bin/env python3
"""Independent exhaustive-pattern sampling for the local M3 end duplicate.

Generate only genuine finite partial-structure E-columns and directed L
tuples obeying E3. Append a last vertex that clones the initial E-socle
of an existing vertex, then verify E1--E3 and that every irreducible
ordered induced pattern (or singleton) projects to the old structure.
This is independent evidence; the corresponding Lean proofs are the
source of formal validation.
"""
import itertools
import random


def source_model(rng, N):
    cut = [rng.randrange(max(1, v)) if v > 1 else 0 for v in range(N)]
    binary = [[False] * N for _ in range(N)]
    for i in range(N):
        binary[i][i] = bool(rng.getrandbits(1))
        for j in range(i + 1, N):
            if i < cut[j]:
                binary[i][j] = bool(rng.getrandbits(1))
                binary[j][i] = bool(rng.getrandbits(1))
    unary = [bool(rng.getrandbits(1)) for _ in range(N)]
    diagonal = [bool(rng.getrandbits(1)) for _ in range(N)]
    return cut, binary, unary, diagonal


def append_duplicate(cut, binary, unary, diagonal, original):
    N, free = len(cut), cut[original]
    def E(u, v):
        return u < cut[v] if v < N else (u < free if v == N else False)
    out = [[False] * (N + 1) for _ in range(N + 1)]
    for x in range(N):
        for y in range(N):
            out[x][y] = binary[x][y]
        if x < free:
            out[x][N], out[N][x] = binary[x][original], binary[original][x]
    out[N][N] = binary[original][original]
    return E, out, unary + [unary[original]], diagonal + [diagonal[original]]


def atomic(binary, unary, diagonal, X):
    return (tuple(unary[x] for x in X),
            tuple(diagonal[x] for x in X),
            tuple(binary[x][y] for x in X for y in X if x != y))


def main():
    rng = random.Random(20261010)
    models = copies = 0
    for N in range(1, 7):
        for _ in range(5000 if N <= 4 else 1500):
            cuts, B, U, D = source_model(rng, N)
            original = rng.randrange(N)
            E, C, V, W = append_duplicate(cuts, B, U, D, original)
            f = cuts[original]
            assert all(not E(u, v) or u + 1 < v
                       for v in range(N + 1) for u in range(N + 1))
            assert all(not E(u, v) or all(E(z, v) for z in range(u))
                       for v in range(N + 1) for u in range(N + 1))
            assert all(not (C[u][v] or C[v][u]) or E(u, v)
                       for v in range(N + 1) for u in range(v))
            assert next(u for u in range(N + 1) if not E(u, N)) == f
            for k in range(1, min(6, N + 1) + 1):
                for X in itertools.combinations(range(N + 1), k):
                    if k > 1 and not all(C[u][v] or C[v][u]
                           for u, v in itertools.combinations(X, 2)):
                        continue
                    projection = tuple(original if x == N else x for x in X)
                    assert list(projection) == sorted(set(projection))
                    assert atomic(C, V, W, X) == atomic(B, U, D, projection)
                    copies += 1
            models += 1
    print(f"PASS: {models} partial structures; {copies} "
          "irreducible/singleton induced-pattern projections, E1-E3")


if __name__ == "__main__":
    main()
