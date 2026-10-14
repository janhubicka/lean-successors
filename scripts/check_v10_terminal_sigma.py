#!/usr/bin/env python3
"""Independent finite age test for the 3-vertex terminal Sigma replica.

No Lean definitions or implementation code are imported. For all Boolean
L-models on up to 3 vertices, and 2,500 reproducibly sampled 4-vertex
models, every irreducible nontrivial pattern or non-neutral singleton in
the one-neutral-filler terminal-letter replica must already occur as an
ordered induced pattern in its original ambient model.
"""
from itertools import combinations
import random


def atomic(B, U, D, vertices):
    return (
        tuple(U[x] for x in vertices),
        tuple(D[x] for x in vertices),
        tuple(B[x][y] for x in vertices for y in vertices if x != y),
    )


def eligible_forbidden_pattern(B, U, D, vertices):
    if len(vertices) == 1:
        x = vertices[0]
        return bool(U[x] or D[x])
    return all(B[x][y] or B[y][x] for x, y in combinations(vertices, 2))


def check_instance(n, B, U, D):
    copies = 0
    for ell in range(n):
        for v in range(ell + 1, n):
            address = {0: ell, 2: v}
            C = [[False] * 3 for _ in range(3)]
            UC = [False] * 3
            DC = [False] * 3
            for x in address:
                UC[x], DC[x] = U[address[x]], D[address[x]]
                for y in address:
                    C[x][y] = B[address[x]][address[y]]

            E = lambda u, w: u == 0 and w == 2
            assert all(
                not E(u, w) or (u + 1 < w and u < 3 and w < 3)
                for u in range(3) for w in range(3)
            )
            assert all(
                not E(u, w) or all(E(z, w) for z in range(u))
                for u in range(3) for w in range(3)
            )
            assert all(
                not (C[u][w] or C[w][u]) or E(u, w)
                for u in range(3) for w in range(u + 1, 3)
            )
            assert next(u for u in range(3) if not E(u, 2)) == 1

            for k in range(1, 4):
                for vertices in combinations(range(3), k):
                    if not eligible_forbidden_pattern(C, UC, DC, vertices):
                        continue
                    pattern = atomic(C, UC, DC, vertices)
                    assert any(
                        atomic(B, U, D, candidate) == pattern
                        for candidate in combinations(range(n), k)
                    ), (n, ell, v, vertices, pattern)
                    copies += 1
    return copies


def main():
    cases = matches = 0
    for n in (1, 2, 3):
        for bits in range(1 << (n * n + 2 * n)):
            B = [[bool((bits >> (x * n + y)) & 1)
                  for y in range(n)] for x in range(n)]
            U = [bool((bits >> (n * n + x)) & 1) for x in range(n)]
            D = [bool((bits >> (n * n + n + x)) & 1) for x in range(n)]
            matches += check_instance(n, B, U, D)
            cases += 1
    rng = random.Random(20261009)
    n = 4
    for _ in range(2500):
        B = [[bool(rng.getrandbits(1)) for _ in range(n)] for _ in range(n)]
        U = [bool(rng.getrandbits(1)) for _ in range(n)]
        D = [bool(rng.getrandbits(1)) for _ in range(n)]
        matches += check_instance(n, B, U, D)
        cases += 1
    print(
        f"PASS: {cases:,} independent relational models; "
        f"{matches:,} forbidden-relevant induced Sigma subsets; "
        "all exact E and forbidden-age checks"
    )


if __name__ == "__main__":
    main()
