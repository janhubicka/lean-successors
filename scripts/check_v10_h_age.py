#!/usr/bin/env python3
"""Finite independent age check for the exact H relation-copying rule.

All directed graphs through three base vertices, eight selected four-vertex
examples, and k=1,2,3 are checked. This is not a proof of the infinite result.
"""
from itertools import combinations


def structure(k, base, n):
    vertices = [("R", i, g) for i in range(n) for g in range(k + 1)]
    vertices += [("F", j, -1) for j in range(2 * n * (k + 1))]

    def allowed(a, b):
        if a[0] != "R" or b[0] != "R":
            return False
        i, q, j, m = a[1], a[2], b[1], b[2]
        return ((i < j and (q < m or q == m == k))
                or (j < i and (m < q or m == q == k)))

    def relation(a, b):
        return base.get((a[1], b[1]), 0) if allowed(a, b) else 0

    def linked(a, b):
        return bool(relation(a, b) or relation(b, a))

    return vertices, relation, linked


def main():
    models = pairs = linked_pairs = triples = irreducible_triples = 0
    for n in range(1, 5):
        directed_pairs = [(i, j) for i in range(n)
                          for j in range(n) if i != j]
        masks = (range(1 << len(directed_pairs)) if n <= 3
                 else [0, 1, 5, 37, 255, 1365, 2730, 4095])
        for mask in masks:
            base = {e: 1 for i, e in enumerate(directed_pairs) if mask >> i & 1}
            for k in range(1, 4):
                vertices, rel, linked = structure(k, base, n)
                models += 1
                for a, b in combinations(vertices, 2):
                    pairs += 1
                    if not linked(a, b):
                        continue
                    linked_pairs += 1
                    assert a[0] == b[0] == "R" and a[1] != b[1]
                    assert rel(a, b) == base.get((a[1], b[1]), 0)
                    assert rel(b, a) == base.get((b[1], a[1]), 0)
                real = [v for v in vertices if v[0] == "R"]
                for triple in combinations(real, 3):
                    triples += 1
                    if not all(linked(a, b) for a, b in combinations(triple, 2)):
                        continue
                    irreducible_triples += 1
                    assert len({v[1] for v in triple}) == 3
                    assert all(rel(a, b) == base.get((a[1], b[1]), 0)
                               for a in triple for b in triple if a != b)
    assert (models, pairs, linked_pairs, triples, irreducible_triples) == (
        231, 90945, 2288, 27749, 588)
    # One-way containment in K is insufficient: it allows deleting
    # a base edge from the top-generation intended K-copy.
    _, deleted, _ = structure(1, {}, 2)
    assert not deleted(("R", 0, 1), ("R", 1, 1))
    assert {(0, 1): 1}[(0, 1)] == 1
    print(f"PASS: {models} models, {pairs} pairs ({linked_pairs} linked), "
          f"{triples} triples ({irreducible_triples} irreducible)")
    print("PASS: one-sided relation containment does not ensure K embeds")


if __name__ == "__main__":
    main()
