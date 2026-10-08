#!/usr/bin/env python3
"""Bounded diagnostic for the E1 necessity example after Proposition 5.5.

The symbolic argument, not finite testing, proves that character 7 forces
source index at least 7 and hence height at least 9.
"""
import random
from itertools import combinations


def allowed(w):
    return all(0 <= c <= i for i, c in enumerate(w))


def prepend_zero(w):
    return (0,) + w


def insert_seven(w):
    return w if len(w) < 7 else w[:7] + (0,) + w[7:]


def check():
    source = (0,) * 7
    source_child = source + (7,)
    target = (0,) * 8
    for f in (prepend_zero, insert_seven):
        assert f(source) == target
        assert f(source_child) == target + (7,)
    assert [len(insert_seven((0,) * j)) for j in range(9)] == [
        0, 1, 2, 3, 4, 5, 6, 8, 9]
    assert [len(prepend_zero((0,) * j)) for j in range(9)] == [
        1, 2, 3, 4, 5, 6, 7, 8, 9]
    rng = random.Random(11)
    tested = 0
    for n in range(12):
        for _ in range(150):
            w = tuple(rng.randrange(i + 1) for i in range(n))
            for f in (prepend_zero, insert_seven):
                assert allowed(w) and allowed(f(w))
                if n > 0:
                    successor_prefix = f(w[:-1]) + (w[-1],)
                    assert f(w)[:len(successor_prefix)] == successor_prefix
                tested += 1
    for n in range(7, 13):
        # For w=(0,1,...,n-1), every retained target position g(j)
        # carries a letter g(j). This letter must be permitted at the
        # source position j, hence g(j) <= j; strict growth gives >= j.
        possible = [g for g in combinations(range(n), 7)
                    if all(g[j] <= j for j in range(7))]
        assert possible == [tuple(range(7))], (n, possible)
    print("PASS: maximal-character words of lengths 7..12 force a unique level set")
    print(f"PASS: {tested} finite successor-preservation checks")
    print("PASS: two distinct height-nine images of {0^8, 0^8 followed by 7}")
    print("Mathematical note: for |w|=7, strict level preservation forces levels 0..8.")


if __name__ == "__main__":
    check()
