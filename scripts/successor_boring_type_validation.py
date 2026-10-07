#!/usr/bin/env python3
"""Finite witness that B1--B2 do not force functoriality of the stated type.

This is a diagnostic of the published definitions, not a Lean certificate or a
counterexample to the Ramsey conclusion itself.
"""
from itertools import product

ALPHABET = ("0", "1")


def words(n):
    return tuple("".join(x) for x in product(ALPHABET, repeat=n))


def extensions(n):
    """E_0={const 0}, E_1={first projection}, E_n=all maps for n>=2.

    Functions are represented by their complete output table in lexical order.
    """
    ins = words(n)
    if n == 0:
        return {("0",)}
    if n == 1:
        return {("0", "1")}
    return set(product(ALPHABET, repeat=len(ins)))


def is_witness(table, n, conditions):
    lookup = dict(zip(words(n), table))
    return all(lookup[prefix] == desired for prefix, desired in conditions)


def interesting_levels(x):
    maximum = max(map(len, x), default=0)
    # Only levels through max length can be interesting: above it all demands
    # are vacuous and every E_n is nonempty.
    answer = []
    for i in range(maximum + 1):
        demand = []
        impossible = False
        for w in x:
            if len(w) == i:
                impossible = True  # One more letter cannot be a prefix of w.
            elif len(w) > i:
                demand.append((w[:i], w[i]))
        if impossible or not any(is_witness(e, i, demand) for e in extensions(i)):
            answer.append(i)
    return tuple(answer)


def tau(x):
    keep = set(interesting_levels(x))
    return frozenset("".join(w[i] for i in range(len(w)) if i in keep) for w in x)


def check_B1_B2():
    # The only B2 pair with n+1 < 2 is m=n=0.
    # Its source is the singleton E_0 constant 0, and E_1's first
    # projection sends the inserted word "0" to 0.
    assert is_witness(next(iter(extensions(1))), 1, [("0", "0")])
    # In every other B2 case n+1 >= 2, so E_{n+1} contains ALL
    # functions. The insertion (a,b) -> a e1(a) b is injective, hence
    # its prescribed output e2(ab) determines a consistent partial map.
    for n in range(1, 4):
        for m in range(n + 1):
            for e1 in extensions(m):
                # Enumerate insertion maps, not the gigantic target E_{n+1}.
                d1 = dict(zip(words(m), e1))
                inserted = [a + d1[a] + b
                            for a in words(m) for b in words(n - m)]
                assert len(set(inserted)) == len(inserted), (m, n)
    # B1 holds for E_1 by definition, and for n>=2 because all
    # projections are in the full function family.
    assert tuple(w[0] for w in words(1)) in extensions(1)
    for n in range(2, 4):
        for j in range(n):
            assert tuple(w[j] for w in words(n)) in extensions(n)
    return True


def run():
    assert check_B1_B2()
    Y = frozenset(("00", "10"))
    PY = frozenset("0" + w for w in Y)
    # P(w) = 0w is shape preserving and has only one omitted target level 0;
    # the missing level is witnessed by E_0's constant-0 extension.
    assert extensions(0) == {("0",)}
    assert interesting_levels(Y) == (0, 1, 2)
    assert interesting_levels(PY) == (1, 3)
    assert tau(Y) == Y
    assert tau(PY) == frozenset(("0", "1"))
    assert tau(Y) != tau(PY)
    print("PASS: B1--B2 proved by explicit low-level checks and full-family extension")
    print("      Higher levels satisfy B1/B2 since E_n is the full function family for n>=2.")
    print(f"PASS: Y={sorted(Y)}, I(Y)={interesting_levels(Y)}, tau(Y)={sorted(tau(Y))}")
    print(f"PASS: P(Y)={sorted(PY)}, I(P(Y))={interesting_levels(PY)}, tau(P(Y))={sorted(tau(PY))}")
    print("PASS: P(w)=0w belongs to M_E, yet tau(P[Y]) != tau(Y).")
    print("      Thus the claimed type invariance/reconstruction is not a consequence of B1--B2.")


if __name__ == "__main__":
    run()
