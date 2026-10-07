#!/usr/bin/env python3
"""Finite checks supporting the boring-extension erasure proof (not a Lean proof)."""
from itertools import combinations, product

SIGMA = ("0", "1")


def words(n):
    return tuple(product(SIGMA, repeat=n))


def family(kind, n):
    inp = words(n)
    if kind == "all":
        return tuple(product(SIGMA, repeat=len(inp)))
    projs = tuple(tuple(w[j] for w in inp) for j in range(n))
    if kind == "proj":
        return tuple(dict.fromkeys(projs))
    if kind == "proj_const":
        return tuple(dict.fromkeys(projs + (tuple("0" for _ in inp),)))
    if kind == "bad":
        if n == 0:
            return (("0",),)
        if n == 1:
            return (("0", "1"),)
        return tuple(product(SIGMA, repeat=len(inp)))
    raise ValueError(kind)


def boring(kind, X, i):
    if any(len(w) == i for w in X):
        return False
    needs = {(w[:i], w[i]) for w in X if len(w) > i}
    if len({p for p, _ in needs}) != len(needs):
        return False
    if kind == "all" or (kind == "bad" and i >= 2):
        return True
    if kind == "bad":
        if i == 0:
            return all(w[i] == "0" for w in X if len(w) > i)
        return all(w[i] == w[0] for w in X if len(w) > i)
    if kind == "proj":
        return any(all(w[i] == w[j] for w in X if len(w) > i)
                   for j in range(i))
    if kind == "proj_const":
        return all(w[i] == "0" for w in X if len(w) > i) or any(
            all(w[i] == w[j] for w in X if len(w) > i)
            for j in range(i))
    raise ValueError(kind)


def tau(kind, X):
    if not X:
        return frozenset()
    interesting = {i for i in range(max(map(len, X)) + 1)
                   if not boring(kind, X, i)}
    return frozenset(tuple(w[i] for i in range(len(w))
                           if i in interesting) for w in X)


def insert(w, m, table):
    if len(w) < m:
        return w
    return w[:m] + (table[words(m).index(w[:m])],) + w[m:]


def check_b2_b3(kind, max_n):
    checked = 0
    b2 = True
    b3 = True
    for n in range(max_n + 1):
        nw = words(n)
        nnw = words(n + 1)
        nindex = {w: i for i, w in enumerate(nw)}
        nnindex = {w: i for i, w in enumerate(nnw)}
        medium = family(kind, n)
        large = set(family(kind, n + 1))
        for m in range(n + 1):
            mw = words(m)
            mindex = {w: i for i, w in enumerate(mw)}
            for e in family(kind, m):
                embedded = {w[:m] + (e[mindex[w[:m]]],) + w[m:]: w
                            for w in nw}
                assert len(embedded) == len(nw)
                for old in medium:
                    if not any(all(target[nnindex[v]] == old[nindex[w]]
                                   for v, w in embedded.items())
                               for target in large):
                        b2 = False
                for new in large:
                    contracted = tuple(new[nnindex[next(v for v, z
                                      in embedded.items() if z == w)]]
                                       for w in nw)
                    if contracted not in medium:
                        b3 = False
                    checked += 1
    return b2, b3, checked


def check_type_insertion(kind):
    ambient = tuple(w for n in range(4) for w in words(n))
    tested = 0
    for size in range(4):
        for Z in combinations(ambient, size):
            X = frozenset(Z)
            old = tau(kind, X)
            for m in range(3):
                for e in family(kind, m):
                    Y = frozenset(insert(w, m, e) for w in X)
                    assert len(X) == len(Y)
                    assert tau(kind, Y) == old, (kind, m, X, Y)
                    tested += 1
    return tested


def main():
    total = 0
    for kind, n in (("all", 2), ("proj", 3), ("proj_const", 3),
                    ("bad", 2)):
        b2, b3, combinations_count = check_b2_b3(kind, n)
        assert b2, kind
        assert b3 == (kind != "bad"), kind
        print(f"{kind}: B2={b2}, B3={b3}, checked={combinations_count}")
        if b3:
            c = check_type_insertion(kind)
            total += c
            print(f"{kind}: type preserved through {c} insertions")
    assert total == 17856
    assert tau("bad", frozenset((tuple("00"), tuple("10")))) != tau(
        "bad", frozenset((tuple("000"), tuple("010"))))
    print(f"PASS: {total} finite insertion/type tests; erasure counterexample")
    # The infinite theorems also have explicit symbolic counterexamples;
    # this finite loop is only a regression against misreading their types.
    X = frozenset((tuple("01"),))
    Y = frozenset((tuple("01"), tuple("11")))
    assert tau("bad", X) == frozenset((("1",),))
    assert tau("bad", Y) == Y
    forced = 0
    for N in range(2, 8):
        ambient = [w for i in range(N + 1) for w in words(i)]
        for u, v in combinations(ambient, 2):
            if tau("bad", frozenset((u, v))) != Y:
                continue
            assert {u[:2], v[:2]} == {tuple("01"), tuple("11")}
            assert tau("bad", frozenset((u,))) == tau("bad", X)
            assert tau("bad", frozenset((v,))) == tau("bad", X)
            assert u[0] != v[0]
            forced += 1
    assert forced == 1818
    print(f"PASS: {forced} finite pairs forced bichromatic")
    gr_count = 0
    for N in range(2, 9):
        for W in product(("0", "lambda0", "lambda1"), repeat=N):
            if "lambda0" not in W or "lambda1" not in W:
                continue
            if W.index("lambda0") >= W.index("lambda1"):
                continue
            U0 = tuple("0" if c == "0" else "lambda0" for c in W)
            U1 = tuple("1" if c == "lambda0" else
                       "lambda0" if c == "lambda1" else "0" for c in W)
            assert "1" not in U0 and "1" in U1
            gr_count += 1
    assert gr_count == 4414
    print(f"PASS: {gr_count} mixed-alphabet parameter-word targets")


if __name__ == "__main__":
    main()
