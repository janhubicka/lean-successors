#!/usr/bin/env python3
"""Finite checks for a candidate counterexample to the Section 4 projection.

This uses EXACTLY the one-ancestral-parameter, one-letter history syntax:
a history of length n is a tuple of codes, and each code is either
the empty tuple or one ancestral level < current position.

The maps gap(0, []) and gap(2, [0]) implement the existing Lean
FreeAncestral.oneGapShapeMap construction.  U and V use these maps
on their first rows and use identity rows thereafter.

The script checks all geometric lift inclusions for the first six rows
and checks an explicit projected image outside range pi(U).

The infinite reduction witness is explained in
docs/wiki/Fat-Tree-to-Shape-Map-Transfer.md.  This standalone finite
model test is *not* a Lean kernel proof of that infinite witness.
"""
from __future__ import annotations

from functools import lru_cache

History = tuple[tuple[int, ...], ...]


def children(history: History) -> tuple[History, ...]:
    n = len(history)
    return (history + ((),),) + tuple(history + ((j,),) for j in range(n))


@lru_cache(maxsize=None)
def all_level(n: int) -> tuple[History, ...]:
    if n == 0:
        return ((),)
    return tuple(y for x in all_level(n - 1) for y in children(x))


def one_gap(history: History, m: int, inserted: tuple[int, ...]) -> History:
    """The free-ancestral gap map, including the shift of old parameters."""
    assert len(inserted) <= 1 and all(0 <= k < m for k in inserted)
    if len(history) < m:
        return history
    shifted_suffix = tuple(
        tuple(k if k < m else k + 1 for k in code)
        for code in history[m:]
    )
    return history[:m] + (inserted,) + shifted_suffix


def e0(history: History) -> History:
    return one_gap(history, 0, ())


def e2(history: History) -> History:
    return one_gap(history, 2, (0,))


def ucut(i: int) -> int:
    return 0 if i == 0 else i + 1


def vcut(i: int) -> int:
    return 0 if i == 0 else (2 if i == 1 else i + 2)


def index(i: int) -> int:
    return i if i <= 1 else i + 1


def urow(i: int, h: History) -> History:
    return e0(h) if i == 0 else h


def vrow(i: int, h: History) -> History:
    return e0(h) if i == 0 else (e2(h) if i == 1 else h)


def one_lift(row, cut, i: int, starting: set[History]) -> set[History]:
    assert all(len(x) == cut(i) for x in starting)
    return {row(i, y) for x in starting for y in children(x)}


def ambient_lift(i: int, j: int, starting: set[History]) -> set[History]:
    for k in range(i, j):
        starting = one_lift(urow, ucut, k, starting)
    return starting


def main() -> None:
    # Witness of the true infinite strict index map:
    # phi(0)=0, phi(1)=1, phi(i)=i+1 for all i >= 2.
    for i in range(6):
        assert vcut(i) == ucut(index(i))
        assert index(i) < index(i + 1)

    for i in range(5):
        lhs = one_lift(vrow, vcut, i, set(all_level(vcut(i))))
        rhs = ambient_lift(
            index(i), index(i + 1), set(all_level(ucut(index(i))))
        )
        assert lhs <= rhs, f"geometric reduction fails at row {i}"
        print(f"row {i}: {len(lhs)} V-lift nodes ⊆ "
              f"{len(rhs)} U-lift nodes")

    # Pi(U) = e0, Pi(V) = e2 ∘ e0; first map's range excludes
    # ANY parameter level 0 in steps after the inserted first step.
    a1: History = ((),)  # unique source node at level 1
    image_u = e0(a1)
    image_v = e2(e0(a1))
    assert image_u == ((), ())
    assert image_v == ((), (), (0,))
    image_u_at_level_3 = {e0(h) for h in all_level(2)}
    assert image_u_at_level_3 == {((), (), ()), ((), (), (1,))}
    assert image_v not in image_u_at_level_3
    # Because e0 maps every source level n to n+1, no OTHER
    # source level can witness image_v ∈ range(e0).
    assert all(len(e0(h)) == len(h) + 1 for n in range(5) for h in all_level(n))
    print("PASS: pi(V)(a1) is not in range(pi(U)); no right factor exists")
    print("NOTE: finite model regression only; infinite fat reduction "
          "and Lean statement remain to be formalized")


if __name__ == "__main__":
    main()
