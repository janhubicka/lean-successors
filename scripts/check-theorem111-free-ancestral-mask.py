#!/usr/bin/env python3
"""Finite sanity checks for the ZFC counterexample to Theorem 1.11.

This is NOT a proof of the transfinite step. It directly enumerates
free ancestral histories with one ancestral parameter and one label,
checking the two masking claims used in the decisive compatibility lemma:

* Every retained level j in range(Q_A) is followed by a mandatory
  source-successor whose ancestral parameter cannot be root level 0.
* Every skipped level j >= 2 is followed by root parameter (0,),
  and this remains true after arbitrary tested pure one-gap maps.

The actual all-level claims and the nowhere-dense ZFC recursion are
proved in English in docs/theorem111-zfc-counterexample-20261016.md.
"""
from functools import lru_cache


@lru_cache(maxsize=None)
def histories(n):
    if n == 0:
        return ((),)
    return tuple(h + (code,)
                 for h in histories(n - 1)
                 for code in ((),) + tuple((k,) for k in range(n - 1)))


def marked_map(h, levels):
    """Q_A on a full source history; levels[n] is lambda_Q_A(n)."""
    out = ((),)  # Q_A(root)=s, the unique level-1 empty-code successor
    for n, code in enumerate(h):
        out += (tuple(levels[k] for k in code),)
        out += ((0,),) * (levels[n + 1] - levels[n] - 1)
    return out


def gap_map(h, m, code):
    """Lean FreeAncestral.oneGapShapeMap on history codes."""
    if len(h) < m:
        return h
    return (h[:m] + (code,)
            + tuple(tuple(k if k < m else k + 1 for k in c)
                    for c in h[m:]))


def check():
    masks = {
        "even": [1, 2, 4, 6, 8, 10, 12],
        "odd": [1, 3, 5, 7, 9, 11, 13],
        "spaced": [1, 2, 5, 8, 10, 12, 15],
    }
    tested = 0
    for name, levels in masks.items():
        for n in range(1, 6):
            images = {marked_map(h, levels) for h in histories(n)}
            assert len(images) == len(histories(n)), (name, n, "injectivity")
            for h in histories(n):
                out = marked_map(h, levels)
                assert len(out) == levels[n]
                for i in range(n):
                    assert out[:levels[i]] == marked_map(h[:i], levels)
                    assert out[levels[i]] == tuple(levels[k] for k in h[i])
                for j in range(1, levels[n]):
                    assert (out[j] == (0,)) == (j not in levels), (
                        name, n, h, j, out
                    )
                tested += 1

        # H fixes every node at levels 0 and 1 for m>=2.
        for m in (2, 3, 4):
            for marker in ((), (0,)):
                def pure_H(h):
                    return gap_map(h, m, marker)

                def pure_level(j):
                    return len(pure_H(((),) * j))

                for n in range(2, 5):
                    for h in histories(n):
                        out = pure_H(marked_map(h, levels))
                        for j in range(2, levels[n]):
                            if j not in levels:
                                assert out[pure_level(j)] == (0,), (
                                    name, m, marker, n, h, j, out
                                )

    print(f"PASS: {tested} full history mask checks plus pure gap-map transport")
    print("NOTE: all-level ZFC topology argument is mathematical, not a "
          "finite-computation conclusion.")


if __name__ == "__main__":
    check()
