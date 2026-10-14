#!/usr/bin/env python3
"""Independent finite regression of the v10 exact H E-relation and its free cuts."""

def position(k, block, generation):
    return 2 * (k + 1) * block + 2 * generation


def build_e_by_insertion(k, blocks):
    """Build E by executing every allowed pair insertion and downward closure."""
    relation = set()
    for j in range(blocks):
        for m in range(k + 1):
            upper = position(k, j, m)
            for i in range(j):
                for q in range(k + 1):
                    if q < m or q == m == k:
                        for lower in range(position(k, i, q) + 1):
                            relation.add((lower, upper))
    return relation


def formula_e(k, lower, upper):
    """Decode the real target before testing the generator conditions."""
    width = 2 * (k + 1)
    j, remainder = divmod(upper, width)
    if remainder % 2:
        return False
    m = remainder // 2
    assert m <= k
    return any(
        lower <= position(k, i, q)
        for i in range(j)
        for q in range(k + 1)
        if q < m or q == m == k
    )


def expected_free(k, j, m):
    if j == 0 or m == 0:
        return 0
    if m == k:
        return position(k, j - 1, k) + 1
    return position(k, j - 1, m - 1) + 1


def main():
    checks = 0
    for k in range(1, 7):
        blocks = 7
        relation = build_e_by_insertion(k, blocks)
        max_vertex = position(k, blocks - 1, k)
        for upper in range(max_vertex + 1):
            free = next(
                lower for lower in range(upper + 1)
                if (lower, upper) not in relation
            )
            if upper % 2:
                assert free == 0, (k, upper, free)
            else:
                j, m = divmod(upper // 2, k + 1)
                assert free == expected_free(k, j, m), (k, j, m, free)
            for lower in range(max_vertex + 1):
                pair = (lower, upper)
                assert (pair in relation) == formula_e(k, lower, upper), (k, pair)
                checks += 1
        for lower, upper in relation:
            assert lower + 1 < upper
            assert all((small, upper) in relation for small in range(lower))
        assert (1, position(k, 1, k)) in relation
    print(
        f"PASS: {checks} independent E comparisons, first free cuts, "
        "spacing and downward closure"
    )


if __name__ == "__main__":
    main()
