#!/usr/bin/env python3
"""Independent finite checker for Fischer's 24-vertex graph H.

This script intentionally does not use Lean or a graph-theory package.
It reconstructs H = G(K3) from the construction in arXiv:2607.23664v1,
independently decodes the published graph6 string, and checks the finite
claims used by the formalization plan.
"""

from functools import lru_cache
from itertools import combinations, product

GRAPH6 = "W{CGW_@?Y??@?@?@_@??@??K_????G??C??B??@????_??B"

CONSTRUCTION_EDGES = {
    (0, 1), (0, 2), (1, 2),
    (0, 3),
    (3, 4), (4, 5), (4, 6), (5, 6),
    (3, 7), (7, 8), (7, 9), (8, 9),
    (1, 10),
    (10, 11), (11, 12), (11, 13), (12, 13),
    (10, 14), (14, 15), (14, 16), (15, 16),
    (2, 17),
    (17, 18), (18, 19), (18, 20), (19, 20),
    (17, 21), (21, 22), (21, 23), (22, 23),
}

BRANCHES = (
    frozenset(range(3, 10)),
    frozenset(range(10, 17)),
    frozenset(range(17, 24)),
)
TRIANGLE = frozenset({0, 1, 2})

INDEPENDENT_WITNESS = frozenset({3, 5, 8, 10, 12, 15, 17, 19, 22})
ZERO_FORCING_WITNESS = frozenset({4, 5, 7, 8, 11, 12, 14, 15, 18, 19, 22})


def decode_graph6(s: str):
    if not s or ord(s[0]) - 63 > 62:
        raise ValueError("This checker only needs the n <= 62 graph6 form.")
    n = ord(s[0]) - 63
    bits = []
    for ch in s[1:]:
        x = ord(ch) - 63
        if not 0 <= x < 64:
            raise ValueError("Invalid graph6 data character.")
        bits.extend((x >> k) & 1 for k in range(5, -1, -1))
    need = n * (n - 1) // 2
    if len(bits) < need:
        raise ValueError("Truncated graph6 string.")
    bits = bits[:need]
    edges = set()
    k = 0
    for j in range(1, n):
        for i in range(j):
            if bits[k]:
                edges.add((i, j))
            k += 1
    return n, edges


def adjacency(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def connected(adj):
    seen = {0}
    stack = [0]
    while stack:
        u = stack.pop()
        for v in adj[u] - seen:
            seen.add(v)
            stack.append(v)
    return len(seen) == len(adj)


def max_independent_size(adj):
    neigh_mask = []
    for u, ns in enumerate(adj):
        mask = 1 << u
        for v in ns:
            mask |= 1 << v
        neigh_mask.append(mask)

    @lru_cache(maxsize=None)
    def alpha(mask):
        if not mask:
            return 0
        v = (mask & -mask).bit_length() - 1
        without_v = alpha(mask & ~(1 << v))
        with_v = 1 + alpha(mask & ~neigh_mask[v])
        return max(without_v, with_v)

    return alpha((1 << len(adj)) - 1)


def is_independent(adj, vertices):
    vs = set(vertices)
    return all(not (adj[u] & vs) for u in vs)


def force_closure(adj, initial):
    blue = set(initial)
    sequence = []
    while True:
        step = None
        for u in sorted(blue):
            white = adj[u] - blue
            if len(white) == 1:
                step = (u, next(iter(white)))
                break
        if step is None:
            return frozenset(blue), tuple(sequence)
        u, v = step
        blue.add(v)
        sequence.append((u, v))


def is_fort(adj, subset):
    F = set(subset)
    if not F:
        return False
    for u in range(len(adj)):
        if u not in F and len(adj[u] & F) == 1:
            return False
    return True


def branch_forts(adj, branch):
    b = sorted(branch)
    forts = []
    for r in range(1, len(b) + 1):
        for xs in combinations(b, r):
            if is_fort(adj, xs):
                forts.append(frozenset(xs))
    return tuple(forts)


def hitting_subsets(branch, forts, size):
    ans = []
    for xs in combinations(sorted(branch), size):
        S = frozenset(xs)
        if all(S & F for F in forts):
            ans.append(S)
    return tuple(ans)


def zero_forcing_lower_bound_via_forts(adj):
    fort_data = []
    for branch in BRANCHES:
        forts = branch_forts(adj, branch)
        size3 = hitting_subsets(branch, forts, 3)
        size4 = hitting_subsets(branch, forts, 4)
        assert all(not hitting_subsets(branch, forts, k) for k in range(3))
        fort_data.append((forts, size3, size4))

    assert [len(x[0]) for x in fort_data] == [12, 12, 12]
    assert [len(x[1]) for x in fort_data] == [12, 12, 12]
    assert [len(x[2]) for x in fort_data] == [25, 25, 25]

    candidates = []

    for A, B, C in product(*(x[1] for x in fort_data)):
        candidates.append(A | B | C)

    for A, B, C in product(*(x[1] for x in fort_data)):
        base = A | B | C
        for t in TRIANGLE:
            candidates.append(base | {t})

    for j in range(3):
        choices = [fort_data[i][1] for i in range(3)]
        choices[j] = fort_data[j][2]
        for A, B, C in product(*choices):
            candidates.append(A | B | C)

    assert len(candidates) == 17_712
    assert len(set(candidates)) == 17_712
    for S in candidates:
        closure, _ = force_closure(adj, S)
        if len(closure) == len(adj):
            raise AssertionError(f"Found zero-forcing set of size <= 10: {sorted(S)}")
    return fort_data, len(candidates)


def main():
    n, g6_edges = decode_graph6(GRAPH6)
    assert n == 24
    assert g6_edges == CONSTRUCTION_EDGES

    adj = adjacency(n, CONSTRUCTION_EDGES)
    degrees = sorted(map(len, adj))
    assert len(CONSTRUCTION_EDGES) == 30
    assert degrees == [2] * 12 + [3] * 12
    assert max(degrees) == 3
    assert connected(adj)

    assert len(INDEPENDENT_WITNESS) == 9
    assert is_independent(adj, INDEPENDENT_WITNESS)
    alpha = max_independent_size(adj)
    assert alpha == 9

    assert len(ZERO_FORCING_WITNESS) == 11
    closure, sequence = force_closure(adj, ZERO_FORCING_WITNESS)
    assert len(closure) == 24

    fort_data, candidates = zero_forcing_lower_bound_via_forts(adj)

    print("graph6 matches construction: yes")
    print("vertices: 24")
    print("edges: 30")
    print("degree multiset: 12x2, 12x3")
    print("connected: yes")
    print("alpha(H):", alpha)
    print("independent witness:", sorted(INDEPENDENT_WITNESS))
    print("zero-forcing witness:", sorted(ZERO_FORCING_WITNESS))
    print("forcing sequence:", list(sequence))
    print("branch fort counts:", [len(x[0]) for x in fort_data])
    print("branch size-3 hitting-set counts:", [len(x[1]) for x in fort_data])
    print("branch size-4 hitting-set counts:", [len(x[2]) for x in fort_data])
    print("lower-bound candidates checked:", candidates)
    print("Z(H): 11")


if __name__ == "__main__":
    main()
