"""Check the three-quadratic-packet transport certificate in four variables.

The 21 integer coefficients are indexed by the 3-by-3 transport matrices
of permutations of six slots. Reconstruct the target independently from
symmetric multiplication. Verify the partially transposed certificate on
every weight block by exact rational elimination.
"""
import itertools as it
import math
from fractions import Fraction as F
from collections import defaultdict
import numpy as np

def powers(d, n):
    if d == 1:
        return [(n,)]
    return [(i,) + p for i in range(n + 1) for p in powers(d - 1, n - i)]

def pt(A, r, m=3):
    p = list(range(2 * m))
    p[m - 1], p[2 * m - 1] = (p[2 * m - 1], p[m - 1])
    return A.reshape((r,) * (2 * m)).transpose(p).reshape(A.shape)

def contingency(p, k=2, m=3):
    v = [0] * (m * m)
    for i, j in enumerate(p):
        v[i // k * m + j // k] += 1
    return tuple(v)

def representatives(k=2, m=3):
    out = {}
    for p in it.permutations(range(k * m)):
        D = contingency(p, k, m)
        if D not in out:
            out[D] = [p, 0]
        out[D][1] += 1
    return out
CERT = [0, 6, 0, 0, 8, 8, 3, 8, 3, 6, 8, 0, 6, 0, 6, 8, 8, 3, 0, 3, 0]

def coefficient_rule(D, count):
    if count == 8:
        return 0
    if count == 64:
        return 8
    assert count == 32
    trace = D[0] + D[4] + D[8]
    if trace == 4:
        return 12 - 6 * D[8]
    assert trace == 1
    return 3 + 3 * D[8]

def conjugate_flow(D, p):
    return tuple((D[p[i] * 3 + p[j]] for i in range(3) for j in range(3)))

def verify_identity():
    """Check the 21 coefficients against the rule and their packet-permutation average."""
    reps = representatives()
    cs = dict(zip(reps, CERT))
    target = {}
    for D, (_, count) in reps.items():
        assert cs[D] == coefficient_rule(D, count)
        endpoint = all((x in (0, 2) for x in D))
        target[D] = F(count, 8) - int(endpoint)
    for D in reps:
        average = sum((F(cs[conjugate_flow(D, p)], 6) for p in it.permutations(range(3))))
        assert average == target[D], (D, average, target[D])
    return True

def integer_operator(d):
    """Construct the integer matrix and partially transpose its third packet."""
    alpha = powers(d, 2)
    r = len(alpha)
    lookup = {a: i for i, a in enumerate(alpha)}
    pairs = []
    for a in alpha:
        u, v = [i for i, n in enumerate(a) for _ in range(n)]
        pairs.append([(u, v)] if u == v else [(u, v), (v, u)])
    q = np.zeros((r ** 3, r ** 3), dtype=np.int64)
    for coeff, (D, (p, _)) in zip(CERT, representatives().items()):
        if coeff == 0:
            continue
        for col, inds in enumerate(it.product(range(r), repeat=3)):
            for choice in it.product(*(pairs[i] for i in inds)):
                word = sum(choice, ())
                word = tuple((word[i] for i in p))
                dest = []
                for u, v in zip(word[::2], word[1::2]):
                    a = tuple((int(i == u) + int(i == v) for i in range(d)))
                    dest.append(lookup[a])
                row = (dest[0] * r + dest[1]) * r + dest[2]
                q[row, col] += coeff
    return (alpha, pt(q, r))

def independent_target(alpha):
    """Build the target directly from Fock multiplication and packet swaps.

    This does not use transport matrices or the proposed coefficients.
    The packet basis is e_i e_i or e_i e_j + e_j e_i.
    """
    d = len(alpha[0])
    r = len(alpha)
    states = list(it.product(range(r), repeat=3))
    by_total = defaultdict(list)
    coef = []
    metric = []
    for n, inds in enumerate(states):
        total = tuple((sum((alpha[i][s] for i in inds)) for s in range(d)))
        off = sum((sum((x > 0 for x in alpha[i])) == 2 for i in inds))
        coef.append(2 ** off)
        metric.append(2 ** off)
        by_total[total].append(n)
    target = np.zeros((r ** 3, r ** 3), dtype=np.int64)
    for total, inds in by_total.items():
        factorial = math.prod((math.factorial(n) for n in total))
        for i in inds:
            for j in inds:
                value = F(factorial * coef[i] * coef[j], 8)
                assert value.denominator == 1
                target[i, j] = value.numerator
    for col, inds in enumerate(states):
        for p in it.permutations(range(3)):
            dest = tuple((inds[i] for i in p))
            row = (dest[0] * r + dest[1]) * r + dest[2]
            target[row, col] -= metric[col]
    return target

def verify_direct_identity(d):
    alpha, P = integer_operator(d)
    r = len(alpha)
    Q = pt(P, r)
    tensor = Q.reshape((r,) * 6)
    total = sum((tensor.transpose(p + tuple((i + 3 for i in p))) for p in it.permutations(range(3)))).reshape(Q.shape)
    X = independent_target(alpha)
    assert np.array_equal(total, 6 * X)
    print('Independent Fock / permutation identity: EXACT PASS', flush=True)
    return True

def exact_psd(block):
    """Test a symmetric block by rational elimination, handling singular pivots."""
    a = [[F(int(x)) for x in row] for row in block]
    pivots = []
    for k in range(len(a)):
        p = a[k][k]
        if p < 0:
            return (False, pivots, p)
        pivots.append(p)
        if p == 0:
            if any((a[k][j] for j in range(k + 1, len(a)))):
                return (False, pivots, 'nonzero zero-pivot row')
            continue
        for i in range(k + 1, len(a)):
            if not a[i][k]:
                continue
            factor = a[i][k] / p
            for j in range(i, len(a)):
                a[i][j] -= factor * a[k][j]
                a[j][i] = a[i][j]
    return (True, pivots, None)

def verify(d, verbose=False):
    """Check the weight decomposition and the full list of exact pivots."""
    verify_identity()
    alpha, P = integer_operator(d)
    r = len(alpha)
    assert np.array_equal(P, P.T)
    groups = defaultdict(list)
    for ind, (i, j, k) in enumerate(it.product(range(r), repeat=3)):
        weight = tuple((alpha[i][s] + alpha[j][s] - alpha[k][s] for s in range(d)))
        groups[weight].append(ind)
    group_number = {i: num for num, inds in enumerate(groups.values()) for i in inds}
    for i, j in zip(*P.nonzero()):
        assert group_number[i] == group_number[j]
    all_pivots = []
    sizes = []
    failed = []
    for weight, inds in groups.items():
        ok, pivots, error = exact_psd(P[np.ix_(inds, inds)])
        all_pivots += pivots
        sizes.append(len(inds))
        if not ok:
            failed.append((weight, error))
    print(dict(d=d, dimension=r ** 3, weight_blocks=len(groups), largest_block=max(sizes), positive_pivots=sum((x > 0 for x in all_pivots)), zero_pivots=sum((x == 0 for x in all_pivots)), failures=failed), flush=True)
    if not failed and verbose:
        print('distinct positive exact pivots:', sorted(set((x for x in all_pivots if x))), flush=True)
    return not failed

def ldlt_certificate(block):
    """Reconstruct the original block entry by entry from rational LDLᵀ factors."""
    n = len(block)
    A = [[F(int(x)) for x in row] for row in block]
    L = [[F(int(i == j)) for j in range(n)] for i in range(n)]
    diagonal = []
    for k in range(n):
        pivot = A[k][k]
        assert pivot >= 0
        diagonal.append(pivot)
        if pivot == 0:
            assert all((A[k][j] == 0 for j in range(k + 1, n)))
            continue
        for i in range(k + 1, n):
            L[i][k] = A[i][k] / pivot
        for i in range(k + 1, n):
            for j in range(i, n):
                A[i][j] -= L[i][k] * pivot * L[j][k]
                A[j][i] = A[i][j]
    for i in range(n):
        for j in range(n):
            assert sum((L[i][k] * diagonal[k] * L[j][k] for k in range(n))) == int(block[i, j])
    return diagonal

def verify_weight_representatives():
    """Replay LDLᵀ on one representative of each of the twelve weight types."""
    alpha, P = integer_operator(4)
    r = len(alpha)
    weight_groups = defaultdict(list)
    for index, (i, j, k) in enumerate(it.product(range(r), repeat=3)):
        weight = tuple((alpha[i][s] + alpha[j][s] - alpha[k][s] for s in range(4)))
        weight_groups[weight].append(index)
    seen = set()
    for weight, indices in weight_groups.items():
        typ = tuple(sorted(weight, reverse=True))
        if typ in seen:
            continue
        seen.add(typ)
        block = P[np.ix_(indices, indices)]
        diagonal = ldlt_certificate(block)
        if any(diagonal):
            print(typ, 'size', len(block), 'rank', sum((x > 0 for x in diagonal)), 'exact reconstruction PASS')
    assert len(seen) == 12
    print('All twelve representative types reconstructed exactly.')
if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Run Python with assertions enabled.')
    assert verify_identity()
    assert verify_direct_identity(4)
    assert verify(4)
    print('All certificate checks passed using integer and rational arithmetic.')
    verify_weight_representatives()
