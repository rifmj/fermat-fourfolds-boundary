#!/usr/bin/env python3
"""Independent verifier of the deep-closure ROUTES recorded in data/l4/CLOSED_LEDGER.tsv.

Every row of the ledger whose route carries an explicit witness of the form

    depth-k [pairs (k1,m-k1),(k2,m-k2),... -> BLOCK + BLOCK + ...]

is re-checked here FROM THE DEFINITIONS, sharing no code with the closure search:

  * each listed pair really is a vanishing pair of the level (k + (m-k) = m, entries nonzero);
  * the multiset union of the class with the listed pairs equals the multiset union of the listed
    blocks (an exact multiset identity, not a count);
  * each block is legitimate: PAIR = a vanishing pair; G2 = a grade-2 Hodge quadruple (constant
    grade 2 over ALL units); G3closed = a grade-3 Hodge sextuple that is closed by one of the four
    BASE predicates, re-derived here (decomposable / quasi / standard / *-split);
  * the recorded depth equals the number of listed pairs.

Rows whose route is a label only (the historical campaign entries, and the two closures proved in
the paper) are reported as such and are NOT counted as verified: this script's output states
exactly how many routes carry a machine-checkable witness.

Usage: python3 verify_deep_routes.py        (assert-fatal on any inconsistency)
"""
import sys, os, re, itertools
from math import gcd
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
LEDGER = HERE + '/data/l4/CLOSED_LEDGER.tsv'


def units(m):
    return [t for t in range(1, m) if gcd(t, m) == 1]


def res(x, m):
    r = x % m
    return r if r else m


def grade_is(c, m, U, g):
    return all(sum(res(t * x, m) for x in c) == g * m for t in U)


def decomposable(a, m):
    cnt = Counter(a)
    for x in cnt:
        y = (m - x) % m
        if (y == x and cnt[x] >= 2) or (y != x and y in cnt):
            return True
    return False


def star_split(a, m):
    return any(sum(a[i] for i in c) % m == 0 and sum(a[i] for i in range(6) if i not in c) % m == 0
               for c in itertools.combinations(range(6), 3) if 0 in c)


def quasi(a, m, U):
    ks = [k for k in range(1, (m + 1) // 2)] + ([m // 2] if m % 2 == 0 else [])
    for k in ks:
        T = sorted(tuple(a) + (k, (m - k) % m))
        if 0 in T:
            continue
        for cmb in itertools.combinations(range(1, 8), 3):
            cs = (0,) + cmb
            c = tuple(T[i] for i in cs)
            d = tuple(T[i] for i in range(8) if i not in cs)
            if grade_is(c, m, U, 2) and grade_is(d, m, U, 2):
                return True
    return False


def standard(a, m, U):
    if m % 5 or m <= 5:
        return False
    d = m // 5
    can = min(tuple(sorted((t * x) % m for x in a)) for t in U)
    for x in range(1, m):
        if (5 * x) % m == 0:
            continue
        ent = [(x + j * d) % m for j in range(5)] + [(m - 5 * x) % m]
        if 0 in ent:
            continue
        if min(tuple(sorted((t * y) % m for y in ent)) for t in U) == can:
            return True
    return False


def base_closed(c, m, U):
    return (decomposable(c, m) or star_split(tuple(c), m)
            or standard(tuple(c), m, U) or quasi(tuple(c), m, U))


def main():
    witnessed = labelled = 0
    for line in open(LEDGER):
        if line.startswith('#'):
            continue
        f = line.rstrip('\n').split('\t')
        if len(f) < 3:
            continue
        m = int(f[0])
        a = tuple(int(x) for x in re.findall(r'\d+', f[1]))
        route = f[2]
        if '[pairs ' not in route:
            labelled += 1
            continue
        U = units(m)
        depth = int(re.search(r'depth-(\d+)', route).group(1)) if route.startswith('depth-') else None
        pairs = [tuple(int(v) for v in p.split(',')) for p in
                 re.findall(r'\((\d+,\d+)\)', route.split('->')[0])]
        blocks = re.findall(r'(PAIR|G2|G3closed)\(([\d, ]+)\)', route.split('->')[1])
        # pairs are vanishing pairs
        for (x, y) in pairs:
            assert (x + y) % m == 0 and x % m and y % m, f"m={m}: bad pair {(x, y)}"
        # exact multiset identity
        left = Counter(a)
        for (x, y) in pairs:
            left[x] += 1
            left[y] += 1
        right = Counter()
        for _, b in blocks:
            for v in (int(v) for v in b.split(',')):
                right[v] += 1
        assert left == right, f"m={m} {a}: multiset identity fails"
        # every block legitimate
        for kind, b in blocks:
            blk = tuple(int(v) for v in b.split(','))
            if kind == 'PAIR':
                assert len(blk) == 2 and sum(blk) % m == 0
            elif kind == 'G2':
                assert len(blk) == 4 and grade_is(blk, m, U, 2), f"m={m}: G2 {blk} not grade 2"
            else:
                assert len(blk) == 6 and grade_is(blk, m, U, 3), f"m={m}: G3 {blk} not grade 3"
                assert base_closed(blk, m, U), f"m={m}: G3closed {blk} is NOT base-closed"
        if depth is not None:
            assert depth == len(pairs), f"m={m}: recorded depth {depth} != {len(pairs)} pairs"
        witnessed += 1
        print(f"  m={m} {a}: route re-verified ({len(pairs)} pairs, "
              f"{len(blocks)} blocks: {','.join(k for k, _ in blocks)})", flush=True)
    print(f"verify_deep_routes: {witnessed} ledger routes re-verified from the definitions "
          f"(exact multiset identity + every block re-derived); {labelled} further rows carry a "
          f"label only (the historical campaign entries and the two closures proved in the paper, "
          f"whose certificates are checked by their own scripts) — PASS")


if __name__ == "__main__":
    main()
