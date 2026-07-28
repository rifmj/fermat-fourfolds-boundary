#!/usr/bin/env python3
"""The p>=7 standard-block sweep: the receipt behind the "restriction is a no-op" statement.

The implemented depth-k partition oracle admits standard blocks only for p in {2,3,5} (lengths
4,4,6). This script tests, EXHAUSTIVELY and from the definitions, whether admitting the longer
standard blocks sigma_{p,x} with p >= 7 would close anything the oracle currently leaves open:

  for every one of the 40 primitive post-depth-two survivors, every prime p >= 7 dividing its
  level m, every admissible x (0 < x < m/p, all entries nonzero), and every augmentation by up to
  D vanishing pairs (D = 2 by default, D = 3 for the residual ten), decide whether

      class  U  (added pairs)  =  sigma_{p,x}  U  (blocks the oracle already admits)

  has a solution — i.e. whether the long standard block would fit as one part of a legitimate
  partition, the rest being pairs, grade-2 Hodge quadruples, or base-closed grade-3 sextuples.

Every hit would mean a class the paper reports as surviving is in fact closed by Aoki Thm 2-1,
so a nonzero count is a defect; the shipped receipt records zero.

Usage:
  python3 long_standard_sweep.py            sweep the 40 at depth <= 2 and the residual 10 at <= 3
  python3 long_standard_sweep.py --emit     also write data/l4/long_standard_sweep.txt
"""
import sys, os, json, itertools
from math import gcd
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
DATA = HERE.rsplit('/code', 1)[0] + '/data/l4'
from census_even import units, hodge_multisets, canon, standard_grade3, Closed0, partition_blocks


def long_standards(m, p):
    """All sigma_{p,x} at level m for the given odd prime p, with nonzero entries."""
    d = m // p
    out = []
    for x in range(1, d):
        ent = [(x + j * d) % m for j in range(p)] + [(m - p * x) % m]
        if 0 in ent:
            continue
        out.append(tuple(sorted(ent)))
    return out


def fits(a, m, blk, depth, U, closed0, memo):
    """Is there an augmentation by <= depth vanishing pairs such that blk is a part of a legitimate
    partition of the augmented multiset?  (blk removed; the remainder must partition.)"""
    half = [k for k in range(1, (m + 1) // 2) if (2 * k) % m] + ([m // 2] if m % 2 == 0 else [])
    for d in range(0, depth + 1):
        for pairs in itertools.combinations_with_replacement(half, d):
            aug = Counter(a)
            for k in pairs:
                aug[k] += 1
                aug[(m - k) % m] += 1
            rest = aug.copy()
            ok = True
            for v in blk:
                if rest[v] <= 0:
                    ok = False
                    break
                rest[v] -= 1
            if not ok:
                continue
            elems = sorted(rest.elements())
            if not elems:
                return (d, pairs)
            if partition_blocks(elems, m, U, closed0, memo) is not None:
                return (d, pairs)
    return None


def main():
    rows = json.load(open(DATA + '/even_final_table.json'))["rows"]
    residual = {(r["m"], tuple(r["class"])) for r in rows
                if r["status"] in ("open", "closed-by-proposition")}
    lines, hits, tested = [], 0, 0
    for r in rows:
        m = tuple(r["class"]), r["m"]
        m, a = r["m"], tuple(r["class"])
        primes = [p for p in range(7, m + 1) if m % p == 0 and all(p % q for q in range(2, p))]
        if not primes:
            continue
        U = units(m)
        S2 = hodge_multisets(m, 4, 2)
        std = standard_grade3(m, U)
        closed0 = Closed0(m, U, std, S2)
        memo = {}
        depth = 3 if (m, a) in residual else 2
        for p in primes:
            for blk in long_standards(m, p):
                tested += 1
                got = fits(a, m, blk, depth, U, closed0, memo)
                if got:
                    hits += 1
                    lines.append(f"HIT m={m} {a} p={p} block={blk} depth={got[0]} pairs={got[1]}")
        lines.append(f"m={m} {a}: primes {primes}, depth <= {depth} — no closure by a p>=7 "
                     f"standard block")
    head = ("=== p>=7 STANDARD-BLOCK SWEEP (receipt for the 'restriction is a no-op' statement) ===\n"
            "Scope: all 40 primitive post-depth-two survivors; every prime p >= 7 dividing the level;\n"
            "every admissible sigma_{p,x}; augmentation depth <= 2, and <= 3 for the ten residual\n"
            "classes (the eight open ones and the two closed by the propositions).\n"
            "A HIT would mean the class is closed by a long standard block, i.e. a defect.\n\n")
    body = "\n".join(lines)
    tail = (f"\n\nTESTED {tested} (class, sigma_{{p,x}}) pairs; HITS: {hits}.\n"
            f"{'NO closure by any p>=7 standard block within the stated depths.' if not hits else 'DEFECT: see HIT lines.'}\n")
    print(body[-600:] if len(body) > 600 else body)
    print(tail.strip())
    assert hits == 0, "a p>=7 standard block closes a reported survivor — the restriction is NOT a no-op"
    if "--emit" in sys.argv:
        open(DATA + '/long_standard_sweep.txt', 'w').write(head + body + tail)
        print(f"WROTE {DATA}/long_standard_sweep.txt")


if __name__ == "__main__":
    main()
