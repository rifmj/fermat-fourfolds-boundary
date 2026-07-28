"""Depth-3 closure predicate at m=33 (§79 follow-up; the last cheap shot at the survivor).

Predicate: exists <=3 vanishing pairs P such that a (+) P partitions into zero-sum blocks,
each certifying:
  size-2 : vanishing pair {x, m-x}                       [Aoki Thm 1-1 / D-class]
  size-4 : grade-2 Hodge quadruple (forall-t == 2m)      [Lefschetz (1,1) on X^2]
  size-6 : grade-3 Hodge sextuple (forall-t == 3m) AND closed_0
           (decomposable / quasi [da Silva] / 3+3-split [§75]; standard = none at 5∤33)
Fire => claim(a) via Aoki Thm 1-4(i) joins + 1-4(ii) cancellation of delta in D^{2#P-2}
(same chain as §79). O7 gates mandatory: zero-sum alone certifies NOTHING.

Calibration (B4): the m=45 target must FIRE at depth 2 (the §79 certificate) before m=33 runs.
Usage: python3 predicates33_depth3.py            (calibration + m=33 depth 3)
"""
import sys, time
from itertools import combinations_with_replacement, combinations
from collections import Counter
from math import gcd
import importlib.util as _ilu, os as _os

_here = _os.path.dirname(_os.path.abspath(__file__))
_spec = _ilu.spec_from_file_location("census_scan_v2", _os.path.join(_here, "census_scan_v2.py"))
_v2 = _ilu.module_from_spec(_spec); _spec.loader.exec_module(_v2)

LOG = _here.rsplit('/code/', 1)[0] + '/data/l4/predicates33_depth3.log'
logf = open(LOG, 'a')
def say(s):
    print(s); logf.write(s + "\n"); logf.flush()

def units(m): return [t for t in range(1, m) if gcd(t, m) == 1]

def grade_ok(c, m, g, U):
    return all(x % m for x in c) and all(sum((t * x) % m for x in c) == g * m for t in U)

class Closed6:
    """closed_0 test for grade-3 sextuples at level m: decomposable / STANDARD (AP-5, 5|m) /
    quasi [da Silva] / 3+3-split [§75]. (Standard is empty at 5∤33 but load-bearing for the
    m=45 calibration — omitting it was the first run's calibration-caught bug.)"""
    def __init__(self, m, U):
        self.m, self.U = m, U
        self.S2 = _v2.hodge_multisets(m, 4, 2)      # grade-2 quadruples (multiset tuples)
        self.std = _v2.standard_grade3(m, U)        # canonical reps of AP-5 standards
        self.memo = {}
    def __call__(self, c):
        c = tuple(sorted(x % self.m for x in c))
        if c in self.memo: return self.memo[c]
        m = self.m
        r = (_v2.has_pair(c, m) or _v2.canon(c, m, self.U) in self.std
             or _v2.splittable(c, m) or _v2.quasi(c, m, self.S2))
        self.memo[c] = r
        return r

def partitions_into_blocks(elems, m, U, closed6, memo_g2):
    """Yield one certifying partition of the sorted element list (or None). Blocks: 2/4/6."""
    n = len(elems)
    if n == 0:
        return []
    first = elems[0]
    rest = elems[1:]
    # size-2: pair {first, m-first}
    tgt = (m - first) % m
    if tgt in rest:
        r2 = list(rest); r2.remove(tgt)
        sub = partitions_into_blocks(r2, m, U, closed6, memo_g2)
        if sub is not None:
            return [("PAIR", (first, tgt))] + sub
    # size-4 blocks containing first
    for idx in combinations(range(len(rest)), 3):
        blk = (first,) + tuple(rest[i] for i in idx)
        if sum(blk) % m: continue
        key = tuple(sorted(blk))
        if key not in memo_g2:
            memo_g2[key] = grade_ok(key, m, 2, U)
        if memo_g2[key]:
            r2 = [rest[i] for i in range(len(rest)) if i not in idx]
            sub = partitions_into_blocks(r2, m, U, closed6, memo_g2)
            if sub is not None:
                return [("G2", key)] + sub
    # size-6 blocks containing first
    if n >= 6:
        for idx in combinations(range(len(rest)), 5):
            blk = (first,) + tuple(rest[i] for i in idx)
            if sum(blk) % m: continue
            key = tuple(sorted(blk))
            if grade_ok(key, m, 3, U) and closed6(key):
                r2 = [rest[i] for i in range(len(rest)) if i not in idx]
                sub = partitions_into_blocks(r2, m, U, closed6, memo_g2)
                if sub is not None:
                    return [("G3closed", key)] + sub
    return None

def run(m, a, depth, label):
    U = units(m)
    closed6 = Closed6(m, U)
    memo_g2 = {}
    say(f"=== {label}: m={m} a={a} depth<={depth} (|S2|={len(closed6.S2)}) ===")
    t0 = time.time()
    half = [k for k in range(1, (m + 1) // 2) if (2 * k) % m]
    fired = False
    for d in range(1, depth + 1):
        cnt = 0
        for pairs in combinations_with_replacement(half, d):
            aug = sorted(list(a) + [x for k in pairs for x in (k, m - k)])
            cert = partitions_into_blocks(aug, m, U, closed6, memo_g2)
            cnt += 1
            if cert is not None:
                # reject the trivial re-partition: every added pair a PAIR-block and the
                # remaining blocks exactly {a}? impossible for indecomposable a (a is one
                # 6-block only if closed_0(a)) — but print and check by eye anyway.
                say(f"FIRE d={d} pairs={[(k, m-k) for k in pairs]}")
                for kind, blk in cert:
                    say(f"   {kind}: {blk}")
                fired = True
        say(f"  depth {d}: {cnt} augmentations exhausted, fired={fired}  [{time.time()-t0:.1f}s]")
        if fired: break
    if not fired:
        say(f"  NO-FIRE through depth {depth} (exhaustive). [{time.time()-t0:.1f}s]")
    say(f"=== {label} DONE ===")
    return fired

if __name__ == "__main__":
    # B4 calibration: m=45 target must fire (depth 2, §79 certificate)
    ok = run(45, (1, 19, 20, 28, 30, 37), 2, "CALIB-m45-mustfire")
    if not ok:
        say("CALIBRATION FAILED — engine untrusted, aborting m=33 run.")
        sys.exit(1)
    # negative calibration: m=33 depth 2 must NOT fire (agentB105 exhaustive result)
    ok33d2 = run(33, (1, 4, 16, 22, 25, 31), 2, "CALIB-m33-d2-mustnotfire")
    if ok33d2:
        say("CALIBRATION ANOMALY: m=33 fired at depth 2 — contradicts §79 exhaustive no-fire; STOP, audit.")
        sys.exit(2)
    # the run: m=33 depth 3
    run(33, (1, 4, 16, 22, 25, 31), 3, "TARGET-m33-d3")
