"""fast_close — performance pass on the closure oracle (§87 engine): numpy grade checks over
HALF-units (exact: sums over t and m−t are complementary, so Σ_t⟨t·c⟩ = g·m on half the units
⟺ the full ∀t condition), global block memoization, and multiprocessing over the leading pair.

Target: depth-4 iterated closure at m≈168 (~2.2M augmentations) in minutes.
CALIBRATION GATE (B4, two-sided) runs first on every invocation:
  must-fire: m=45 two-pair (§79), m=50 depth-4 (§84), m=54 iterated-d3 (§85)
  must-not-fire: m=33 depth-2 (§79/§81), 168#1 iterated depth-3 (§86)
Usage: python3 fast_close.py <m> <a0,a1,...,a5> <depth> <gen>   (gen: 0=pipeline blocks, 1=Closed1)
"""
import sys, os, time
import numpy as np
import importlib.util as ilu
from itertools import combinations, combinations_with_replacement
from math import gcd
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
_s = ilu.spec_from_file_location('ce', os.path.join(HERE, 'census_even.py'))
ce = ilu.module_from_spec(_s); _s.loader.exec_module(ce)

# ---------------- fast level context ----------------
class Ctx:
    def __init__(self, m, gen):
        self.m = m; self.gen = gen
        self.U = ce.units(m)
        self.H = [t for t in self.U if t <= m // 2]          # half-units
        # P[x] = vector of (t*x mod m) over half-units, x = 0..m-1 (row 0 unused)
        P = np.zeros((m, len(self.H)), dtype=np.int64)
        for x in range(1, m):
            P[x] = [(t * x) % m for t in self.H]
        self.P = P
        self.S2 = ce.hodge_multisets(m, 4, 2)
        self.std = ce.standard_grade3(m, self.U)
        self.c0 = ce.Closed0(m, self.U, self.std, self.S2)
        self.memo_blk = {}     # block tuple -> bool (grade-2 ok for 4s; grade3+closed for 6s)
        self.memo_g2_ce = {}   # for ce.closes inner calls (gen-1 blocks)

    def grade_ok(self, c, g):
        if not all(x % self.m for x in c):
            return False
        return bool((self.P[list(c)].sum(axis=0) == g * self.m).all())

    def ok4(self, c):
        r = self.memo_blk.get(c)
        if r is None:
            r = self.grade_ok(c, 2)
            self.memo_blk[c] = r
        return r

    def ok6(self, c):
        key = ('6',) + c
        r = self.memo_blk.get(key)
        if r is None:
            if not self.grade_ok(c, 3):
                r = False
            else:
                can = ce.canon(c, self.m, self.U)
                r = self.c0(can)
                if not r and self.gen >= 1:
                    r = ce.closes(can, self.m, self.U, self.c0, self.memo_g2_ce, max_pairs=2) is not None
            self.memo_blk[key] = r
        return r

def partition_ok(elems, ctx):
    n = len(elems)
    if n == 0:
        return True
    first = elems[0]; rest = elems[1:]
    m = ctx.m
    tgt = (m - first) % m
    if tgt in rest:
        r2 = list(rest); r2.remove(tgt)
        if partition_ok(r2, ctx):
            return True
    for idx in combinations(range(len(rest)), 3):
        blk = (first,) + tuple(rest[i] for i in idx)
        if sum(blk) % m:
            continue
        if ctx.ok4(tuple(sorted(blk))):
            r2 = [rest[i] for i in range(len(rest)) if i not in idx]
            if partition_ok(r2, ctx):
                return True
    if n >= 6:
        for idx in combinations(range(len(rest)), 5):
            blk = (first,) + tuple(rest[i] for i in idx)
            if sum(blk) % m:
                continue
            if ctx.ok6(tuple(sorted(blk))):
                r2 = [rest[i] for i in range(len(rest)) if i not in idx]
                if partition_ok(r2, ctx):
                    return True
    return False

_G = {}
def _init(m, a, gen, depth):
    _G['ctx'] = Ctx(m, gen); _G['a'] = a; _G['depth'] = depth
    _G['half'] = [k for k in range(1, (m + 1) // 2) if (2 * k) % m] + ([m // 2] if m % 2 == 0 else [])

def _work(first_idx):
    ctx = _G['ctx']; a = _G['a']; depth = _G['depth']; half = _G['half']
    m = ctx.m; k1 = half[first_idx]
    hits = []
    # enumerate remaining pairs (multisets) with indices >= first_idx, total depth pairs
    rest_depth = depth - 1
    for combo in combinations_with_replacement(range(first_idx, len(half)), rest_depth):
        pairs = (k1,) + tuple(half[i] for i in combo)
        aug = sorted(list(a) + [x for k in pairs for x in (k, (m - k) % m)])
        if partition_ok(aug, ctx):
            hits.append(pairs)
            break
    return hits

def closes_fast(m, a, depth, gen, procs=8):
    half = [k for k in range(1, (m + 1) // 2) if (2 * k) % m] + ([m // 2] if m % 2 == 0 else [])
    # depths 1..depth-1 serially (cheap), depth parallel over leading pair
    ctx = Ctx(m, gen)
    for D in range(1, depth):
        for pairs in combinations_with_replacement(half, D):
            aug = sorted(list(a) + [x for k in pairs for x in (k, (m - k) % m)])
            if partition_ok(aug, ctx):
                return D, pairs
    with Pool(procs, initializer=_init, initargs=(m, a, gen, depth)) as pool:
        for res in pool.imap_unordered(_work, range(len(half)), chunksize=1):
            if res:
                pool.terminate()
                return depth, res[0]
    return None, None

def calibrate():
    ok = True
    t0 = time.time()
    d, p = closes_fast(45, (1, 19, 20, 28, 30, 37), 2, 0, procs=4)
    print(f"CALIB m=45 two-pair: {'FIRE d=%s' % d if d else 'no-fire'} (must fire d=2)"); ok &= (d == 2)
    d, p = closes_fast(50, (1, 7, 27, 30, 41, 44), 4, 0, procs=8)
    print(f"CALIB m=50 depth-4: {'FIRE d=%s' % d if d else 'no-fire'} (must fire d<=4)"); ok &= (d is not None)
    d, p = closes_fast(54, (1, 7, 19, 36, 49, 50), 3, 1, procs=4)
    print(f"CALIB m=54 iterated-d3: {'FIRE d=%s' % d if d else 'no-fire'} (must fire d=3)"); ok &= (d == 3)
    d, p = closes_fast(33, (1, 4, 16, 22, 25, 31), 2, 0, procs=4)
    print(f"CALIB m=33 depth-2: {'FIRE' if d else 'NO-FIRE'} (must NOT fire)"); ok &= (d is None)
    d, p = closes_fast(168, (1, 25, 79, 121, 127, 151), 3, 1, procs=8)
    print(f"CALIB 168#1 iterated-d3: {'FIRE' if d else 'NO-FIRE'} (must NOT fire)"); ok &= (d is None)
    print(f"CALIBRATION {'PASS' if ok else 'FAIL'}  [{time.time()-t0:.0f}s]")
    return ok

if __name__ == "__main__":
    if sys.argv[1:] == ['--calibrate'] or not sys.argv[1:]:
        sys.exit(0 if calibrate() else 1)
    m = int(sys.argv[1]); a = tuple(int(x) for x in sys.argv[2].split(','))
    depth = int(sys.argv[3]); gen = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    t0 = time.time()
    d, pairs = closes_fast(m, a, depth, gen)
    if d:
        print(f"*** FIRE d={d} pairs={pairs} ***  [{time.time()-t0:.0f}s]")
    else:
        print(f"NO-FIRE depth<={depth} gen={gen}  [{time.time()-t0:.0f}s]")
