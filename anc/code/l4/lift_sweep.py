"""LIFT SWEEP over the even-sector primitives (§83 genre, systematic; §84 engine).

For each open primitive beta@m and lift factor e: test whether e*beta closes at level L=e*m by the
depth-<=D closure oracle (pipeline predicates + {pair, grade-2, closed_0-sextuple} partitions).
By the §83 descent lemma (claim level-transparency), a fire at ANY lift closes beta itself.

Cheap by design: a single lifted class needs only S2@L (quadruple supply) + predicates — never the
full grade-3 census of level L. S2/std/Closed0 memoized per level.

Usage: python3 lift_sweep.py e depth [m1 m2 ...]   (default: all 21 even primitives)
Idempotent log: data/l4/lift_sweep.log
"""
import sys, time, importlib.util as ilu, os
from itertools import combinations_with_replacement

HERE = os.path.dirname(os.path.abspath(__file__))
_s = ilu.spec_from_file_location('ce', os.path.join(HERE, 'census_even.py'))
ce = ilu.module_from_spec(_s); _s.loader.exec_module(ce)

LOG = HERE.rsplit('/code', 1)[0] + '/data/l4/lift_sweep.log'
logf = open(LOG, 'a')
def say(s):
    print(s, flush=True); logf.write(s + "\n"); logf.flush()

TARGETS = [
 (50, (1,7,27,30,41,44)),
 (54, (1,7,19,36,49,50)), (54, (1,7,24,38,41,51)), (54, (1,7,36,38,39,41)),
 (66, (1,8,23,52,54,60)), (66, (1,25,31,37,49,55)),
 (70, (1,6,43,45,57,58)), (70, (1,20,24,42,61,62)),
 (72, (1,10,37,50,54,64)), (72, (1,26,37,40,54,58)),
 (78, (1,12,43,55,60,63)), (78, (1,20,43,45,62,63)), (78, (1,28,42,45,54,64)),
 (90, (1,8,26,62,85,88)), (90, (1,23,38,55,74,79)), (90, (1,38,46,55,56,74)),
 (102, (1,14,16,82,93,100)), (102, (1,16,28,62,99,100)), (102, (1,40,52,69,70,74)), (102, (1,46,52,57,70,80)),
 (108, (1,44,55,58,82,84)),
]

_level_cache = {}
def level_ctx(L):
    if L not in _level_cache:
        t0 = time.time()
        U = ce.units(L)
        S2 = ce.hodge_multisets(L, 4, 2)
        std = ce.standard_grade3(L, U)
        _level_cache[L] = (U, S2, std)
        say(f"  [level {L}: |S2|={len(S2)} built in {time.time()-t0:.0f}s]")
    return _level_cache[L]

def extract_cert(a, L, U, c0, memo, maxd=2):
    half = [k for k in range(1, (L + 1) // 2) if (2 * k) % L] + ([L // 2] if L % 2 == 0 else [])
    for d in range(1, maxd + 1):
        for pairs in combinations_with_replacement(half, d):
            aug = sorted(list(a) + [x for k in pairs for x in (k, (L - k) % L)])
            cert = ce.partition_blocks(aug, L, U, c0, memo)
            if cert is not None:
                return pairs, cert
    return None

def run(e, depth, only_ms=None):
    import re
    done = set()
    try:
        for ln in open(LOG):
            mm = re.match(r"RESULT (\d+) (\([\d, ]+\)) (\d+) ", ln)
            if mm:
                done.add((int(mm.group(1)), tuple(int(x) for x in re.findall(r"\d+", mm.group(2))), int(mm.group(3))))
    except FileNotFoundError:
        pass
    say(f"=== LIFT SWEEP e={e} depth<={depth} ({time.strftime('%F %T')}) ===")
    for m, b in TARGETS:
        if only_ms and m not in only_ms:
            continue
        if (m, b, e) in done:
            say(f"RESULT-SKIP {m} {b} {e} (already done)"); continue
        L = e * m
        lifted = tuple(sorted((e * x) % L for x in b))
        U, S2, std = level_ctx(L)
        if not ce.grade_ok(lifted, L, 3, U):
            say(f"RESULT {m} {b} {e} SANITY-FAIL lifted={lifted}"); continue
        c0 = ce.Closed0(L, U, std, S2)
        memo = {}
        t0 = time.time()
        d = ce.closes(lifted, L, U, c0, memo, max_pairs=depth)
        if d is None:
            say(f"RESULT {m} {b} {e} NO-FIRE depth<={depth} lifted={lifted}@{L}  [{time.time()-t0:.0f}s]")
        else:
            pairs, cert = extract_cert(lifted, L, U, c0, memo, maxd=d)
            say(f"RESULT {m} {b} {e} *** FIRE depth={d} *** lifted={lifted}@{L}  [{time.time()-t0:.0f}s]")
            say(f"  pairs={[(k, (L-k)%L) for k in pairs]}")
            for kind, blk in cert:
                extra = ""
                if kind == "G3closed":
                    reasons = []
                    if ce.decomposable(blk, L): reasons.append("decomposable")
                    if ce.canon(blk, L, U) in std: reasons.append("standard")
                    if ce.splittable(tuple(blk), L): reasons.append("*-split")
                    if ce.quasi(tuple(blk), L, S2): reasons.append("quasi")
                    extra = f"  via={reasons}"
                say(f"   {kind}: {blk}{extra}")
    say(f"=== SWEEP e={e} DONE ===")

if __name__ == "__main__":
    e = int(sys.argv[1]); depth = int(sys.argv[2])
    only = [int(x) for x in sys.argv[3:]] or None
    run(e, depth, only)
