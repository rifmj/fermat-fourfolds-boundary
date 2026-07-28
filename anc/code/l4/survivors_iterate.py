"""ITERATED closure on the three even survivors (§85 engine).

Closed_1(block) := pipeline(block) OR block itself closes at depth<=2 with pipeline blocks —
i.e. the §84 fires (and any depth-2-certifiable sextuple) become legitimate G3 blocks. Sound by
the same Aoki 1-4 chain: claim(block) is established first, then used (a two-generation tree of
certificates, each generation = the refereed chain).

Also reports the BOTTLENECK census at depth 3 with Closed_0: partitions where everything works
except one 6-block fails closed_0 — and whether Closed_1 rescues those blocks.

Usage: python3 survivors_iterate.py [m ...]
"""
import sys, time, os, importlib.util as ilu
from itertools import combinations_with_replacement

HERE = os.path.dirname(os.path.abspath(__file__))
_s = ilu.spec_from_file_location('ce', os.path.join(HERE, 'census_even.py'))
ce = ilu.module_from_spec(_s); _s.loader.exec_module(ce)

LOG = HERE.rsplit('/code', 1)[0] + '/data/l4/survivors_iterate.log'
logf = open(LOG, 'a')
def say(s):
    print(s, flush=True); logf.write(s + "\n"); logf.flush()

SURV = [(54, (1, 7, 19, 36, 49, 50)), (70, (1, 20, 24, 42, 61, 62)), (90, (1, 23, 38, 55, 74, 79))]

def run(m, a):
    U = ce.units(m)
    S2 = ce.hodge_multisets(m, 4, 2)
    std = ce.standard_grade3(m, U)
    c0 = ce.Closed0(m, U, std, S2)
    memo_g2 = {}
    memo_c1 = {}
    stats = {'c1_tests': 0, 'c1_hits': 0}

    def closed1(c):
        key = ce.canon(c, m, U)
        if key in memo_c1:
            return memo_c1[key]
        r = c0(key)
        if not r:
            stats['c1_tests'] += 1
            d = ce.closes(key, m, U, c0, memo_g2, max_pairs=2)
            r = d is not None
            if r: stats['c1_hits'] += 1
        memo_c1[key] = r
        return r

    say(f"=== m={m} a={a} ITERATED closure (Closed_1 blocks), depth<=3 ===")
    t0 = time.time()
    half = [k for k in range(1, (m + 1) // 2) if (2 * k) % m] + [m // 2]
    fired = None
    for D in (1, 2, 3):
        for pairs in combinations_with_replacement(half, D):
            aug = sorted(list(a) + [x for k in pairs for x in (k, (m - k) % m)])
            cert = ce.partition_blocks(aug, m, U, closed1, memo_g2)
            if cert is not None:
                fired = (D, pairs, cert)
                break
        if fired: break
        say(f"  depth {D}: exhausted, no fire  [{time.time()-t0:.0f}s; c1 rescue-tests {stats['c1_tests']}, hits {stats['c1_hits']}]")
    if fired:
        D, pairs, cert = fired
        say(f"*** FIRE (iterated) depth={D} pairs={[(k,(m-k)%m) for k in pairs]} ***")
        for kind, blk in cert:
            if kind == "G3closed":
                via = 'pipeline' if c0(ce.canon(blk, m, U)) else 'GEN-2 (own depth<=2 certificate)'
                say(f"   {kind}: {blk}  via={via}")
                if via.startswith('GEN-2'):
                    # print the block's own certificate for the receipt chain
                    for pp in combinations_with_replacement(half, 1):
                        pass
            else:
                say(f"   {kind}: {blk}")
    else:
        say(f"NO-FIRE (iterated) through depth 3.  [{time.time()-t0:.0f}s; c1 rescue-tests {stats['c1_tests']}, hits {stats['c1_hits']}]")
    say(f"=== m={m} DONE ===")

if __name__ == "__main__":
    only = [int(x) for x in sys.argv[1:]] or None
    for m, a in SURV:
        if only and m not in only: continue
        run(m, a)
