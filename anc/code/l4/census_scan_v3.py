"""Census scan v3 — the DEFINITIVE pipeline (§85 consolidation): even-safe predicates +
ITERATED closure (Closed₁) + transport/ledger post-processing.

Per m (any parity):
  grade-3 Hodge orbit reps  [meet-in-middle, even-safe]
    → decomposable (multiplicity-aware; m/2 self-pair handled)     [induced]
    → standard (AP-5)                                              [Aoki Thm 2-1 (+inflation)]
    → quasi (incl. the (m/2,m/2) pair)                             [da Silva]
    → *-split                                                      [§75]
    → closes at depth ≤ DEPTH with Closed₁ blocks                  [§§79/83/84/85 Aoki chain,
      (blocks may carry their own depth-≤2 certificates)            two-generation trees]
    → TRANSPORT: content-gcd reduction hits the CLOSED LEDGER      [§83 inflation/descent]
    → TRULY OPEN survivors (+ledger-annotated)

Ledger: data/l4/CLOSED_LEDGER.tsv (deep closures with §-provenance; canonical orbit reps).
Usage: python3 census_scan_v3.py <m1> <m2> ...   [--depth N (default 3)]
Idempotent log: data/l4/census_scan_v3.log
"""
import sys, os, time, re, importlib.util as ilu
from math import gcd

HERE = os.path.dirname(os.path.abspath(__file__))
_s = ilu.spec_from_file_location('ce', os.path.join(HERE, 'census_even.py'))
ce = ilu.module_from_spec(_s); _s.loader.exec_module(ce)

DATA = HERE.rsplit('/code', 1)[0] + '/data/l4'
LOG = DATA + '/census_scan_v3.log'
LEDGER = DATA + '/CLOSED_LEDGER.tsv'


def load_ledger():
    led = {}
    try:
        for ln in open(LEDGER):
            if ln.startswith('#') or not ln.strip():
                continue
            parts = ln.rstrip('\n').split('\t')
            m = int(parts[0])
            cls = tuple(int(x) for x in re.findall(r'\d+', parts[1]))
            if len(cls) == 6:
                led[(m, cls)] = parts[2] + ' ' + parts[3]
    except FileNotFoundError:
        pass
    return led


def scan(m, depth, logf):
    def say(s):
        print(s, flush=True); logf.write(s + "\n"); logf.flush()
    led = load_ledger()
    U = ce.units(m)
    S3 = ce.hodge_multisets(m, 6, 3)
    S2 = ce.hodge_multisets(m, 4, 2)
    std = ce.standard_grade3(m, U)
    reps = sorted({ce.canon(a, m, U) for a in S3})
    c0 = ce.Closed0(m, U, std, S2)
    memo_g2, memo_c1 = {}, {}

    def closed1(c):
        key = ce.canon(c, m, U)
        if key in memo_c1:
            return memo_c1[key]
        r = c0(key) or (ce.closes(key, m, U, c0, memo_g2, max_pairs=2) is not None)
        memo_c1[key] = r
        return r

    counts = {'base': 0, 'deep': 0, 'transport': 0}
    opens = []
    for a in reps:
        if c0(a):
            counts['base'] += 1; continue
        d = ce.closes(a, m, U, closed1, memo_g2, max_pairs=depth)
        if d is not None:
            counts['deep'] += 1; continue
        g = a[0]
        for x in a[1:]:
            g = gcd(g, x)
        g = gcd(g, m)
        if g > 1:
            red = tuple(sorted(x // g for x in a))
            red = ce.canon(red, m // g, ce.units(m // g))
            if (m // g, red) in led:
                counts['transport'] += 1
                continue
        opens.append(a)
    say(f"m={m}: reps={len(reps)} base-closed={counts['base']} deep-closed(d<={depth},iter)={counts['deep']} "
        f"transport-closed={counts['transport']} OPEN={len(opens)}")
    for a in opens:
        g = a[0]
        for x in a[1:]:
            g = gcd(g, x)
        g = gcd(g, m)
        note = f"content-gcd={g}" + (f" -> level {m//g} (NOT in ledger)" if g > 1 else " (primitive)")
        known = " [KNOWN-OPEN]" if (m, a) in {(70,(1,20,24,42,61,62)),(110,(1,24,62,71,81,91)),(110,(1,31,55,71,81,91)),(114,(1,7,78,79,86,91)),(114,(1,13,43,72,103,110)),(114,(1,13,43,80,102,103))} else ""
        say(f"  m={m} OPEN {a}  {note}{known}")
    say(f"=== m={m} DONE (v3 d{depth}) ===")


if __name__ == "__main__":
    args = sys.argv[1:]
    depth = 3
    if '--depth' in args:
        i = args.index('--depth'); depth = int(args[i + 1]); del args[i:i + 2]
    ms = [int(x) for x in args]
    try:
        done = {int(l.split('m=')[1].split()[0]) for l in open(LOG)
                if l.startswith('=== m=') and 'DONE' in l}
    except FileNotFoundError:
        done = set()
    with open(LOG, 'a') as logf:
        for m in ms:
            if m in done:
                print(f"m={m}: already DONE, skip"); continue
            t0 = time.time()
            scan(m, depth, logf)
            print(f"  [m={m} took {time.time()-t0:.0f}s]")
