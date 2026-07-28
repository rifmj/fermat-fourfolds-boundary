#!/usr/bin/env python3
"""Independent reimplementation of the census (second implementation, bundled).

Written for the ODD census and, since the multiplicity fix, used for the EVEN key levels as well
(its decomposability test is multiplicity-aware: the self-paired m/2 needs multiplicity two).

Written after the fact as an algorithmically independent cross-check of census_scan_v2.py: no code
is shared with the engine. Differences: full-unit profiles (v2 uses a half-unit system), numpy
chunked profile computation (v2 uses byte-packed arrays), and independently written classifiers
(pair / quasi / standard / star-split / canonizer). For every level it recomputes the census from
scratch and, when the witness receipt is present, ASSERTS agreement with it orbit-tally by
orbit-tally and survivor by survivor.

Usage: python3 census_independent.py [m ...]   (default: the 89-level census list)
"""
import sys, os, json, itertools
from math import gcd
from collections import defaultdict

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
WITNESS = HERE.rsplit('/code', 1)[0] + '/data/l4/census_witnesses_odd.json'


def units_full(m):
    return np.array([t for t in range(1, m) if gcd(t, m) == 1], dtype=np.int64)


def multisets(m, k):
    return np.array(list(itertools.combinations_with_replacement(range(1, m), k)),
                    dtype=np.int64)


def profiles(T, U, m, chunk=200000):
    outs = []
    for i in range(0, len(T), chunk):
        block = T[i:i + chunk]                    # (n, k)
        pr = (block[:, :, None] * U[None, None, :]) % m
        outs.append(pr.sum(axis=1).astype(np.int32))   # (n, |U|)
    return np.concatenate(outs) if outs else np.empty((0, len(U)), np.int32)


def grade3_sextuples(m):
    U = units_full(m)
    T = multisets(m, 3)
    P = profiles(T, U, m)
    buckets = defaultdict(list)
    for row, prof in zip(T, P):
        buckets[prof.tobytes()].append(tuple(int(x) for x in row))
    target = np.full(len(U), 3 * m, dtype=np.int32)
    out = set()
    for key, lst in buckets.items():
        comp = (target - np.frombuffer(key, dtype=np.int32)).tobytes()
        if comp in buckets:
            for c1 in lst:
                for c2 in buckets[comp]:
                    out.add(tuple(sorted(c1 + c2)))
    return out, U


def grade2_quads(m):
    U = units_full(m)
    T = multisets(m, 2)
    P = profiles(T, U, m)
    buckets = defaultdict(list)
    for row, prof in zip(T, P):
        buckets[prof.tobytes()].append(tuple(int(x) for x in row))
    target = np.full(len(U), 2 * m, dtype=np.int32)
    out = set()
    for key, lst in buckets.items():
        comp = (target - np.frombuffer(key, dtype=np.int32)).tobytes()
        if comp in buckets:
            for c1 in lst:
                for c2 in buckets[comp]:
                    out.add(tuple(sorted(c1 + c2)))
    return out


def canonize(a, m, Ulist):
    return min(tuple(sorted((t * x) % m for x in a)) for t in Ulist)


def classify(m):
    S3, U = grade3_sextuples(m)
    Ulist = [int(t) for t in U]
    reps = sorted({canonize(a, m, Ulist) for a in S3})
    S2 = grade2_quads(m)
    std = set()
    if m % 5 == 0 and m > 5:
        d = m // 5
        for x in range(1, m):
            if (5 * x) % m == 0:
                continue
            ent = [(x + j * d) % m for j in range(5)] + [(m - 5 * x) % m]
            if 0 in ent:
                continue
            std.add(canonize(tuple(ent), m, Ulist))
    tallies, survivors = defaultdict(int), []
    for a in reps:
        # EVEN-SAFE decomposability (multiplicity-aware): a vanishing pair {x, m-x} needs BOTH
        # entries present; the self-paired x = m/2 needs multiplicity >= 2. A plain set test is
        # unsound at even m (a single m/2 would read as a pair) -- regression: (1,29,35,43,45,57)
        # at m=70 is NOT decomposable.
        from collections import Counter as _C
        cnt = _C(a)
        dec = False
        for x in cnt:
            y = (m - x) % m
            if y == x:
                if cnt[x] >= 2:
                    dec = True
                    break
            elif y in cnt:
                dec = True
                break
        if dec:
            tallies["decomposable"] += 1
            continue
        quasi = False
        for k in range(1, (m + 1) // 2 + 1):
            T = sorted(a + (k, m - k))
            for cmb in itertools.combinations(range(1, 8), 3):
                cs = (0,) + cmb
                c = tuple(T[i] for i in cs)
                dd = tuple(T[i] for i in range(8) if i not in cs)
                if c in S2 and dd in S2:
                    quasi = True
                    break
            if quasi:
                break
        if quasi:
            tallies["quasi"] += 1
            continue
        if a in std:
            tallies["standard"] += 1
            continue
        split = False
        for cmb in itertools.combinations(range(6), 3):
            if 0 not in cmb:
                continue
            if sum(a[i] for i in cmb) % m == 0 and \
               sum(a[i] for i in range(6) if i not in cmb) % m == 0:
                split = True
                break
        if split:
            tallies["star-split"] += 1
        else:
            tallies["survivor"] += 1
            survivors.append(list(a))
    return {"m": m, "n_reps": len(reps), "tallies": dict(tallies), "survivors": survivors,
            "reps": [list(a) for a in reps]}


def main():
    ms = [int(x) for x in sys.argv[1:]] or [m for m in range(21, 200, 2) if m != 23]
    ref = None
    if os.path.exists(WITNESS):
        data = json.load(open(WITNESS))
        ref = {lev["m"]: lev for lev in data["levels"]}
    mismatches = 0
    for m in ms:
        res = classify(m)
        line = f"m={m}: reps={res['n_reps']} tallies={res['tallies']}"
        if ref and m in ref:
            ok = (res["n_reps"] == ref[m]["n_reps"] and res["tallies"] == ref[m]["tallies"])
            surv_ref = sorted(tuple(r["class"]) for r in ref[m]["orbits"]
                              if r["kind"] == "survivor")
            ok = ok and sorted(tuple(x) for x in res["survivors"]) == surv_ref
            line += f"   vs receipt: {'MATCH' if ok else 'MISMATCH'}"
            if not ok:
                mismatches += 1
        print(line, flush=True)
    if ref:
        assert mismatches == 0, f"{mismatches} level(s) disagree with the receipt"
        print("INDEPENDENT CENSUS: every requested level PRESENT IN the stored witness receipt "
              "matches it exactly; levels absent from the receipt are reported unverified "
              "(rep counts, tallies, survivor lists).")


if __name__ == "__main__":
    main()
