"""Census scan v2 — the FULL open-boundary pipeline per odd m (companion-note engine):

  grade-3 Hodge orbit reps
    → decomposable (contains vanishing pair)                  [algebraic: induced]
    → quasi-decomposable ((2,2)-split after adding a pair)    [algebraic: induced, da Silva (P2)]
    → standard (Aoki AP-5: {x, x+m/5,…,−5x}, 5|m, m>5)        [algebraic: Aoki 1987]
    → *-splittable (two zero-sum triples)                     [algebraic: §75 join/Lefschetz theorem]
    → TRULY OPEN survivors  + eigenvalue-field degree (multi-prime, D8)

Memory: meet-in-middle profiles stored on HALF the units (the −t coordinate is determined:
Σ⟨−t c_i⟩ = k·m − Σ⟨t c_i⟩) and encoded as uint16 bytes — fits all odd m ≤ 199.
Idempotent: skips m already marked DONE in the log (append-driven, safe to relaunch).
Usage: python3 census_scan_v2.py <m1> <m2> ...    (calibration anchors: 21, 27, 33)
"""
import sys, itertools
from array import array
from math import gcd
from collections import defaultdict

LOG = __file__.rsplit('/code/', 1)[0] + '/data/l4/census_scan_v2.log'


def units(m):
    return [t for t in range(1, m) if gcd(t, m) == 1]


def half_units(m):
    U, seen, H = units(m), set(), []
    for t in U:
        if t not in seen:
            H.append(t)
            seen.add(t)
            seen.add(m - t)
    return H


def hodge_multisets(m, k, grade):
    H = half_units(m)
    k1, k2 = k // 2, k - k // 2

    def profs(kk):
        d = defaultdict(list)
        for c in itertools.combinations_with_replacement(range(1, m), kk):
            v = array('H', (sum((t * ai) % m for ai in c) for t in H)).tobytes()
            d[v].append(c)
        return d

    A = profs(k1)
    B = A if k2 == k1 else profs(k2)
    target = grade * m
    out = set()
    for v, lst in A.items():
        va = array('H'); va.frombytes(v)
        w = array('H', (target - x for x in va)).tobytes()
        if w in B:
            for c1 in lst:
                for c2 in B[w]:
                    out.add(tuple(sorted(c1 + c2)))
    return out


def canon(a, m, U):
    return min(tuple(sorted((t * ai) % m for ai in a)) for t in U)


def has_pair(a, m):
    s = set(a)
    return any((m - x) in s for x in s)


def standard_grade3(m, U):
    out = set()
    if m % 5 == 0 and m > 5:
        d = m // 5
        for i in range(1, m):
            if (5 * i) % m == 0:
                continue
            e = [(i + k * d) % m for k in range(5)] + [(m - 5 * i) % m]
            if all(x != 0 for x in e):
                out.add(canon(tuple(sorted(e)), m, U))
    return out


def splittable(a, m):
    idx = range(6)
    for c in itertools.combinations(idx, 3):
        if 0 not in c:
            continue
        if sum(a[i] for i in c) % m == 0 and sum(a[i] for i in idx if i not in c) % m == 0:
            return True
    return False


def quasi(a, m, S2):
    for k in range(1, (m + 1) // 2):
        T = sorted(a + (k, m - k))
        for comb in itertools.combinations(range(1, 8), 3):
            cs = (0,) + comb
            c = tuple(T[i] for i in cs)
            d = tuple(T[i] for i in range(8) if i not in cs)
            if c in S2 and d in S2:
                return True
    return False


def prim_root(p):
    for g in range(2, p):
        x, seen = 1, set()
        for _ in range(p - 1):
            x = x * g % p
            seen.add(x)
        if len(seen) == p - 1:
            return g


def eig_degree(a, m, nprimes=5):
    import mpmath as mp
    mp.mp.dps = 25
    U = units(m)
    degs = []
    p, found = m + 1, 0
    while found < nprimes and p < 40 * m:
        if p % m == 1 and all(p % q for q in range(2, int(p ** .5) + 1)):
            found += 1
            g = prim_root(p)
            ind, x = {}, 1
            for kk in range(p - 1):
                ind[x] = kk
                x = x * g % p
            zp = [mp.e ** (2j * mp.pi * i / p) for i in range(p)]
            zm = [mp.e ** (2j * mp.pi * kk / m) for kk in range(m)]
            G = [mp.mpc(0)] * m
            for xx in range(1, p):
                kk = ind[xx]
                for j in range(m):
                    G[j] += zm[(j * kk) % m] * zp[xx]
            vals = set()
            for t in U:
                u = mp.mpc(1)
                for ai in a:
                    u *= G[(t * ai) % m]
                u /= mp.mpf(p) ** 3
                vals.add((round(float(u.real), 7), round(float(u.imag), 7)))
            degs.append(len(vals))
        p += 1
    return max(degs) if degs else -1


def scan(m, logf):
    U = units(m)
    S3 = hodge_multisets(m, 6, 3)
    S2set = hodge_multisets(m, 4, 2)
    reps = sorted({canon(a, m, U) for a in S3})
    dec = [a for a in reps if has_pair(a, m)]
    indec = [a for a in reps if not has_pair(a, m)]
    q = [a for a in indec if quasi(a, m, S2set)]
    nq = [a for a in indec if a not in set(q)]
    std = standard_grade3(m, U)
    after_std = [a for a in nq if a not in std]
    split_cl = [a for a in after_std if splittable(a, m)]
    open_true = [a for a in after_std if not splittable(a, m)]
    line = (f"m={m}: reps={len(reps)} dec={len(dec)} indec={len(indec)} quasi={len(q)} "
            f"nonquasi={len(nq)} std-covered={len(nq)-len(after_std)} "
            f"split-covered={len(split_cl)} TRULY-OPEN={len(open_true)}")
    print(line); logf.write(line + "\n")
    for a in split_cl:
        s = f"  m={m} SPLIT-CLOSED {a}"
        print(s); logf.write(s + "\n")
    for a in open_true:
        diag = [l for l in (3, 5, 7, 11, 13) if m % l == 0 and len({ai % l for ai in a}) == 1]
        dg = eig_degree(a, m)
        s = (f"  m={m} OPEN {a}  diag={diag or 'none'}  eig-field-degree(max over 2 primes)={dg}"
             f"  {'IMAG-QUADRATIC candidate' if dg == 2 else 'BEYOND imaginary quadratic' if dg > 2 else ''}")
        print(s); logf.write(s + "\n")
    logf.write(f"=== m={m} DONE ===\n"); logf.flush()


if __name__ == "__main__":
    ms = [int(x) for x in sys.argv[1:]]
    try:
        done = set()
        for ln in open(LOG):
            if ln.startswith("=== m=") and "DONE" in ln:
                done.add(int(ln.split("m=")[1].split()[0]))
    except FileNotFoundError:
        done = set()
    with open(LOG, "a") as logf:
        for m in ms:
            if m in done:
                print(f"m={m}: already DONE, skip")
                continue
            import time
            t0 = time.time()
            scan(m, logf)
            print(f"  [m={m} took {time.time()-t0:.1f}s]")
