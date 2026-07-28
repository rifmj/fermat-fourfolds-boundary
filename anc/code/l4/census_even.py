"""Even-m census (§82) — extends the odd-m open-boundary scan (§77/§79) to EVEN degrees.

Why a new file: the frozen odd engine's `has_pair` is UNSOUND for even m — the element m/2 is
self-paired (m − m/2 = m/2), so a class containing m/2 ONCE is falsely flagged decomposable.
Here `decomposable` is multiplicity-aware (Counter): a vanishing pair {x, m−x} requires BOTH x and
m−x present, and for x = m/2 requires multiplicity ≥ 2. Everything else mirrors the verified pipeline;
the FULL closure oracle (decomposable / standard AP-5 / quasi / *-split / two-pair §79) is applied,
and a brute-force calibrator proves the multiset engine against direct enumeration at small m.

Grade-3 standards are AP-5 ONLY for every parity (grade = (p+1)/2 = 3 ⟺ p = 5; Aoki's p=2
construction is a surface curve, not a fourfold sextuple) — so `standard_grade3` is unchanged.

Usage: python3 census_even.py --calibrate        # brute-force gate at m=6,8,10,12,14
       python3 census_even.py <m1> <m2> ...      # scan even m (idempotent; skips DONE)
"""
import sys, itertools, time
from array import array
from math import gcd
from collections import defaultdict, Counter

HERE = __file__.rsplit('/code/', 1)[0]
LOG = HERE + '/data/l4/census_even.log'


def units(m):
    return [t for t in range(1, m) if gcd(t, m) == 1]


def half_units(m):
    U, seen, H = units(m), set(), []
    for t in U:
        if t not in seen:
            H.append(t); seen.add(t); seen.add(m - t)
    return H


def hodge_multisets(m, k, grade):
    """All size-k grade-g Hodge multisets (entries 1..m-1, Σ≡0, Σ⟨t·⟩=g·m ∀ half-unit t)."""
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


def decomposable(a, m):
    """EVEN-SAFE: ∃ sub-multiset vanishing pair {x, m−x} (x=m/2 needs multiplicity ≥ 2)."""
    cnt = Counter(x % m for x in a)
    for x in cnt:
        y = (m - x) % m
        if y == x:
            if cnt[x] >= 2:
                return True
        elif y in cnt:
            return True
    return False


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
    """*-split: two zero-sum triples, one containing index 0 (§75)."""
    idx = range(6)
    for c in itertools.combinations(idx, 3):
        if 0 not in c:
            continue
        if sum(a[i] for i in c) % m == 0 and sum(a[i] for i in idx if i not in c) % m == 0:
            return True
    return False


def quasi(a, m, S2):
    """da Silva quasi-decomposable (EVEN-SAFE pair range incl. the doubled m/2 pair)."""
    ks = list(range(1, (m + 1) // 2))
    if m % 2 == 0:
        ks.append(m // 2)   # the (m/2, m/2) vanishing pair, valid for even m
    for k in ks:
        T = sorted(a + (k, (m - k) % m))
        for comb in itertools.combinations(range(1, 8), 3):
            cs = (0,) + comb
            c = tuple(T[i] for i in cs)
            d = tuple(T[i] for i in range(8) if i not in cs)
            if c in S2 and d in S2:
                return True
    return False


# ---- full closure oracle (pipeline + two-pair §79) via block partitioning ----

def grade_ok(c, m, g, U):
    return all(x % m for x in c) and all(sum((t * x) % m for x in c) == g * m for t in U)


class Closed0:
    """a sextuple is closed_0 iff decomposable / standard(AP-5) / quasi / *-split."""
    def __init__(self, m, U, std, S2):
        self.m, self.U, self.std, self.S2 = m, U, std, S2
        self.memo = {}

    def __call__(self, c):
        key = canon(c, self.m, self.U)
        if key in self.memo:
            return self.memo[key]
        m = self.m
        r = (decomposable(c, m) or key in self.std
             or splittable(tuple(c), m) or quasi(tuple(c), m, self.S2))
        self.memo[key] = r
        return r


def partition_blocks(elems, m, U, closed0, memo_g2):
    n = len(elems)
    if n == 0:
        return []
    first = elems[0]; rest = elems[1:]
    tgt = (m - first) % m
    if tgt in rest:
        r2 = list(rest); r2.remove(tgt)
        sub = partition_blocks(r2, m, U, closed0, memo_g2)
        if sub is not None:
            return [("PAIR", (first, tgt))] + sub
    for idx in itertools.combinations(range(len(rest)), 3):
        blk = (first,) + tuple(rest[i] for i in idx)
        if sum(blk) % m:
            continue
        key = tuple(sorted(blk))
        if key not in memo_g2:
            memo_g2[key] = grade_ok(key, m, 2, U)
        if memo_g2[key]:
            r2 = [rest[i] for i in range(len(rest)) if i not in idx]
            sub = partition_blocks(r2, m, U, closed0, memo_g2)
            if sub is not None:
                return [("G2", key)] + sub
    if n >= 6:
        for idx in itertools.combinations(range(len(rest)), 5):
            blk = (first,) + tuple(rest[i] for i in idx)
            if sum(blk) % m:
                continue
            key = tuple(sorted(blk))
            if grade_ok(key, m, 3, U) and closed0(key):
                r2 = [rest[i] for i in range(len(rest)) if i not in idx]
                sub = partition_blocks(r2, m, U, closed0, memo_g2)
                if sub is not None:
                    return [("G3closed", key)] + sub
    return None


def closes(a, m, U, closed0, memo_g2, max_pairs=2):
    """Minimal augmentation-pair depth (0..max_pairs) at which a closes; None if open."""
    if closed0(a):
        return 0
    half = [k for k in range(1, (m + 1) // 2) if (2 * k) % m]
    if m % 2 == 0:
        half.append(m // 2)
    for d in range(1, max_pairs + 1):
        for pairs in itertools.combinations_with_replacement(half, d):
            aug = sorted(list(a) + [x for k in pairs for x in (k, (m - k) % m)])
            if partition_blocks(aug, m, U, closed0, memo_g2) is not None:
                return d
    return None


def prim_root(p):
    for g in range(2, p):
        x, seen = 1, set()
        for _ in range(p - 1):
            x = x * g % p; seen.add(x)
        if len(seen) == p - 1:
            return g


def eig_degree(a, m, nprimes=5):
    import mpmath as mp
    mp.mp.dps = 25
    U = units(m); degs = []
    p, found = m + 1, 0
    while found < nprimes and p < 60 * m:
        if p % m == 1 and all(p % q for q in range(2, int(p ** .5) + 1)):
            found += 1
            g = prim_root(p)
            ind, x = {}, 1
            for kk in range(p - 1):
                ind[x] = kk; x = x * g % p
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


# ---------------- brute-force calibration ----------------

def brute_reps(m, grade=3):
    """Direct enumeration of grade-g Hodge orbit reps + total sextuple count (small m only)."""
    U = units(m)
    tot = 0; reps = set()
    for a in itertools.combinations_with_replacement(range(1, m), 6):
        if sum(a) % m:
            continue
        if all(sum((t * ai) % m for ai in a) == grade * m for t in U):
            tot += 1
            reps.add(canon(a, m, U))
    return tot, reps


def calibrate():
    logf = open(LOG, 'a')
    def say(s):
        print(s); logf.write(s + "\n"); logf.flush()
    say(f"=== CALIBRATION (brute vs engine) {time.strftime('%Y-%m-%d')} ===")
    ok = True
    for m in (6, 8, 10, 12, 14):
        U = units(m)
        bt, br = brute_reps(m, 3)
        eng = {canon(a, m, U) for a in hodge_multisets(m, 6, 3)}
        et = len(hodge_multisets(m, 6, 3))
        match_reps = (br == eng)
        # decomposable soundness: brute vanishing-pair test vs even-safe decomposable
        dec_ok = True
        for a in br:
            bpair = any((a[i] + a[j]) % m == 0 for i in range(6) for j in range(i + 1, 6))
            if bpair != decomposable(a, m):
                dec_ok = False; break
        say(f"m={m}: brute_reps={len(br)} engine_reps={len(eng)} reps_match={match_reps} "
            f"brute_tot={bt} decomp_sound={dec_ok}")
        ok = ok and match_reps and dec_ok
    say(f"CALIBRATION {'PASS' if ok else 'FAIL'}")
    return ok


def scan(m, logf):
    def say(s):
        print(s); logf.write(s + "\n"); logf.flush()
    U = units(m)
    S3 = hodge_multisets(m, 6, 3)
    S2 = hodge_multisets(m, 4, 2)
    reps = sorted({canon(a, m, U) for a in S3})
    std = standard_grade3(m, U)
    closed0 = Closed0(m, U, std, S2)
    memo_g2 = {}
    buckets = Counter()
    opens = []
    for a in reps:
        d = closes(a, m, U, closed0, memo_g2, max_pairs=2)
        buckets[d] += 1
        if d is None:
            opens.append(a)
    say(f"m={m}: reps={len(reps)} closed@0={buckets[0]} closed@1={buckets[1]} "
        f"closed@2={buckets[2]} OPEN={len(opens)}")
    for a in opens:
        g = gcd(gcd(gcd(a[0], a[1]), gcd(a[2], a[3])), gcd(a[4], a[5]))
        induced = f"content-gcd={g} -> reduces to level {m//g}" if g > 1 else "content-gcd=1 (primitive candidate)"
        dg = eig_degree(a, m)
        say(f"  m={m} OPEN {a}  {induced}  eig-field-degree(max 2 primes)={dg}")
    say(f"=== m={m} DONE ===")


if __name__ == "__main__":
    if "--calibrate" in sys.argv:
        sys.exit(0 if calibrate() else 1)
    ms = [int(x) for x in sys.argv[1:] if x.isdigit()]
    try:
        done = {int(l.split("m=")[1].split()[0]) for l in open(LOG)
                if l.startswith("=== m=") and "DONE" in l}
    except FileNotFoundError:
        done = set()
    with open(LOG, "a") as logf:
        for m in ms:
            if m in done:
                print(f"m={m}: already DONE, skip"); continue
            t0 = time.time()
            scan(m, logf)
            print(f"  [m={m} took {time.time()-t0:.1f}s]")
