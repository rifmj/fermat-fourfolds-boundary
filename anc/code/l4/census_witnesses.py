#!/usr/bin/env python3
"""Per-orbit closure witnesses for the odd census (Theorem B receipt, witness tier).

For every odd level of the census list and every Galois-orbit representative of a grade-3 Hodge
sextuple, emit the classification together with an EXPLICIT witness, and VERIFY the witness on the
spot (every check is an assert):

  decomposable : a vanishing pair {x, m-x} inside the multiset
  quasi        : k and a split  a + {k,m-k} = c + d  into two grade-2 Hodge quadruples
  standard     : the parameter x with  a ~ sigma_{5,x}  (as Galois orbits)
  star-split   : two zero-sum triples  a = T1 + T2
  survivor     : one of the seven orbits closed by Theorems A'/A'' of the paper -- verified by
                 re-establishing the NEGATIVE screenings live (no vanishing pair, no quasi
                 witness at any k, not standard, no zero-sum split), so the terminal label is a
                 re-checked certificate, not a label

Output: data/l4/census_witnesses_odd.json  (per level: reps, tallies, witness records).
Usage:  python3 census_witnesses.py [m ...]      (default: the 89-level census list)
        python3 census_witnesses.py --verify     (re-check every witness stored in the JSON)
"""
import sys, os, json, itertools
from math import gcd
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from census_scan_v2 import units, hodge_multisets, canon, has_pair, standard_grade3

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = HERE.rsplit('/code', 1)[0] + '/data/l4/census_witnesses_odd.json'

SURVIVOR_LABELS = {
    (33,): "closed by Thm A'' (level-66 lift)",
    (45,): "closed by Thm A' (two-pair)",
    (105,): "closed by Thm A' (two-pair)",
    (99,): "induced copy of the m=33 class (content 3); closes by transport from Thm A''",
    (135,): "induced copy of the m=45 class (content 3); closes by transport from Thm A'",
    (165,): "induced copy of the m=33 class (content 5); closes by transport from Thm A''",
}


def grade_ok(c, m, g):
    for t in range(1, m):
        if gcd(t, m) != 1:
            continue
        if sum(((t * x) % m if (t * x) % m else m) for x in c) != g * m:
            return False
    return True


def find_pair(a, m):
    s = set(a)
    for x in a:
        if (m - x) in s:
            return (x, m - x)
    return None


def find_split(a, m):
    for cmb in itertools.combinations(range(6), 3):
        if 0 not in cmb:
            continue
        T1 = tuple(a[i] for i in cmb)
        T2 = tuple(a[i] for i in range(6) if i not in cmb)
        if sum(T1) % m == 0 and sum(T2) % m == 0:
            return (T1, T2)
    return None


def find_quasi(a, m, S2):
    for k in range(1, (m + 1) // 2 + 1):
        if (2 * k) % m == 0 and k != m - k:
            continue
        T = sorted(a + (k, m - k))
        for cmb in itertools.combinations(range(1, 8), 3):
            cs = (0,) + cmb
            c = tuple(T[i] for i in cs)
            d = tuple(T[i] for i in range(8) if i not in cs)
            if c in S2 and d in S2:
                return (k, c, d)
    return None


def find_standard(a, m, U):
    if m % 5 or m <= 5:
        return None
    d = m // 5
    for x in range(1, m):
        if (5 * x) % m == 0:
            continue
        ent = sorted([(x + j * d) % m for j in range(5)] + [(m - 5 * x) % m])
        if 0 in ent:
            continue
        if canon(tuple(ent), m, U) == a:
            return x
    return None


_NEG = {}


def _neg_ctx(m):
    """Per-level context (units, grade-2 quadruples, standard set) for survivor negatives."""
    if m not in _NEG:
        U = units(m)
        _NEG[m] = (U, hodge_multisets(m, 4, 2), standard_grade3(m, U))
    return _NEG[m]


def verify_witness(m, a, rec):
    kind = rec["kind"]
    if kind == "decomposable":
        x, y = rec["pair"]
        assert (x + y) % m == 0
        from collections import Counter as _C
        cnt = _C(a)
        if x == y:
            assert cnt[x] >= 2
        else:
            assert cnt[x] >= 1 and cnt[y] >= 1
    elif kind == "quasi":
        k, c, d = rec["k"], tuple(rec["c"]), tuple(rec["d"])
        assert sorted(a + (k, m - k)) == sorted(c + d)
        assert grade_ok(c, m, 2) and grade_ok(d, m, 2)
    elif kind == "standard":
        x = rec["x"]
        dgt = m // 5
        ent = sorted([(x + j * dgt) % m for j in range(5)] + [(m - 5 * x) % m])
        U = units(m)
        assert canon(tuple(ent), m, U) == tuple(a)
    elif kind == "star-split":
        T1, T2 = tuple(rec["T1"]), tuple(rec["T2"])
        assert sorted(T1 + T2) == sorted(a)
        assert sum(T1) % m == 0 and sum(T2) % m == 0
    elif kind == "survivor":
        assert rec["closure"]
        # Negative screening: the survivor label claims NO earlier mechanism applies -- re-derive
        # all four negatives from the definitions (not from the stored JSON).
        U, S2, std = _neg_ctx(m)
        assert find_pair(a, m) is None, f"survivor at m={m} has a vanishing pair"
        assert find_quasi(a, m, S2) is None, f"survivor at m={m} is quasi-decomposable"
        assert a not in std, f"survivor at m={m} is standard"
        assert find_split(a, m) is None, f"survivor at m={m} is star-split"
    else:
        raise AssertionError(f"unknown kind {kind}")
    return True


def scan_level(m):
    U = units(m)
    S3 = hodge_multisets(m, 6, 3)
    S2 = hodge_multisets(m, 4, 2)
    reps = sorted({canon(a, m, U) for a in S3})
    std = standard_grade3(m, U)
    out, tallies = [], defaultdict(int)
    for a in reps:
        assert grade_ok(a, m, 3)
        rec = {"class": list(a)}
        p = find_pair(a, m)
        if p:
            rec.update(kind="decomposable", pair=list(p))
        else:
            q = find_quasi(a, m, S2)
            if q:
                rec.update(kind="quasi", k=q[0], c=list(q[1]), d=list(q[2]))
            elif a in std:
                x = find_standard(a, m, U)
                assert x is not None
                rec.update(kind="standard", x=x)
            else:
                sp = find_split(a, m)
                if sp:
                    rec.update(kind="star-split", T1=list(sp[0]), T2=list(sp[1]))
                else:
                    rec.update(kind="survivor",
                               closure=SURVIVOR_LABELS.get((m,), "UNEXPECTED survivor"))
                    assert (m,) in SURVIVOR_LABELS, f"unexpected survivor at m={m}: {a}"
        verify_witness(m, tuple(a), rec)
        tallies[rec["kind"]] += 1
        out.append(rec)
    return {"m": m, "n_reps": len(reps), "tallies": dict(tallies), "orbits": out}


def main():
    if "--verify" in sys.argv:
        data = json.load(open(OUT))
        n = 0
        for lev in data["levels"]:
            for rec in lev["orbits"]:
                verify_witness(lev["m"], tuple(rec["class"]), rec)
                n += 1
        nsurv = sum(1 for lev in data["levels"] for rec in lev["orbits"]
                    if rec["kind"] == "survivor")
        print(f"census_witnesses: re-verified {n} stored witnesses across "
              f"{len(data['levels'])} levels — ALL PASS "
              f"(incl. live negative re-screening of the {nsurv} survivor orbits)")
        return
    ms = [int(x) for x in sys.argv[1:]] or [m for m in range(21, 200, 2) if m != 23]
    levels = []
    for m in ms:
        lev = scan_level(m)
        levels.append(lev)
        print(f"m={m}: reps={lev['n_reps']} tallies={lev['tallies']}")
    json.dump({"list": ms, "levels": levels}, open(OUT, "w"))
    total = sum(l["n_reps"] for l in levels)
    surv = sum(l["tallies"].get("survivor", 0) for l in levels)
    print(f"WROTE {OUT}: {len(levels)} levels, {total} orbit witnesses, {surv} survivors "
          f"(expected 7 on the full list). ALL WITNESSES VERIFIED AT EMISSION.")
    if len(ms) == 89:
        assert surv == 7


if __name__ == "__main__":
    main()
