#!/usr/bin/env python3
"""Exact verification of every closure identity stated in the manuscript
"New cases and the open boundary of the Hodge conjecture for Fermat fourfolds".

Self-contained (stdlib only; exact integer arithmetic throughout). Every check is an
assert — a clean exit IS the verification.

Conventions (manuscript §1): <x> is the residue of x mod m in {1,...,m-1}; a multiset
a = (a_0,...,a_{n+1}) with nonzero entries and sum ≡ 0 (mod m) is a Hodge character of
grade g iff sum_i <t a_i> = g·m for every t in (Z/m)^*.
"""
from math import gcd
from collections import Counter

def res(x, m):
    r = x % m
    assert r != 0, f"zero entry mod {m}"
    return r

def grade_profile(a, m):
    """Return the set of values sum_i <t a_i> / m over all units t (must be integers)."""
    out = set()
    for t in range(1, m):
        if gcd(t, m) != 1:
            continue
        s = sum(res(t * x, m) for x in a)
        assert s % m == 0, f"non-integral grade at t={t} for {a} mod {m}"
        out.add(s // m)
    return out

def is_hodge(a, m, g):
    """Hodge of pure grade g: sum_i <t a_i> = g m for ALL units t."""
    return grade_profile(a, m) == {g}

def muls(*parts):
    c = Counter()
    for p in parts:
        c.update(p)
    return c

def is_standard5(S, m):
    """S is an Aoki 5-standard sextuple: {x, x+m/5,...,x+4m/5, -5x} for some x, 5x != 0."""
    assert m % 5 == 0
    d = m // 5
    for x in range(1, m):
        if (5 * x) % m == 0:
            continue
        cand = Counter([ (x + k * d) % m for k in range(5) ] + [(-5 * x) % m])
        if 0 in cand:
            continue
        if cand == Counter(S):
            return x
    return None

fails = 0
def check(label, cond):
    global fails
    status = "PASS" if cond else "FAIL"
    if not cond:
        fails += 1
    print(f"[{status}] {label}")

# ---------------------------------------------------------------- Theorem A (m=39)
for a, b, c in [((1,7,16,22,34,37), (1,16,22), (7,34,37)),
                ((1,14,16,22,29,35), (1,16,22), (14,29,35))]:
    m = 39
    check(f"A m=39 {a}: Hodge grade 3", is_hodge(a, m, 3))
    check(f"A m=39 {a}: multiset split", muls(b, c) == muls(a))
    check(f"A m=39 {a}: zero-sum triples", sum(b) % m == 0 and sum(c) % m == 0)
    # * -split type condition: |t b| + |t c| = 3 with each in {1,2} for every unit t
    ok = True
    for t in range(1, m):
        if gcd(t, m) != 1:
            continue
        gb = sum(res(t * x, m) for x in b) // m
        gc = sum(res(t * x, m) for x in c) // m
        ok &= (gb + gc == 3 and gb in (1, 2) and gc in (1, 2))
    check(f"A m=39 {a}: conjugate types (1,2)/(2,1)", ok)

# ---------------------------------------------------------------- Theorem A' (table)
APRIME = [
    (45,  (1,19,20,28,30,37),   ((5,40),(10,35)),  (1,10,19,28,37,40), (5,20,30,35)),
    (105, (3,24,50,66,85,87),   ((15,90),(45,60)), (3,24,45,66,87,90), (15,50,60,85)),
    (105, (1,22,43,64,90,95),   ((5,100),(20,85)), (1,22,43,64,85,100),(5,20,90,95)),
]
for m, a, (p1, p2), S, Q in APRIME:
    check(f"A' m={m} {a}: Hodge grade 3", is_hodge(a, m, 3))
    check(f"A' m={m} {a}: vanishing pairs", (p1[0]+p1[1]) % m == 0 and (p2[0]+p2[1]) % m == 0)
    check(f"A' m={m} {a}: 10-multiset identity", muls(a, p1, p2) == muls(S, Q))
    x = is_standard5(S, m)
    check(f"A' m={m} {a}: S is 5-standard (x={x})", x is not None)
    check(f"A' m={m} {a}: Q grade-2 Hodge", is_hodge(Q, m, 2))

# ---------------------------------------------------------------- Theorem A'' (m=33 witness)
m33, m66 = 33, 66
w = (1,4,16,22,25,31)
check("A'' w Hodge grade 3 at m=33", is_hodge(w, m33, 3))
check("A'' w is the da Silva witness (same Galois orbit as (7,10,13,19,22,28))",
      any(Counter(res(t * x, m33) for x in (7,10,13,19,22,28)) == Counter(w)
          for t in range(1, m33) if gcd(t, m33) == 1))
a66 = tuple(sorted((2 * x) % m66 for x in w))
check(f"A'' a=2w mod 66 = {a66}: entries nonzero", all(x % m66 for x in a66))
check("A'' a Hodge grade 3 at m=66", is_hodge(a66, m66, 3))
Q66, S66 = (1,25,44,62), (2,8,32,41,50,65)
check("A'' augmented identity a+(1,65)+(25,41) = Q+S",
      muls(a66, (1,65), (25,41)) == muls(Q66, S66))
check("A'' Q grade-2 Hodge at 66", is_hodge(Q66, m66, 2))
q1, q2 = (2,32,33,65), (8,33,41,50)
check("A'' S+(33,33) = (2,32,33,65)+(8,33,41,50)", muls(S66, (33,33)) == muls(q1, q2))
check("A'' (33,33) legitimate: <33t>+<33t>=66 for all units t",
      all(2 * res(33 * t, m66) == 66 for t in range(1, m66) if gcd(t, m66) == 1))
check("A'' both quadruples grade-2 Hodge at 66", is_hodge(q1, m66, 2) and is_hodge(q2, m66, 2))
check("A'' matched entries of beta=(2,32,65;33), gamma=(8,41,50;33) sum to 0 mod 66",
      (33 + 33) % m66 == 0 and sorted(q1) == sorted((2,32,65,33)) and sorted(q2) == sorted((8,41,50,33)))

# ------------------------------------------------- Exchange lemma instance (m=110 pair)
m110 = 110
T1 = (1,24,62,71,81,91)   # zeta_110 class (census rep)
T2 = (1,31,55,71,81,91)   # zeta_5 class (census rep)
check("EX both m=110 classes Hodge grade 3", is_hodge(T1, m110, 3) and is_hodge(T2, m110, 3))
Scom = Counter(T1) & Counter(T2)
A = list((Counter(T1) - Scom).elements()); B = list((Counter(T2) - Scom).elements())
q = tuple(A + [(-x) % m110 for x in B])
check(f"EX |A|=|B|=2 (A={A}, B={B})", len(A) == 2 and len(B) == 2)
check(f"EX q=A+(-B)={q}: nonzero entries, grade-(1,1) Hodge quadruple",
      all(x % m110 for x in q) and is_hodge(q, m110, 2))

# ---------------------------- Prop D even-m caveat (Remark: inadmissible => decomposable)
bad = 0; ncase = 0
for m in range(10, 251, 5):
    d = m // 5
    for x in range(1, m):
        if (5 * x) % m == 0:
            continue
        if d // gcd(x, d) > 2:      # admissible — not the excluded case
            continue
        e = [(x + k * d) % m for k in range(5)] + [(-5 * x) % m]
        if any(v == 0 for v in e):
            continue
        ncase += 1
        s = set(e)
        if not any((m - v) in s for v in s):
            bad += 1
check(f"PropD even-m caveat: all {ncase} inadmissible standard multisets (m<=250) are decomposable",
      bad == 0 and ncase > 0)

print()
if fails:
    raise SystemExit(f"{fails} CHECK(S) FAILED")
print("ALL CLOSURE IDENTITIES VERIFIED EXACTLY (Theorems A, A', A''; exchange instance @110; "
      "Prop D even-m caveat).")


# --- even-m multiplicity regressions (external referee round, 2026-07-28) ---
# Standalone, engine-independent: multiplicity-aware decomposability + exhaustive self-pair quasi.
def _dec_exact(a, m):
    from collections import Counter
    cnt = Counter(a)
    for x in cnt:
        y = (m - x) % m
        if (y == x and cnt[x] >= 2) or (y != x and y in cnt):
            return True
    return False

def _quasi_exact(a, m):
    from math import gcd
    from itertools import combinations
    U = [t for t in range(1, m) if gcd(t, m) == 1]
    def hq(q):
        return all(x % m for x in q) and all(sum((t * x) % m for x in q) == 2 * m for t in U)
    for k in range(1, m // 2 + 1):
        aug = list(a) + [k, m - k]
        for half in combinations(range(8), 4):
            if 0 not in half:
                continue
            h1 = [aug[i] for i in half]
            h2 = [aug[i] for i in range(8) if i not in half]
            if sum(h1) % m or sum(h2) % m:
                continue
            if hq(h1) and hq(h2):
                return True
    return False

_m = 70
_r1 = (1, 29, 35, 43, 45, 57)   # single m/2: NOT decomposable (set-based tests fail here), NOT quasi
assert not _dec_exact(_r1, _m), "regression: single m/2 misread as a vanishing pair"
assert not _quasi_exact(_r1, _m), "regression: (1,29,35,43,45,57)@70 must not be quasi"
_r2 = (1, 3, 36, 38, 64, 68)    # genuinely quasi through the SELF-PAIR k=35
assert _quasi_exact(_r2, _m), "regression: self-pair quasi at (1,3,36,38,64,68)@70 must fire"
print("[PASS] even-m multiplicity regressions: single-m/2 not a pair; self-pair quasi fires")
