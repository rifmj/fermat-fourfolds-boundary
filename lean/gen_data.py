#!/usr/bin/env python3
"""Generate BoundaryData.lean: the certificate data consumed by the Lean formalisation.

Everything emitted here is *untrusted data* on the Lean side — Lean re-verifies each item
against its own procedurally-generated S_m lattice (gensS) and its own combinatorial
checkers by `native_decide`. This script also runs the normalization-pinning experiments
for the Jacobi layer (B4: the Lean port must reproduce these before reporting news).

Emits:
  * OUT verdicts (gap classes): modular kernel witness (q, phi) + a 2u membership certificate
  * IN verdicts: explicit integer combinations over gens_S(m)
  * the m=168 coset identity  vec(a) - vec(6*xi28) in S_168
  * exchange edges for the walls W70/W110/W114 (+ the 220/210 lift links)
  * gens_S fingerprints (count + weighted hash) per level, to pin Lean's gensS ordering
"""
import sys, os, json
from math import gcd
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
ANC = os.path.normpath(os.path.join(HERE, '..', 'anc'))
sys.path.insert(0, os.path.join(ANC, 'code', 'l4'))
os.environ['SLC_QUIET'] = '1'
import importlib.util as ilu
_s = ilu.spec_from_file_location('core', os.path.join(ANC, 'code', 'l4', 's_lattice_core.py'))
core = ilu.module_from_spec(_s); _s.loader.exec_module(core)
_s2 = ilu.spec_from_file_location('slat', os.path.join(ANC, 'code', 'l4', 's_lattice.py'))
slat = ilu.module_from_spec(_s2); _s2.loader.exec_module(slat)

vec, gens_S, certificate = core.vec, core.gens_S, slat.certificate

# ---------------------------------------------------------------- helpers
def units(m):
    return [t for t in range(1, m) if gcd(t, m) == 1]

def canon(a, m, U=None):
    U = U or units(m)
    return min(tuple(sorted((t * ai) % m for ai in a)) for t in U)

def is_hodge(a, m, g):
    for t in units(m):
        if sum((t * x) % m for x in a) != g * m or any((t * x) % m == 0 for x in a):
            return False
    return True

def nullspace_mod_q(rows, q):
    n = len(rows[0])
    mat = [[x % q for x in r] for r in rows]
    piv_cols, r0 = [], 0
    for c in range(n):
        pr = next((i for i in range(r0, len(mat)) if mat[i][c] % q), None)
        if pr is None:
            continue
        mat[r0], mat[pr] = mat[pr], mat[r0]
        inv = pow(mat[r0][c], q - 2, q)
        mat[r0] = [(x * inv) % q for x in mat[r0]]
        for i in range(len(mat)):
            if i != r0 and mat[i][c] % q:
                f = mat[i][c]
                mat[i] = [(mat[i][k] - f * mat[r0][k]) % q for k in range(n)]
        piv_cols.append(c)
        r0 += 1
    free = [c for c in range(n) if c not in piv_cols]
    basis = []
    for fc in free:
        phi = [0] * n
        phi[fc] = 1
        for ri, pc in enumerate(piv_cols):
            phi[pc] = (-mat[ri][fc]) % q
        basis.append(phi)
    return basis

def kernel_witness(m, a, G=None):
    G = G or gens_S(m)
    u = vec(m, a)
    for q in [2, 3, 5, 7, 11, 13]:
        for phi in nullspace_mod_q(G, q):
            if sum(x * y for x, y in zip(phi, u)) % q:
                assert all(sum(x * y for x, y in zip(phi, g)) % q == 0 for g in G)
                return q, phi
    return None

def fingerprint(G):
    M = 1000000007
    fp = 0
    for i, g in enumerate(G):
        for j, x in enumerate(g):
            if x:
                fp = (fp + x * (i + 1) * (j + 1)) % M
    return fp

# ---------------------------------------------------------------- lattice verdicts
GAP = [
    (21,  (1, 4, 16, 9, 15, 18)),      # Aoki's xi_21 (calibration, s_lattice_core self-demo)
    (28,  (1, 9, 18, 10, 21, 25)),     # repaired xi_28 (Prop w168 erratum)
    (33,  (1, 4, 16, 22, 25, 31)),
    (70,  (1, 20, 24, 42, 61, 62)),
    (105, (1, 22, 43, 64, 90, 95)),
    (110, (1, 24, 62, 71, 81, 91)),
    (110, (1, 31, 55, 71, 81, 91)),
    (114, (1, 13, 43, 72, 103, 110)),
    (114, (1, 13, 43, 80, 102, 103)),
    (114, (1, 7, 78, 79, 86, 91)),
    (168, (1, 25, 79, 121, 127, 151)),
    (210, (2, 9, 129, 142, 168, 180)),
    (220, (1, 62, 111, 142, 162, 182)),
]
IN = [
    (210, (1, 79, 109, 121, 151, 169)),
    (45,  (1, 19, 20, 28, 30, 37)),
    (105, (3, 24, 50, 66, 85, 87)),
]

out_rows, in_rows, fps = [], [], {}
for m, a in GAP:
    G = gens_S(m)
    fps[m] = (len(G), fingerprint(G))
    qw = kernel_witness(m, a, G)
    assert qw, f"no kernel witness for {m} {a}"
    q, phi = qw
    ok2, cert2 = certificate(m, a, vec_override=[2 * x for x in vec(m, a)])
    assert ok2, f"2u not in S_{m} for {a}?!"
    out_rows.append(dict(m=m, cls=list(a), q=q, phi=phi,
                         cert2u=sorted((int(i), int(c)) for i, c in cert2.items())))
    print(f"OUT m={m} {a}: witness q={q}; 2u cert {len(cert2)} gens")

for m, a in IN:
    G = gens_S(m)
    fps[m] = (len(G), fingerprint(G))
    ok, cert = certificate(m, a)
    assert ok, f"{m} {a} should be IN"
    in_rows.append(dict(m=m, cls=list(a), cert=sorted((int(i), int(c)) for i, c in cert.items())))
    print(f"IN  m={m} {a}: cert {len(cert)} gens, coeffs {sorted(set(cert.values()))}")

# m=168 coset identity: vec(a) - vec(6*xi28 entries) in S_168
m = 168
a168 = (1, 25, 79, 121, 127, 151)
xi28_inflated = tuple(6 * x for x in (1, 9, 18, 10, 21, 25))
diff = [x - y for x, y in zip(vec(m, a168), vec(m, xi28_inflated))]
ok, cert = certificate(m, a168, vec_override=diff)
assert ok, "168 coset identity failed"
coset168 = dict(m=m, cls=list(a168), xi=list(xi28_inflated),
                cert=sorted((int(i), int(c)) for i, c in cert.items()))
print(f"COSET 168: vec(a)-vec(6*xi28) in S_168, cert {len(cert)} gens")

# also: 2*xi in S for the two calibration levels (gap-group 2-torsion receipts)
for m, a in [(21, (1, 4, 16, 9, 15, 18)), (28, (1, 9, 18, 10, 21, 25))]:
    ok, cert = certificate(m, a, vec_override=[2 * x for x in vec(m, a)])
    assert ok

# ---------------------------------------------------------------- exchange edges
def scan_edges(m, T, target_canons):
    """All exchange edges from T landing (at canon level) in target_canons; keep witnesses."""
    U = units(m)
    H = [t for t in U if t <= m // 2]
    def g_ok(c, g):
        return all(x % m for x in c) and all(sum((t * x) % m for x in c) == g * m for t in H)
    edges = []
    for Aidx in combinations(range(6), 2):
        A = [T[i] for i in Aidx]
        S = [T[i] for i in range(6) if i not in Aidx]
        sA = sum(A) % m
        for y1 in range(1, m):
            y2 = (sA - y1) % m
            if y2 == 0 or y1 > y2:
                continue
            q = tuple(sorted(A + [(m - y1) % m, (m - y2) % m]))
            if not g_ok(q, 2):
                continue
            Tp = tuple(sorted(S + [y1, y2]))
            if g_ok(Tp, 3):
                can = canon(Tp, m, U)
                if can in target_canons:
                    edges.append((2, A, [y1, y2], Tp, q, can))
    return edges

def pick_edge(m, T, target):
    U = units(m)
    tc = canon(target, m, U)
    edges = scan_edges(m, T, {tc})
    assert edges, f"no |A|=2 edge {m} {T} -> {target}"
    lA, A, B, Tp, q, can = edges[0]
    # find unit t with sorted(t*target) == Tp
    t = next(t for t in U if tuple(sorted((t * x) % m for x in target)) == Tp)
    print(f"EDGE m={m} {T} <- {target}: A={A} B={B} q={q} t={t}")
    return dict(m=m, T=list(T), A=list(A), B=list(B), Tp=list(Tp), q=list(q), t=t,
                target=list(target))

edges = []
T110a, T110b = (1, 24, 62, 71, 81, 91), (1, 31, 55, 71, 81, 91)
T114 = [(1, 13, 43, 72, 103, 110), (1, 13, 43, 80, 102, 103), (1, 7, 78, 79, 86, 91)]
edges.append(pick_edge(110, T110a, T110b))
edges.append(pick_edge(110, T110b, T110a))
edges.append(pick_edge(114, T114[0], T114[1]))
edges.append(pick_edge(114, T114[1], T114[0]))
edges.append(pick_edge(114, T114[0], T114[2]))
edges.append(pick_edge(114, T114[2], T114[0]))
# W70 <-> 210#2 (at level 210, via the 3-lift of the 70 class)
c70 = (1, 20, 24, 42, 61, 62)
lift70 = tuple(3 * x for x in c70)
T210 = (2, 9, 129, 142, 168, 180)
edges.append(pick_edge(210, T210, lift70))
edges.append(pick_edge(210, lift70, T210))
# 220 <-> 2-lifts of the 110 pair
T220 = (1, 62, 111, 142, 162, 182)
lift110b = tuple(2 * x for x in T110b)
edges.append(pick_edge(220, T220, lift110b))
edges.append(pick_edge(220, lift110b, T220))

for m in [110, 114, 210, 220]:
    if m not in fps:
        G = gens_S(m)
        fps[m] = (len(G), fingerprint(G))

# ---------------------------------------------------------------- Jacobi experiments
def prim_root(p):
    for g in range(2, p):
        x, seen = 1, set()
        for _ in range(p - 1):
            x = x * g % p
            seen.add(x)
        if len(seen) == p - 1:
            return g

def jacobi_S(alpha, p, m):
    """S(alpha) = sum over v_i in F_p^*, sum v = 0 of prod chi^{a_i}(v_i); chi(g^k)=zeta_m^k.
    Returns length-m integer vector (exponent coefficients in Z[x]/(x^m-1))."""
    g = prim_root(p)
    ind = {}
    x = 1
    for k in range(p - 1):
        ind[x] = k
        x = x * g % p
    dp = [[0] * m for _ in range(p)]
    dp[0][0] = 1
    for ai in alpha:
        ndp = [[0] * m for _ in range(p)]
        for v in range(1, p):
            e = (ai * ind[v]) % m
            for s in range(p):
                row = dp[s]
                if any(row):
                    nrow = ndp[(s + v) % p]
                    for ee in range(m):
                        c = row[ee]
                        if c:
                            nrow[(ee + e) % m] += c
        dp = ndp
    return dp[0]

def cyclotomic(n, cache={}):
    if n in cache:
        return cache[n]
    # Phi_n = (x^n - 1) / prod_{d|n, d<n} Phi_d, exact division
    def polmul(a, b):
        r = [0] * (len(a) + len(b) - 1)
        for i, ai in enumerate(a):
            if ai:
                for j, bj in enumerate(b):
                    r[i + j] += ai * bj
        return r
    def poldiv(num, den):
        num = num[:]
        q = [0] * (len(num) - len(den) + 1)
        for i in range(len(q) - 1, -1, -1):
            c = num[i + len(den) - 1]
            assert c % den[-1] == 0
            q[i] = c // den[-1]
            for j, dj in enumerate(den):
                num[i + j] -= q[i] * dj
        assert all(c == 0 for c in num)
        return q
    num = [-1] + [0] * (n - 1) + [1]
    for d in range(1, n):
        if n % d == 0:
            num = poldiv(num, cyclotomic(d))
    cache[n] = num
    return num

def reduce_mod_phi(v, m):
    phi = cyclotomic(m)
    deg = len(phi) - 1
    v = v[:]
    for i in range(len(v) - 1, deg - 1, -1):
        c = v[i]
        if c:
            for j in range(len(phi)):
                v[i - deg + j] -= c * phi[j]
    return v[:deg]

def mulmod(a, b, m):
    r = [0] * m
    for i, ai in enumerate(a):
        if ai:
            for j, bj in enumerate(b):
                if bj:
                    r[(i + j) % m] += ai * bj
    return r

print("\n--- Jacobi normalization experiments ---")
# exp3: m=33 sanity (must reproduce the anc certificate: u' = 1 + x^11)
p, m = 67, 33
S = jacobi_S((7, 10, 13, 19, 22, 28), p, m)
assert all(c % (p - 1) == 0 for c in S)
J = [c // (p - 1) for c in S]
assert all(c % (p * p) == 0 for c in reduce_mod_phi(J, m)), "u' not integral at 33?!"
U33 = [c // (p * p) for c in reduce_mod_phi(J, m)]
target = reduce_mod_phi([1] + [0] * 10 + [1] + [0] * 21, m)
print(f"exp3 m=33 p=67: u'(t=1) == 1+x^11: {U33 == target}")

# exp1: m=39 divisorial calibration at p=79: expect j = p^2 exactly
p, m = 79, 39
S = jacobi_S((1, 14, 16, 22, 29, 35), p, m)
assert all(c % (p - 1) == 0 for c in S)
J = reduce_mod_phi([c // (p - 1) for c in S], m)
expect = [p * p] + [0] * (len(J) - 1)
print(f"exp1 m=39 p=79 divisorial: j == p^2: {J == expect}")

# exp4: m=66 consistency: u(2w@66, 67) — expect 1 + x^22 (= 1+zeta_3 = zeta_6)
p, m = 67, 66
w = (1, 4, 16, 22, 25, 31)
a66 = tuple((2 * x) % 66 for x in w)
S = jacobi_S(a66, p, m)
assert all(c % (p - 1) == 0 for c in S)
J = reduce_mod_phi([c // (p - 1) for c in S], m)
assert all(c % (p * p) == 0 for c in J)
U66 = [c // (p * p) for c in J]
t66 = reduce_mod_phi([1] + [0] * 21 + [1] + [0] * (66 - 23), m)
print(f"exp4 m=66 p=67: u'(2w) == 1+x^22: {U66 == t66}")

# exp2: m=45 A' row: multiplicativity u(a) = u(S)u(Q) at p=181: j6(a)*p ?= j6(S)*j4(Q)
p, m = 181, 45
a45, S45, Q45 = (1, 19, 20, 28, 30, 37), (1, 10, 19, 28, 37, 40), (5, 20, 30, 35)
jA = reduce_mod_phi([c // (p - 1) for c in jacobi_S(a45, p, m)], m)
jS = reduce_mod_phi([c // (p - 1) for c in jacobi_S(S45, p, m)], m)
jQ = reduce_mod_phi([c // (p - 1) for c in jacobi_S(Q45, p, m)], m)
lhs = reduce_mod_phi(mulmod([x * p for x in jA] + [0] * (m - len(jA)), [1] + [0] * (m - 1), m), m)
rhs = reduce_mod_phi(mulmod(jS + [0] * (m - len(jS)), jQ + [0] * (m - len(jQ)), m), m)
print(f"exp2 m=45 p=181: p*j(a) == j(S)*j(Q): {lhs == rhs}")

# ---------------------------------------------------------------- emit Lean
def lean_nat_list(l):
    return "[" + ", ".join(str(x) for x in l) + "]"

def lean_cert(c):
    return "[" + ", ".join(f"({i}, {v})" for i, v in c) + "]"

L = []
L.append("/- BoundaryData.lean — GENERATED by gen_data.py; certificate data (UNTRUSTED on the")
L.append("   Lean side: every item is re-verified by native_decide in BoundaryCore/BoundaryClaim). -/")
L.append("namespace BoundaryData")
L.append("")
L.append("structure OutVerdict where")
L.append("  m : Nat"); L.append("  cls : List Nat"); L.append("  q : Nat")
L.append("  phi : List Nat"); L.append("  cert2u : List (Nat × Int)")
L.append("")
L.append("structure InVerdict where")
L.append("  m : Nat"); L.append("  cls : List Nat"); L.append("  cert : List (Nat × Int)")
L.append("")
L.append("structure ExEdge where")
L.append("  m : Nat"); L.append("  T : List Nat"); L.append("  A : List Nat"); L.append("  B : List Nat")
L.append("  Tp : List Nat"); L.append("  q : List Nat"); L.append("  t : Nat"); L.append("  target : List Nat")
L.append("")
L.append("def outVerdicts : List OutVerdict := [")
for r in out_rows:
    L.append(f"  ⟨{r['m']}, {lean_nat_list(r['cls'])}, {r['q']}, {lean_nat_list(r['phi'])}, {lean_cert(r['cert2u'])}⟩,")
L[-1] = L[-1].rstrip(',')
L.append("]")
L.append("")
L.append("def inVerdicts : List InVerdict := [")
for r in in_rows:
    L.append(f"  ⟨{r['m']}, {lean_nat_list(r['cls'])}, {lean_cert(r['cert'])}⟩,")
L[-1] = L[-1].rstrip(',')
L.append("]")
L.append("")
L.append("/-- m=168 coset identity: vec(cls) − vec(6·ξ₂₈) ∈ S₁₆₈ (Prop w168's `a ≡ 6ξ₂₈ mod S`). -/")
L.append(f"def coset168cls : List Nat := {lean_nat_list(coset168['cls'])}")
L.append(f"def coset168xi : List Nat := {lean_nat_list(coset168['xi'])}")
L.append(f"def coset168cert : List (Nat × Int) := {lean_cert(coset168['cert'])}")
L.append("")
L.append("def exchangeEdges : List ExEdge := [")
for e in edges:
    L.append(f"  ⟨{e['m']}, {lean_nat_list(e['T'])}, {lean_nat_list(e['A'])}, {lean_nat_list(e['B'])}, "
             f"{lean_nat_list(e['Tp'])}, {lean_nat_list(e['q'])}, {e['t']}, {lean_nat_list(e['target'])}⟩,")
L[-1] = L[-1].rstrip(',')
L.append("]")
L.append("")
L.append("/-- (m, #generators, Σ g_i[j]·(i+1)·(j+1) mod 10^9+7) for the levels used — pins the")
L.append("    generator ORDER of Lean's gensS against the certificate indices above. -/")
L.append("def gensFingerprints : List (Nat × Nat × Nat) := [")
for m in sorted(fps):
    n, fp = fps[m]
    L.append(f"  ({m}, {n}, {fp}),")
L[-1] = L[-1].rstrip(',')
L.append("]")
L.append("")
L.append("end BoundaryData")

with open(os.path.join(HERE, 'BoundaryData.lean'), 'w') as f:
    f.write("\n".join(L) + "\n")
json.dump(dict(out=out_rows, inn=in_rows, coset168=coset168, edges=edges,
               fps={str(k): v for k, v in fps.items()}),
          open(os.path.join(HERE, 'lean_data.json'), 'w'))
print(f"\nwrote BoundaryData.lean ({len(L)} lines)")
